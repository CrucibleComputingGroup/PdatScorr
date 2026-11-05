from pathlib import Path
import sys
import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'experiments/bounded_dynamic/len5/application_screen'))
from program_rom import read_image, response, verilog_selector


def test_little_endian_zero_words_and_faults(tmp_path):
    p = tmp_path/'image.hex'
    p.write_text('@00000000\n13 00 00 00 37 14 00 00 00 00 00 00\n')
    image = read_image(p)
    assert response(image, 0) == (0x13, False, 31)
    assert response(image, 4) == (0x1437, False, 31)
    assert response(image, 8) == (0, False, 31)
    assert response(image, 12, 0x1234) == (0x1234, True, 1)
    assert response(image, 2, 0x5678) == (0x5678, True, 0)
    assert response(image, 1<<63, 7) == (7, True, 1)
    assert image['bytes'] == 12 and image['nonzero_words'] == 2


@pytest.mark.parametrize('text', ['00 00 00 00', '@0 00 00 00',
    '@4 00 00 00 00', '@0 00 00 00 00 @0 00', '@0 00 00 00 00 @8 00 00 00 00',
    '@0 xx 00 00 00', '@0 1234 00 00 00'])
def test_malformed_or_partial_images_rejected(tmp_path, text):
    p = tmp_path/'bad.hex'; p.write_text(text)
    with pytest.raises(ValueError): read_image(p)


def test_real_program_image_matches_disassembly_and_padding():
    folder = ROOT/'experiments/bounded_dynamic/len5/results/streaming_v2'
    image = read_image(folder/'program.hex')
    assert image['bytes'] == 0x1280
    import re
    for address, word in re.findall(r'(?m)^\s*([0-9a-f]+):\s+([0-9a-f]{8})\s', (folder/'program.disasm').read_text()):
        assert response(image, int(address,16)) == (int(word,16), False, 31)
    for address in range(0x1200, 0x1280, 4):
        assert response(image, address) == (0, False, 31)
    source = '\n'.join(verilog_selector(image))
    assert 'assume' not in source and '64\'d4736' in source


@pytest.mark.parametrize('zero_fault_data', [False, True])
def test_generated_selector_matches_independent_byte_memory(tmp_path, zero_fault_data):
    """Exercise emitted RTL against Icarus $readmemh, including fault branches."""
    import shutil
    import subprocess
    if not shutil.which('iverilog') or not shutil.which('vvp'):
        pytest.skip('Icarus Verilog needed for ROM RTL regression')
    path = ROOT/'experiments/bounded_dynamic/len5/results/streaming_v2/program.hex'
    image = read_image(path)
    size = image['bytes']
    source = tmp_path/'rom_test.sv'
    source.write_text(f'''module RomTest;
      reg [63:0] instr_addr_o;
      reg [31:0] instruction_fault_data, selected_instruction;
      reg selected_instruction_fault;
      reg [4:0] selected_instruction_code;
      reg [7:0] byte_memory [0:{size-1}];
      integer i;
      {chr(10).join(verilog_selector(image, zero_fault_data=zero_fault_data))}
      task check_address(input [63:0] address);
        reg [31:0] expected;
        begin
          instr_addr_o = address;
          instruction_fault_data = 32'hf001ba11 ^ address[31:0];
          #1;
          if (address[1:0] != 0) begin
            if (!selected_instruction_fault || selected_instruction_code != 0 ||
                selected_instruction !== {"32'b0" if zero_fault_data else "instruction_fault_data"}) $fatal(1,"misaligned");
          end else if (address >= {size}) begin
            if (!selected_instruction_fault || selected_instruction_code != 1 ||
                selected_instruction !== {"32'b0" if zero_fault_data else "instruction_fault_data"}) $fatal(1,"unmapped");
          end else begin
            expected = {{byte_memory[address+3],byte_memory[address+2],
                         byte_memory[address+1],byte_memory[address]}};
            if (selected_instruction_fault || selected_instruction_code != 31 ||
                selected_instruction !== expected) $fatal(1,"word at %h",address);
          end
        end
      endtask
      initial begin
        $readmemh("{path}",byte_memory);
        for (i=0;i<{size+8};i=i+1) check_address(i);
        check_address(64'h8000000000000000);
        check_address(64'hfffffffffffffffe);
        $display("ROM_RTL_PASS");
        $finish;
      end
    endmodule
    ''')
    subprocess.run(['iverilog','-g2012','-s','RomTest','-o',str(tmp_path/'sim'),str(source)],
                   check=True, capture_output=True, text=True, timeout=20)
    run = subprocess.run(['vvp',str(tmp_path/'sim')], check=True, capture_output=True,
                         text=True, timeout=20)
    assert 'ROM_RTL_PASS' in run.stdout
