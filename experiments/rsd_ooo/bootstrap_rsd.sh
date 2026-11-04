#!/usr/bin/env bash
# Obtain the exact RSD source and record the host/cross-tool identities.
# Does not alter an existing checkout or install system packages.
set -euo pipefail
experiment_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
core_dir="$experiment_dir/rsd"
core_revision=7b65f6ba0bce58d4d859082660123b7100aae975
compiler_prefix="${RSD_EXPERIMENT_CROSS_PREFIX:-/home/allenjin/riscv/bin/riscv32-unknown-elf-}"
export PATH=/usr/bin:/bin:/usr/local/bin
mkdir -p "$experiment_dir/results"
if [[ ! -d "$core_dir/.git" ]]; then
    git clone https://github.com/rsd-devel/rsd "$core_dir"
    git -C "$core_dir" checkout --detach "$core_revision"
fi
test "$(git -C "$core_dir" rev-parse HEAD)" = "$core_revision"
test -z "$(git -C "$core_dir" status --porcelain --untracked-files=no)"
"${compiler_prefix}gcc" --version
python3 - "$experiment_dir" "$compiler_prefix" <<'PY'
import hashlib, json, platform, shutil, subprocess, sys, time
from pathlib import Path
root, prefix = Path(sys.argv[1]), sys.argv[2]
def identify(executable):
    path = Path(shutil.which(executable) or executable).resolve()
    p = subprocess.run([str(path), '--version'], capture_output=True, text=True)
    return {'path':str(path), 'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'version':(p.stdout+p.stderr).splitlines()[0]}
result = {'platform':platform.platform(), 'python':sys.version,
          'core_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root/'rsd',text=True).strip(),
          'tools':{t:identify(t) for t in ('gcc','g++','make',prefix+'gcc',prefix+'as',prefix+'ld',prefix+'objcopy')}}
libgcc = Path(subprocess.check_output([prefix+'gcc','-march=rv32im_zicsr','-mabi=ilp32','-print-libgcc-file-name'],text=True).strip())
result['libgcc'] = {'path':str(libgcc),'sha256':hashlib.sha256(libgcc.read_bytes()).hexdigest()}
path = root/'results/setup_manifest.json'
if path.exists():
    if json.loads(path.read_text()) == result:
        print(f'Existing provenance verified: {path}')
        raise SystemExit(0)
    path = root/f'results/setup_manifest_{time.time_ns()}.json'
path.write_text(json.dumps(result,indent=2)+'\n')
print(path)
PY
# Then run bootstrap_verilator.sh to build local pinned Verilator 4.228.
