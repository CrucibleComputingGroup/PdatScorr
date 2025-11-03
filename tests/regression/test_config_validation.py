#!/usr/bin/env python3
"""
Regression tests for configuration file validation.

Tests ensure that config loading properly validates YAML files and provides
helpful error messages for common mistakes.
"""

import os
import pytest
import sys
from pathlib import Path

# Path to project root
PROJECT_ROOT = Path(__file__).parent.parent.parent
FIXTURES_DIR = Path(__file__).parent / "fixtures"

# Add scripts directory to path for imports
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

from config_loader import ConfigLoader, CoreConfig


class TestConfigLoading:
    """Test basic config file loading."""

    def test_load_valid_config(self):
        """Test loading a valid config file."""
        config_file = FIXTURES_DIR / "ibex_test.yaml"

        config = ConfigLoader.load_config(str(config_file))

        assert config.core_name == "ibex"
        assert config.architecture == "rv32"
        assert config.synthesis.top_module == "ibex_core"
        assert len(config.synthesis.source_files) > 0
        assert len(config.synthesis.include_dirs) > 0

    def test_load_main_config(self):
        """Test loading the main ibex config."""
        config_file = PROJECT_ROOT / "configs" / "ibex.yaml"

        config = ConfigLoader.load_config(str(config_file))

        assert config.core_name == "ibex"
        assert len(config.injections) == 3
        assert config.get_injection("isa") is not None
        assert config.get_injection("timing") is not None
        assert config.get_injection("odc_error") is not None

    def test_config_not_found(self):
        """Test error handling for missing config file."""
        with pytest.raises(FileNotFoundError) as exc_info:
            ConfigLoader.load_config("nonexistent.yaml")

        assert "not found" in str(exc_info.value).lower()

    def test_invalid_yaml_syntax(self, tmp_path):
        """Test error handling for invalid YAML syntax."""
        bad_yaml = tmp_path / "bad.yaml"
        bad_yaml.write_text("core_name: ibex\narchitecture: [unclosed list")

        with pytest.raises(Exception):  # YAML parsing error
            ConfigLoader.load_config(str(bad_yaml))


class TestConfigValidation:
    """Test config validation logic."""

    def test_missing_required_fields(self):
        """Test error handling for missing required fields."""
        config_file = FIXTURES_DIR / "ibex_invalid.yaml"

        with pytest.raises(ValueError) as exc_info:
            ConfigLoader.load_config(str(config_file))

        error_msg = str(exc_info.value).lower()
        assert "missing required" in error_msg or "architecture" in error_msg

    def test_missing_synthesis_fields(self, tmp_path):
        """Test validation of synthesis section."""
        config = tmp_path / "test.yaml"
        config.write_text("""
core_name: "test"
architecture: "rv32"
signals:
  instruction_data: "instr"
  pc: "pc"
synthesis:
  # Missing core_root, source_files, include_dirs
  top_module: "core"
""")

        with pytest.raises(ValueError) as exc_info:
            ConfigLoader.load_config(str(config))

        assert "synthesis" in str(exc_info.value).lower()


class TestInjectionPoints:
    """Test injection point configuration."""

    def test_get_injection_by_type(self):
        """Test retrieving injection points by constraint type."""
        config_file = FIXTURES_DIR / "ibex_test.yaml"
        config = ConfigLoader.load_config(str(config_file))

        isa_inj = config.get_injection("isa")
        assert isa_inj is not None
        assert isa_inj.name == "id_stage_isa"
        assert "id_stage" in isa_inj.source_file.lower()

        timing_inj = config.get_injection("timing")
        assert timing_inj is not None
        assert timing_inj.name == "core_timing"
        assert "core" in timing_inj.source_file.lower()

    def test_get_injection_by_name(self):
        """Test retrieving injection points by name."""
        config_file = FIXTURES_DIR / "ibex_test.yaml"
        config = ConfigLoader.load_config(str(config_file))

        inj = config.get_injection_by_name("id_stage_isa")
        assert inj is not None
        assert inj.constraint_type == "isa"

        inj = config.get_injection_by_name("core_timing")
        assert inj is not None
        assert inj.constraint_type == "timing"

        # Non-existent injection
        assert config.get_injection_by_name("nonexistent") is None

    def test_injection_validation(self, tmp_path):
        """Test validation of injection point fields."""
        config = tmp_path / "test.yaml"
        config.write_text("""
core_name: "test"
architecture: "rv32"
signals:
  instruction_data: "instr"
  pc: "pc"
synthesis:
  core_root: "$IBEX_ROOT"
  source_files: ["file.sv"]
  include_dirs: ["rtl"]
injections:
  - name: "test_inj"
    # Missing source_file and constraint_type
    description: "Test injection"
""")

        with pytest.raises(ValueError) as exc_info:
            ConfigLoader.load_config(str(config))

        error_msg = str(exc_info.value).lower()
        assert "injection" in error_msg


class TestPathResolution:
    """Test path resolution and environment variable expansion."""

    def test_env_var_expansion(self):
        """Test environment variable expansion in paths."""
        # Set a test environment variable
        os.environ["TEST_CORE_ROOT"] = "/test/path"

        expanded = ConfigLoader.expand_env_vars("$TEST_CORE_ROOT/rtl")
        assert expanded == "/test/path/rtl"

        expanded = ConfigLoader.expand_env_vars("${TEST_CORE_ROOT}/rtl")
        assert expanded == "/test/path/rtl"

        # Cleanup
        del os.environ["TEST_CORE_ROOT"]

    def test_core_root_resolution_with_env(self):
        """Test core_root resolution when env var is set."""
        # Temporarily set IBEX_ROOT
        orig_ibex_root = os.environ.get("IBEX_ROOT")
        test_path = "/tmp/test_ibex_core"

        try:
            os.environ["IBEX_ROOT"] = test_path
            os.makedirs(test_path, exist_ok=True)

            resolved = ConfigLoader.resolve_core_root("$IBEX_ROOT")
            assert resolved == test_path

        finally:
            # Cleanup
            if orig_ibex_root:
                os.environ["IBEX_ROOT"] = orig_ibex_root
            elif "IBEX_ROOT" in os.environ:
                del os.environ["IBEX_ROOT"]

            if os.path.exists(test_path):
                os.rmdir(test_path)

    def test_core_root_fallback(self):
        """Test core_root fallback paths."""
        # Temporarily unset IBEX_ROOT
        orig_ibex_root = os.environ.get("IBEX_ROOT")
        if "IBEX_ROOT" in os.environ:
            del os.environ["IBEX_ROOT"]

        try:
            # Should fall back to ../PdatCoreSim/cores/ibex or similar
            resolved = ConfigLoader.resolve_core_root("$IBEX_ROOT")

            # Should resolve to some fallback path
            assert os.path.isabs(resolved)
            assert "ibex" in resolved.lower()

        finally:
            # Restore original
            if orig_ibex_root:
                os.environ["IBEX_ROOT"] = orig_ibex_root

    def test_core_root_not_found(self, tmp_path):
        """Test error when core_root doesn't exist."""
        # Temporarily unset IBEX_ROOT and use non-existent path
        orig_ibex_root = os.environ.get("IBEX_ROOT")
        if "IBEX_ROOT" in os.environ:
            del os.environ["IBEX_ROOT"]

        try:
            # Create config with non-existent core_root
            config_file = tmp_path / "test.yaml"
            config_file.write_text("""
core_name: "test"
architecture: "rv32"
signals:
  instruction_data: "instr"
  pc: "pc"
synthesis:
  core_root: "/nonexistent/path/to/core"
  source_files: ["file.sv"]
  include_dirs: ["rtl"]
""")

            with pytest.raises(FileNotFoundError) as exc_info:
                ConfigLoader.load_config(str(config_file))

            assert "core root" in str(exc_info.value).lower() or "not found" in str(exc_info.value).lower()

        finally:
            if orig_ibex_root:
                os.environ["IBEX_ROOT"] = orig_ibex_root


class TestParameterHandling:
    """Test synthesis parameter configuration."""

    def test_default_parameters(self):
        """Test default parameter values."""
        config_file = FIXTURES_DIR / "ibex_test.yaml"
        config = ConfigLoader.load_config(str(config_file))

        # Should have default parameters
        assert "writeback_stage" in config.synthesis.parameters
        assert config.synthesis.parameters["writeback_stage"] == False

    def test_abc_config(self):
        """Test ABC configuration defaults."""
        config_file = FIXTURES_DIR / "ibex_test.yaml"
        config = ConfigLoader.load_config(str(config_file))

        assert "default_depth" in config.synthesis.abc_config
        assert config.synthesis.abc_config["default_depth"] == 2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
