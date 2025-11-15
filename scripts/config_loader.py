#!/usr/bin/env python3
"""
Configuration file loader and validator for PDAT Synthesis.

Loads YAML configuration files and validates them against the schema.
Handles environment variable expansion and path resolution.
"""

import os
import sys
import yaml
from pathlib import Path
from typing import Dict, Any, Optional, List
from dataclasses import dataclass


@dataclass
class InjectionPoint:
    """Configuration for a single injection point."""
    name: str
    source_file: str
    constraint_type: str
    module_path: Optional[str] = None
    description: Optional[str] = None
    signals: Optional[Dict[str, Any]] = None


@dataclass
class SynthesisConfig:
    """Synthesis-specific configuration."""
    core_root: str
    core_root_resolved: str  # After environment variable expansion
    source_files: List[str]
    include_dirs: List[str]
    top_module: str = "ibex_core"
    parameters: Dict[str, Any] = None
    abc_config: Dict[str, Any] = None
    pre_synthesized: bool = False  # Whether core uses pre-synthesized (gate-level) Verilog
    cell_library: Optional[str] = None  # Path to standard cell library for pre-synthesized cores

    def __post_init__(self):
        if self.parameters is None:
            self.parameters = {}
        if self.abc_config is None:
            self.abc_config = {"default_depth": 2}


@dataclass
class CoreConfig:
    """Complete core configuration."""
    core_name: str
    architecture: str
    signals: Dict[str, Any]
    synthesis: SynthesisConfig
    injections: List[InjectionPoint]
    vcd: Optional[Dict[str, Any]] = None
    result_muxes: Optional[List[Dict[str, Any]]] = None  # For ODC mux-level analysis

    def get_injection(self, constraint_type: str) -> Optional[InjectionPoint]:
        """Get injection point by constraint type."""
        for inj in self.injections:
            if inj.constraint_type == constraint_type:
                return inj
        return None

    def get_injection_by_name(self, name: str) -> Optional[InjectionPoint]:
        """Get injection point by name."""
        for inj in self.injections:
            if inj.name == name:
                return inj
        return None


class ConfigLoader:
    """Loads and validates YAML configuration files."""

    @staticmethod
    def expand_env_vars(value: str) -> str:
        """Expand environment variables in a string.

        Supports $VAR and ${VAR} syntax.
        """
        if not isinstance(value, str):
            return value

        # Handle ${VAR} style
        import re
        def replacer(match):
            var_name = match.group(1)
            return os.environ.get(var_name, match.group(0))

        value = re.sub(r'\$\{([^}]+)\}', replacer, value)

        # Handle $VAR style
        value = re.sub(r'\$([A-Za-z_][A-Za-z0-9_]*)', replacer, value)

        return value

    @staticmethod
    def resolve_core_root(core_root_config: str) -> str:
        """Resolve core_root path with environment variable expansion and fallbacks.

        Args:
            core_root_config: Path from config (may contain env vars)

        Returns:
            Absolute path to core root

        Raises:
            FileNotFoundError: If core root cannot be found
        """
        # First try to expand environment variables
        expanded = ConfigLoader.expand_env_vars(core_root_config)

        # If it starts with $, it means the env var wasn't set
        if expanded.startswith('$'):
            # Extract the variable name
            var_name = expanded.split('/')[0][1:]  # Remove leading $

            # Infer core name from environment variable (e.g., IBEX_ROOT -> ibex)
            core_name = var_name.replace('_ROOT', '').lower()

            # Try common fallback paths (relative to this script's parent directory)
            script_dir = Path(__file__).parent.parent  # Go up to project root
            fallback_paths = [
                script_dir.parent / 'PdatCoreSim' / 'cores' / core_name,
                script_dir.parent / 'CoreSim' / 'cores' / core_name,
            ]

            for fallback in fallback_paths:
                fallback_abs = fallback.resolve()
                if fallback_abs.is_dir():
                    print(f"Warning: ${var_name} not set, using fallback: {fallback_abs}", file=sys.stderr)
                    return str(fallback_abs)

            raise FileNotFoundError(
                f"Environment variable ${var_name} not set and no fallback paths found.\n"
                f"Tried: {', '.join(str(p) for p in fallback_paths)}\n"
                f"Please set ${var_name} or ensure core is in a fallback location."
            )

        # Expand user home directory and make absolute
        resolved = os.path.abspath(os.path.expanduser(expanded))

        if not os.path.isdir(resolved):
            raise FileNotFoundError(f"Core root directory not found: {resolved}")

        return resolved

    @staticmethod
    def validate_required_fields(config: Dict[str, Any], required: List[str], context: str = "config"):
        """Validate that required fields are present."""
        missing = [field for field in required if field not in config]
        if missing:
            raise ValueError(f"Missing required fields in {context}: {', '.join(missing)}")

    @staticmethod
    def load_config(config_path: str) -> CoreConfig:
        """Load and validate a configuration file.

        Args:
            config_path: Path to YAML config file

        Returns:
            CoreConfig object

        Raises:
            FileNotFoundError: If config file not found
            ValueError: If config is invalid
        """
        config_path = Path(config_path)

        if not config_path.exists():
            raise FileNotFoundError(f"Config file not found: {config_path}")

        # Load YAML
        with open(config_path, 'r') as f:
            data = yaml.safe_load(f)

        if not data:
            raise ValueError(f"Empty config file: {config_path}")

        # Validate top-level required fields
        ConfigLoader.validate_required_fields(
            data,
            ['core_name', 'architecture', 'signals', 'synthesis']
        )

        # Validate synthesis section
        synth_data = data['synthesis']
        ConfigLoader.validate_required_fields(
            synth_data,
            ['core_root', 'source_files', 'include_dirs'],
            context="synthesis"
        )

        # Resolve core_root
        core_root_resolved = ConfigLoader.resolve_core_root(synth_data['core_root'])

        # Parse synthesis config
        synthesis = SynthesisConfig(
            core_root=synth_data['core_root'],
            core_root_resolved=core_root_resolved,
            source_files=synth_data['source_files'],
            include_dirs=synth_data['include_dirs'],
            top_module=synth_data.get('top_module', 'ibex_core'),
            parameters=synth_data.get('parameters', {}),
            abc_config=synth_data.get('abc', {'default_depth': 2}),
            pre_synthesized=synth_data.get('pre_synthesized', False),
            cell_library=synth_data.get('cell_library')
        )

        # Parse injection points
        injections = []
        if 'injections' in data:
            for inj_data in data['injections']:
                ConfigLoader.validate_required_fields(
                    inj_data,
                    ['name', 'source_file', 'constraint_type'],
                    context=f"injection '{inj_data.get('name', 'unknown')}'"
                )

                injections.append(InjectionPoint(
                    name=inj_data['name'],
                    source_file=inj_data['source_file'],
                    constraint_type=inj_data['constraint_type'],
                    module_path=inj_data.get('module_path'),
                    description=inj_data.get('description'),
                    signals=inj_data.get('signals')
                ))

        # Create and return CoreConfig
        return CoreConfig(
            core_name=data['core_name'],
            architecture=data['architecture'],
            signals=data['signals'],
            synthesis=synthesis,
            injections=injections,
            vcd=data.get('vcd'),
            result_muxes=data.get('result_muxes')  # For ODC analysis
        )

    @staticmethod
    def find_config_file(core_name: Optional[str] = None, config_dir: str = "configs") -> str:
        """Find config file by core name.

        Args:
            core_name: Name of core (e.g., 'ibex')
            config_dir: Directory containing configs

        Returns:
            Path to config file

        Raises:
            FileNotFoundError: If config not found
        """
        if core_name is None:
            core_name = "ibex"  # Default

        config_path = Path(config_dir) / f"{core_name}.yaml"

        if not config_path.exists():
            raise FileNotFoundError(
                f"Config file not found: {config_path}\n"
                f"Available configs: {', '.join(p.stem for p in Path(config_dir).glob('*.yaml') if p.stem != 'schema')}"
            )

        return str(config_path)


def main():
    """Test config loader."""
    import argparse

    parser = argparse.ArgumentParser(description="Test config loader")
    parser.add_argument('config', help='Path to config file')
    parser.add_argument('--dump', action='store_true', help='Dump parsed config')

    args = parser.parse_args()

    try:
        config = ConfigLoader.load_config(args.config)
        print(f"✓ Successfully loaded config: {config.core_name}")
        print(f"  Architecture: {config.architecture}")
        print(f"  Core root: {config.synthesis.core_root_resolved}")
        print(f"  Top module: {config.synthesis.top_module}")
        print(f"  Source files: {len(config.synthesis.source_files)} files")
        print(f"  Injection points: {len(config.injections)}")
        for inj in config.injections:
            print(f"    - {inj.name}: {inj.constraint_type} → {inj.source_file}")

        if args.dump:
            print("\nFull config:")
            print(config)

    except Exception as e:
        print(f"✗ Error loading config: {e}")
        return 1

    return 0


if __name__ == "__main__":
    exit(main())
