#!/usr/bin/env python3
"""
Pytest configuration for regression tests.
"""

import pytest
import os


def pytest_configure(config):
    """Configure pytest with custom markers."""
    config.addinivalue_line(
        "markers", "slow: marks tests as slow (deselect with '-m \"not slow\"')"
    )
    config.addinivalue_line(
        "markers", "requires_abc: marks tests that require ABC tool"
    )
    config.addinivalue_line(
        "markers", "requires_gates: marks tests that require gate-level synthesis"
    )


def pytest_collection_modifyitems(config, items):
    """Automatically mark tests based on content."""
    for item in items:
        # Mark tests that use --gates as requiring gates
        if "gates" in item.name.lower():
            item.add_marker(pytest.mark.requires_gates)

        # Mark ABC-related tests
        if "abc" in item.name.lower():
            item.add_marker(pytest.mark.requires_abc)
