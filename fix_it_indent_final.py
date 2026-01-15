#!/usr/bin/env python3
"""
Fix 'it' block indentation in SSpec files.

Problem: When a describe block has a docstring, the 'it' blocks are
indented at +8 spaces from describe, but they should be at +4 (same as
the docstring).

Correct structure:
describe "Test":          # 0 spaces
    \"""Docstring\"""       # 4 spaces
    it "test":            # 4 spaces (same as docstring)
        val x = 42        # 8 spaces (from describe)
"""

import re
from pathlib import Path

def fix_spec_file(filepath):
    """Fix it block indentation after describe docstrings."""
    with open(filepath, 'r') as f:
        lines = f.readlines()

    fixed_lines = []
    changes = 0
    i = 0

    while i < len(lines):
        line = lines[i]

        # Check for describe block
        match = re.match(r'^(\s*)describe ', line)
        if match:
            describe_indent = len(match.group(1))
            docstring_indent = describe_indent + 4

            fixed_lines.append(line)
            i += 1

            # Check if next non-empty line starts a docstring
            found_docstring_start = False
            docstring_end_idx = None

            while i < len(lines):
                current = lines[i]
                if current.strip():
                    if '"""' in current:
                        found_docstring_start = True
                        fixed_lines.append(current)
                        i += 1

                        # Find end of docstring
                        while i < len(lines):
                            doc_line = lines[i]
                            fixed_lines.append(doc_line)
                            if '"""' in doc_line:
                                docstring_end_idx = i
                                i += 1
                                break
                            i += 1
                        break
                    else:
                        break
                else:
                    fixed_lines.append(current)
                    i += 1

            # If describe has docstring, fix it/context blocks
            if found_docstring_start and docstring_end_idx is not None:
                while i < len(lines):
                    current = lines[i]
                    current_indent = len(current) - len(current.lstrip())

                    # Stop at next describe or less-indented line
                    if current.strip() and re.match(r'^\s*describe ', current):
                        break
                    if current.strip() and current_indent < docstring_indent:
                        fixed_lines.append(current)
                        i += 1
                        break

                    # Fix it/context blocks that are over-indented (at +8 instead of +4)
                    it_match = re.match(r'^(\s+)(it|context) "', current)
                    if it_match and current_indent == docstring_indent + 4:
                        # This it block is at +8 from describe, should be at +4
                        # De-indent by 4 spaces
                        fixed_line = ' ' * docstring_indent + current.lstrip()
                        fixed_lines.append(fixed_line)
                        changes += 1
                        i += 1

                        # Also de-indent everything in this it/context block by 4
                        while i < len(lines):
                            block_line = lines[i]
                            block_indent = len(block_line) - len(block_line.lstrip())

                            # Stop at next it/context/describe at same or lower level
                            if block_line.strip() and re.match(r'^\s*(it|context|describe)', block_line):
                                if block_indent <= docstring_indent + 4:
                                    break

                            # De-indent by 4 if it's part of the it block
                            if block_line.strip() and block_indent > docstring_indent:
                                new_indent = max(0, block_indent - 4)
                                fixed_block_line = ' ' * new_indent + block_line.lstrip()
                                fixed_lines.append(fixed_block_line)
                                i += 1
                            elif not block_line.strip():
                                fixed_lines.append(block_line)
                                i += 1
                            else:
                                break
                    else:
                        fixed_lines.append(current)
                        i += 1
                continue

        fixed_lines.append(line)
        i += 1

    if changes > 0:
        with open(filepath, 'w') as f:
            f.writelines(fixed_lines)
        print(f"✓ Fixed {changes} it/context blocks in {filepath.name}")
        return True
    else:
        print(f"  No changes needed in {filepath.name}")
        return False

def main():
    spec_dir = Path('simple/std_lib/test/features')

    failing_specs = [
        'codegen/cranelift_spec.spl',
        'concurrency/async_await_spec.spl',
        'concurrency/async_default_spec.spl',
        'concurrency/generators_spec.spl',
        'control_flow/conditionals_spec.spl',
        'control_flow/error_handling_spec.spl',
        'control_flow/loops_spec.spl',
        'control_flow/match_spec.spl',
        'data_structures/arrays_spec.spl',
        'data_structures/dicts_spec.spl',
        'data_structures/sets_spec.spl',
        'data_structures/strings_spec.spl',
        'data_structures/tuples_spec.spl',
        'infrastructure/parser_spec.spl',
        'ml/config_system_spec.spl',
        'ml/torch_caching_spec.spl',
        'ml/training_engine_spec.spl',
        'stdlib/file_io_spec.spl',
        'testing_framework/after_each_spec.spl',
        'testing_framework/before_each_spec.spl',
        'types/basic_types_spec.spl',
        'types/enums_spec.spl',
        'types/operators_spec.spl',
        'types/option_result_spec.spl',
    ]

    total_fixed = 0
    for spec_path in failing_specs:
        filepath = spec_dir / spec_path
        if filepath.exists():
            if fix_spec_file(filepath):
                total_fixed += 1
        else:
            print(f"✗ File not found: {filepath}")

    print(f"\nFixed {total_fixed}/{len(failing_specs)} files")

if __name__ == '__main__':
    main()
