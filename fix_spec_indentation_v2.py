#!/usr/bin/env python3
"""
Fix indentation in SSpec test files.

Problem: Code after docstrings in `it` blocks has 0 indentation when it should
have proper indentation to be inside the `it` block.
"""

import re
from pathlib import Path

def fix_spec_file(filepath):
    """Fix indentation issues in a spec file."""
    with open(filepath, 'r') as f:
        lines = f.readlines()

    fixed_lines = []
    changes = 0
    i = 0

    while i < len(lines):
        line = lines[i]
        fixed_lines.append(line)

        # Check if this is an `it` or `context` block line
        match = re.match(r'^(\s+)(it|context) ', line)
        if match:
            block_indent = len(match.group(1))
            expected_body_indent = block_indent + 4

            i += 1
            # Look for docstring
            found_docstring = False
            while i < len(lines):
                current = lines[i]
                current_stripped = current.strip()

                # If we hit another block at same or lower indent, stop
                if current_stripped and not current.startswith(' ' * (block_indent + 1)):
                    break

                # Check for docstring
                if '"""' in current and not found_docstring:
                    found_docstring = True
                    fixed_lines.append(current)
                    i += 1

                    # Read until end of docstring
                    while i < len(lines):
                        doc_line = lines[i]
                        fixed_lines.append(doc_line)
                        if '"""' in doc_line:
                            i += 1
                            break
                        i += 1

                    # Now fix the code lines after the docstring
                    while i < len(lines):
                        code_line = lines[i]
                        code_stripped = code_line.strip()
                        code_indent = len(code_line) - len(code_line.lstrip())

                        # Stop if we hit empty line followed by less-indented content
                        if not code_stripped:
                            fixed_lines.append(code_line)
                            i += 1
                            # Peek at next line
                            if i < len(lines):
                                next_line = lines[i]
                                next_indent = len(next_line) - len(next_line.lstrip())
                                if next_line.strip() and next_indent <= block_indent:
                                    # Next content is at same or lower level - end of it block
                                    break
                            continue

                        # Stop if we hit another it/context/describe at same or lower indent
                        if re.match(r'^\s*(it|context|describe|print\(")', code_line):
                            if code_indent <= block_indent:
                                break

                        # Fix indentation if line needs it
                        if code_stripped and code_indent < expected_body_indent:
                            fixed_line = ' ' * expected_body_indent + code_line.lstrip()
                            fixed_lines.append(fixed_line)
                            changes += 1
                            i += 1
                        else:
                            fixed_lines.append(code_line)
                            i += 1
                    break
                else:
                    fixed_lines.append(current)
                    i += 1
            continue

        i += 1

    if changes > 0:
        with open(filepath, 'w') as f:
            f.writelines(fixed_lines)
        print(f"✓ Fixed {changes} lines in {filepath.name}")
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
