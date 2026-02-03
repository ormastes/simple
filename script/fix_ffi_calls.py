#!/usr/bin/env python3
"""
FFI Call Fixer Script
Adds TODO comments for direct FFI calls and creates missing wrappers
"""

import re
import os
from pathlib import Path
from collections import defaultdict

# Directories to exclude (core/internal code that should use direct FFI)
EXCLUDE_PATTERNS = [
    '/core/',
    '/collections/',  # Internal collection implementations
    '.disabled',
    '/ffi_gen/specs/',  # FFI generation specs
    '/test/',  # Test files are OK to use direct FFI for now
]

# Files that are FFI wrapper modules themselves
WRAPPER_MODULES = [
    'src/app/io/mod.spl',
    'src/compiler/ffi.spl',
    'src/compiler/ffi_minimal.spl',
]

# Common FFI functions that should have wrappers
COMMON_FFI_WRAPPERS = {
    'rt_file_exists': 'file_exists',
    'rt_file_read_text': 'file_read_text',
    'rt_file_write_text': 'file_write_text',
    'rt_file_delete': 'file_delete',
    'rt_dir_create': 'dir_create',
    'rt_env_get': 'env_get',
    'rt_process_run': 'process_run',
}

def should_skip_file(filepath):
    """Check if file should be skipped"""
    for pattern in EXCLUDE_PATTERNS:
        if pattern in filepath:
            return True
    if filepath in WRAPPER_MODULES:
        return True
    return False

def find_rt_calls_in_line(line):
    """Find all rt_* function calls in a line"""
    # Match rt_function_name(
    pattern = r'\brt_[a-z_]+\('
    matches = re.finditer(pattern, line)
    return [m.group()[:-1] for m in matches]  # Remove trailing (

def is_wrapper_definition(line, prev_lines):
    """Check if this line is inside a wrapper function definition"""
    # Look back to see if we're in a function that's a wrapper
    for prev in reversed(prev_lines[-10:]):
        if prev.strip().startswith('fn ') and ':' not in prev:
            return True
        if prev.strip().startswith('extern fn'):
            return False
    return False

def add_todo_comment(filepath):
    """Add TODO comments to direct FFI calls"""
    if should_skip_file(filepath):
        return 0

    try:
        with open(filepath, 'r') as f:
            lines = f.readlines()
    except:
        return 0

    modified = False
    new_lines = []
    prev_lines = []
    i = 0

    while i < len(lines):
        line = lines[i]
        rt_calls = find_rt_calls_in_line(line)

        if rt_calls and not line.strip().startswith('extern fn'):
            # Check if already has TODO comment
            has_todo = (i > 0 and 'TODO' in lines[i-1])

            if not has_todo and not is_wrapper_definition(line, prev_lines):
                # Add TODO comment
                indent = len(line) - len(line.lstrip())
                wrapper_names = [COMMON_FFI_WRAPPERS.get(call, call.replace('rt_', ''))
                               for call in rt_calls]

                todo_comment = ' ' * indent + '# TODO: Replace direct FFI call with wrapper '
                if len(rt_calls) == 1:
                    todo_comment += f'({wrapper_names[0]}) from app.io or compiler.ffi'
                else:
                    todo_comment += f'functions from app.io or compiler.ffi'
                todo_comment += '\n'

                new_lines.append(todo_comment)
                modified = True

        new_lines.append(line)
        prev_lines.append(line)
        i += 1

    if modified:
        with open(filepath, 'w') as f:
            f.writelines(new_lines)

    return 1 if modified else 0

def find_missing_wrappers():
    """Find FFI functions that don't have wrappers"""
    # Read app.io module
    io_module = Path('src/app/io/mod.spl')
    if not io_module.exists():
        return {}

    with open(io_module, 'r') as f:
        content = f.read()

    # Find all extern fn declarations
    extern_pattern = r'extern fn (rt_[a-z_]+)\('
    externs = set(re.findall(extern_pattern, content))

    # Find all wrapper functions
    wrapper_pattern = r'fn ([a-z_]+)\([^)]*\):[^{]*\n\s*(rt_[a-z_]+)\('
    wrappers = {}
    for match in re.finditer(wrapper_pattern, content):
        wrapper_name, rt_name = match.groups()
        wrappers[rt_name] = wrapper_name

    # Find missing wrappers
    missing = {}
    for extern in externs:
        if extern not in wrappers:
            missing[extern] = extern.replace('rt_', '')

    return missing

def create_missing_wrapper_report():
    """Create a report of missing wrappers with code to add"""
    missing = find_missing_wrappers()

    if not missing:
        return "All FFI functions have wrappers!"

    report = "# Missing FFI Wrappers\n\n"
    report += f"Found {len(missing)} FFI functions without wrappers.\n\n"
    report += "## Wrappers to Add\n\n"
    report += "Add these to `src/app/io/mod.spl`:\n\n"
    report += "```simple\n"

    for rt_name, wrapper_name in sorted(missing.items()):
        report += f"# TODO: Add wrapper for {rt_name}\n"
        report += f"fn {wrapper_name}(...) -> ...:\n"
        report += f"    {rt_name}(...)\n\n"

    report += "```\n"

    return report

def main():
    print("=== FFI Call Fixer ===")
    print("")

    # Step 1: Find and add TODO comments
    print("Step 1: Adding TODO comments to direct FFI calls...")
    files_modified = 0

    for root, dirs, files in os.walk('src'):
        # Skip certain directories
        dirs[:] = [d for d in dirs if d not in ['core', '__pycache__']]

        for file in files:
            if file.endswith('.spl'):
                filepath = os.path.join(root, file)
                files_modified += add_todo_comment(filepath)

    print(f"  Modified {files_modified} files")
    print("")

    # Step 2: Create missing wrapper report
    print("Step 2: Generating missing wrapper report...")
    report = create_missing_wrapper_report()

    os.makedirs('doc/report', exist_ok=True)
    with open('doc/report/missing_ffi_wrappers.md', 'w') as f:
        f.write(report)

    print("  Report saved to: doc/report/missing_ffi_wrappers.md")
    print("")

    print("Done!")
    print("")
    print("Next steps:")
    print("  1. Review modified files for TODO comments")
    print("  2. Check doc/report/missing_ffi_wrappers.md for wrappers to add")
    print("  3. Create wrappers in src/app/io/mod.spl or src/compiler/ffi.spl")
    print("  4. Replace direct FFI calls with wrapper calls")

if __name__ == '__main__':
    main()
