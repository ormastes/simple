#!/usr/bin/env python3
"""Migrate #[...] attribute syntax to @... syntax in .spl files.

Handles:
  #[name]           → @name
  #[name(args)]     → @name(args)
  #[name = "value"] → @name("value")
  #![name(args)]    → @name(args)

Skips:
  - Lines where #[ appears inside a string literal
  - Files in ffi_gen/ directories (Rust code generation)
"""

import os
import re
import sys

# Directories to skip (contain Rust codegen that emits #[repr(C)] etc.)
SKIP_DIRS = {'ffi_gen', 'node_modules', '.git', 'target', 'build'}

# Counters
files_modified = 0
lines_modified = 0
total_replacements = 0


def is_inside_string(line, match_start):
    """Check if position match_start is inside a string literal."""
    in_string = False
    quote_char = None
    i = 0
    while i < match_start:
        ch = line[i]
        if not in_string:
            if ch == '"' or ch == "'":
                in_string = True
                quote_char = ch
        else:
            if ch == '\\':
                i += 1  # skip escaped char
            elif ch == quote_char:
                in_string = False
        i += 1
    return in_string


def is_comment_line(line):
    """Check if the #[ is part of a comment (line starts with #)."""
    stripped = line.lstrip()
    # If line starts with # but not #[ or #!, it's a comment
    if stripped.startswith('#') and not stripped.startswith('#[') and not stripped.startswith('#!'):
        return True
    return False


def migrate_line(line):
    """Migrate a single line from #[...] to @... syntax. Returns (new_line, count)."""
    count = 0
    result = line

    # Pattern 1: #![name(args)] → @name(args) (inner attributes)
    def replace_inner(m):
        nonlocal count
        if is_inside_string(result, m.start()):
            return m.group(0)
        count += 1
        name = m.group(1)
        args = m.group(2) if m.group(2) else ''
        return f'@{name}{args}'

    result = re.sub(r'#!\[(\w+)((?:\([^)]*\))?)\]', replace_inner, result)

    # Pattern 2: #[name = "value"] → @name("value")
    def replace_assign(m):
        nonlocal count
        if is_inside_string(result, m.start()):
            return m.group(0)
        count += 1
        name = m.group(1)
        value = m.group(2)
        return f'@{name}("{value}")'

    result = re.sub(r'#\[(\w+)\s*=\s*"([^"]*)"\]', replace_assign, result)

    # Pattern 3: #[name(args)] → @name(args) (with nested parens support)
    def replace_with_args(m):
        nonlocal count
        if is_inside_string(result, m.start()):
            return m.group(0)
        count += 1
        name = m.group(1)
        args = m.group(2)
        return f'@{name}({args})'

    result = re.sub(r'#\[(\w+)\(([^)]*)\)\]', replace_with_args, result)

    # Pattern 4: #[name] → @name (simple, no args)
    def replace_simple(m):
        nonlocal count
        if is_inside_string(result, m.start()):
            return m.group(0)
        count += 1
        name = m.group(1)
        return f'@{name}'

    result = re.sub(r'#\[(\w+)\]', replace_simple, result)

    return result, count


def should_skip_dir(dirpath):
    """Check if directory should be skipped."""
    parts = dirpath.split(os.sep)
    return any(skip in parts for skip in SKIP_DIRS)


def migrate_file(filepath):
    """Migrate a single file. Returns number of replacements."""
    global files_modified, lines_modified, total_replacements

    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except (UnicodeDecodeError, IOError):
        return 0

    new_lines = []
    file_replacements = 0

    for line in lines:
        new_line, count = migrate_line(line)
        new_lines.append(new_line)
        if count > 0:
            file_replacements += count
            lines_modified += 1

    if file_replacements > 0:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.writelines(new_lines)
        files_modified += 1
        total_replacements += file_replacements
        print(f"  {filepath}: {file_replacements} replacements")

    return file_replacements


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else '.'

    print(f"Migrating #[...] → @... in .spl files under {root}")
    print()

    for dirpath, dirnames, filenames in os.walk(root):
        # Skip unwanted directories
        if should_skip_dir(dirpath):
            continue
        # Remove skip dirs from dirnames to prevent descending
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]

        for filename in filenames:
            if not filename.endswith('.spl'):
                continue
            filepath = os.path.join(dirpath, filename)
            migrate_file(filepath)

    print()
    print(f"Done: {total_replacements} replacements in {lines_modified} lines across {files_modified} files")


if __name__ == '__main__':
    main()
