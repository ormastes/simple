#!/usr/bin/env python3
"""
Desugar lambda expressions in Simple source files.

Handles patterns like:
  items.map(\x: expr)  ->  for loop
  items.filter(\x: cond) -> for loop with if
  something_map(items, \x: expr) -> for loop
  value.map(\x: expr) -> if-let pattern for Option.map
"""

import re
import sys
import os

def desugar_file(filepath):
    """Read a .spl file and desugar all lambda expressions."""
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    result = []
    i = 0
    changed = False
    in_docstring = False

    while i < len(lines):
        line = lines[i]
        stripped = line.lstrip()

        # Track docstrings
        if stripped.startswith('"""') or stripped.startswith('r"""'):
            check = stripped[1:] if stripped.startswith('r') else stripped
            # Count triple quotes - if odd number, toggle docstring state
            count = check.count('"""')
            if count == 1:
                in_docstring = not in_docstring
            result.append(line)
            i += 1
            continue

        if in_docstring:
            result.append(line)
            i += 1
            continue

        # Skip comments
        if stripped.startswith('#'):
            result.append(line)
            i += 1
            continue

        # Check for lambda patterns (not in strings)
        if '\\' in line and not in_string_context(line):
            new_lines = try_desugar_lambda(line, lines, i)
            if new_lines is not None:
                result.extend(new_lines)
                changed = True
                i += 1
                continue

        result.append(line)
        i += 1

    return result, changed

def in_string_context(line):
    """Check if ALL backslashes in the line are inside string literals."""
    # Simple heuristic: if there's a \x: pattern outside quotes, it's a lambda
    in_str = False
    i = 0
    text = line
    while i < len(text):
        if text[i] == '"' and (i == 0 or text[i-1] != '\\'):
            in_str = not in_str
        elif text[i] == '\\' and not in_str and i + 1 < len(text) and text[i+1].isalpha():
            return False  # Found backslash-letter outside string
        i += 1
    return True

def get_indent(line):
    """Get the indentation of a line."""
    return len(line) - len(line.lstrip())

def try_desugar_lambda(line, lines, line_idx):
    """Try to desugar a lambda on this line. Returns new lines or None."""
    indent = get_indent(line)
    indent_str = ' ' * indent
    stripped = line.rstrip('\n').rstrip()

    # Pattern 1: val x = items.map(\var: expr)
    # -> var x_list: [type] = []; for var in items: x_list.push(expr); val x = x_list
    m = re.match(r'^(\s*)(val|var)\s+(\w+)\s*=\s*(.+?)\.map\(\\(\w+):\s*(.+?)\)(.*)$', stripped)
    if m:
        ind, kw, varname, collection, param, expr, rest = m.groups()
        # Check for .join() or other chained calls after the map
        chain = rest.strip()
        tmp = f"__{varname}_list"
        new_lines = []
        new_lines.append(f"{ind}var {tmp}: [text] = []\n")
        new_lines.append(f"{ind}for {param} in {collection}:\n")
        new_lines.append(f"{ind}    {tmp}.push({expr})\n")
        if chain:
            new_lines.append(f"{ind}{kw} {varname} = {tmp}{chain}\n")
        else:
            new_lines.append(f"{ind}{kw} {varname} = {tmp}\n")
        return new_lines

    # Pattern 1b: val x = items.map(\var: expr).join(sep)
    m = re.match(r'^(\s*)(val|var)\s+(\w+)\s*=\s*(.+?)\.map\(\\(\w+):\s*(.+?)\)\.(\w+)\((.+?)\)(.*)$', stripped)
    if m:
        ind, kw, varname, collection, param, expr, method, method_arg, rest = m.groups()
        tmp = f"__{varname}_list"
        new_lines = []
        new_lines.append(f"{ind}var {tmp}: [text] = []\n")
        new_lines.append(f"{ind}for {param} in {collection}:\n")
        new_lines.append(f"{ind}    {tmp}.push({expr})\n")
        new_lines.append(f"{ind}{kw} {varname} = {tmp}.{method}({method_arg}){rest}\n")
        return new_lines

    # Pattern 2: val x = name_map(items, \var: expr)
    m = re.match(r'^(\s*)(val|var)\s+(\w+)\s*=\s*(\w+_map)\((\w+),\s*\\(\w+):\s*(.+?)\)(.*)$', stripped)
    if m:
        ind, kw, varname, fn_name, collection, param, expr, rest = m.groups()
        tmp = f"__{varname}_list"
        new_lines = []
        new_lines.append(f"{ind}var {tmp} = []\n")
        new_lines.append(f"{ind}for {param} in {collection}:\n")
        new_lines.append(f"{ind}    {tmp}.push({expr})\n")
        if rest.strip():
            new_lines.append(f"{ind}{kw} {varname} = {tmp}{rest}\n")
        else:
            new_lines.append(f"{ind}{kw} {varname} = {tmp}\n")
        return new_lines

    # Pattern 3: items.filter(\var: cond)
    m = re.match(r'^(\s*)(val|var)\s+(\w+)\s*=\s*(.+?)\.filter\(\\(\w+):\s*(.+?)\)(.*)$', stripped)
    if m:
        ind, kw, varname, collection, param, cond, rest = m.groups()
        tmp = f"__{varname}_list"
        new_lines = []
        new_lines.append(f"{ind}var {tmp} = []\n")
        new_lines.append(f"{ind}for {param} in {collection}:\n")
        new_lines.append(f"{ind}    if {cond}:\n")
        new_lines.append(f"{ind}        {tmp}.push({param})\n")
        if rest.strip():
            new_lines.append(f"{ind}{kw} {varname} = {tmp}{rest}\n")
        else:
            new_lines.append(f"{ind}{kw} {varname} = {tmp}\n")
        return new_lines

    # Pattern 4: name_filter(items, \var: cond).len()
    m = re.match(r'^(\s*)(val|var)\s+(\w+)\s*=\s*(\w+_filter)\((\w+),\s*\\(\w+):\s*(.+?)\)(.*)$', stripped)
    if m:
        ind, kw, varname, fn_name, collection, param, cond, rest = m.groups()
        tmp = f"__{varname}_list"
        new_lines = []
        new_lines.append(f"{ind}var {tmp} = []\n")
        new_lines.append(f"{ind}for {param} in {collection}:\n")
        new_lines.append(f"{ind}    if {cond}:\n")
        new_lines.append(f"{ind}        {tmp}.push({param})\n")
        if rest.strip():
            new_lines.append(f"{ind}{kw} {varname} = {tmp}{rest}\n")
        else:
            new_lines.append(f"{ind}{kw} {varname} = {tmp}\n")
        return new_lines

    # Pattern 5: assignment without val/var: x = items.map(\var: expr)
    m = re.match(r'^(\s*)(\w[\w.]*)\s*=\s*(.+?)\.map\(\\(\w+):\s*(.+?)\)(.*)$', stripped)
    if m and 'val ' not in stripped[:20] and 'var ' not in stripped[:20]:
        ind, target, collection, param, expr, rest = m.groups()
        tmp = f"__tmp_map"
        new_lines = []
        new_lines.append(f"{ind}var {tmp} = []\n")
        new_lines.append(f"{ind}for {param} in {collection}:\n")
        new_lines.append(f"{ind}    {tmp}.push({expr})\n")
        if rest.strip():
            new_lines.append(f"{ind}{target} = {tmp}{rest}\n")
        else:
            new_lines.append(f"{ind}{target} = {tmp}\n")
        return new_lines

    # If we can't desugar it automatically, return None (keep original)
    return None


def process_directory(src_dir, dst_dir):
    """Process all .spl files in src_dir, write results to dst_dir."""
    total_files = 0
    changed_files = 0

    for root, dirs, files in os.walk(src_dir):
        for fname in files:
            if not fname.endswith('.spl'):
                continue

            src_path = os.path.join(root, fname)
            rel_path = os.path.relpath(src_path, src_dir)
            dst_path = os.path.join(dst_dir, rel_path)

            os.makedirs(os.path.dirname(dst_path), exist_ok=True)

            new_lines, changed = desugar_file(src_path)
            total_files += 1
            if changed:
                changed_files += 1

            with open(dst_path, 'w', encoding='utf-8') as f:
                f.writelines(new_lines)

    print(f"Processed {total_files} files, {changed_files} had lambdas desugared")


def process_single_file(filepath):
    """Process a single file in-place."""
    new_lines, changed = desugar_file(filepath)
    if changed:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.writelines(new_lines)
        print(f"Desugared: {filepath}")
    else:
        print(f"No changes: {filepath}")


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: desugar_lambdas.py <file.spl|src_dir> [dst_dir]")
        sys.exit(1)

    path = sys.argv[1]
    if os.path.isfile(path):
        process_single_file(path)
    elif os.path.isdir(path):
        dst = sys.argv[2] if len(sys.argv) > 2 else path
        process_directory(path, dst)
    else:
        print(f"Not found: {path}")
        sys.exit(1)
