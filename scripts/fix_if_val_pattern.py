#!/usr/bin/env python3
"""
Fix 'if val Some(x) = ...' pattern matching syntax to use match instead.
This syntax is invalid in Simple and causes parse errors.
"""

import re
import sys
from pathlib import Path

def fix_if_val_pattern(content: str) -> str:
    """
    Convert 'if val Some(x) = option:' to proper match expressions.

    Handles two cases:
    1. Statement form: if val Some(x) = opt:\n    body\nelse:\n    else_body
    2. Expression form: val x = if val Some(y) = opt:\n    expr1\nelse:\n    expr2
    """

    # Pattern for 'if val Some(var) = expr:'
    # We need to handle indentation and capture the condition
    pattern = r'(\s*)if val Some\((\w+)\)\s*=\s*([^:]+):\s*\n((?:\1    .+\n)*)\1else:\s*\n((?:\1    .+\n)*)'

    def replace_match(m):
        indent = m.group(1)
        var_name = m.group(2)
        option_expr = m.group(3).strip()
        some_body = m.group(4).rstrip('\n')
        none_body = m.group(5).rstrip('\n')

        # Dedent the bodies (remove one level of indentation)
        some_lines = some_body.split('\n')
        none_lines = none_body.split('\n')

        dedented_some = '\n'.join(line[4:] if line.startswith('    ') else line for line in some_lines)
        dedented_none = '\n'.join(line[4:] if line.startswith('    ') else line for line in none_lines)

        # Build match expression
        result = f'{indent}match {option_expr}:\n'
        result += f'{indent}    case Some({var_name}):\n'
        for line in dedented_some.split('\n'):
            if line.strip():
                result += f'{indent}        {line}\n'
        result += f'{indent}    case None:\n'
        for line in dedented_none.split('\n'):
            if line.strip():
                result += f'{indent}        {line}\n'

        return result

    # First pass: handle statement form
    content = re.sub(pattern, replace_match, content, flags=re.MULTILINE)

    # Second pass: handle expression form (val x = if val Some...)
    expr_pattern = r'(\s*)val\s+(\w+)\s*=\s*if val Some\((\w+)\)\s*=\s*([^:]+):\s*\n(\1    )(.+)\n\1else:\s*\n(\1    )(.+)'

    def replace_expr_match(m):
        indent = m.group(1)
        result_var = m.group(2)
        some_var = m.group(3)
        option_expr = m.group(4).strip()
        some_expr = m.group(6).strip()
        none_expr = m.group(8).strip()

        result = f'{indent}val {result_var} = match {option_expr}:\n'
        result += f'{indent}    case Some({some_var}):\n'
        result += f'{indent}        {some_expr}\n'
        result += f'{indent}    case None:\n'
        result += f'{indent}        {none_expr}\n'

        return result

    content = re.sub(expr_pattern, replace_expr_match, content, flags=re.MULTILINE)

    return content

def main():
    # Find all .spl files in spec directory
    spec_dir = Path('simple/std_lib/src/spec')
    if not spec_dir.exists():
        print(f"Error: {spec_dir} not found")
        sys.exit(1)

    files_modified = 0
    total_replacements = 0

    for spl_file in spec_dir.rglob('*.spl'):
        content = spl_file.read_text(encoding='utf-8')
        original_content = content

        # Check if file contains the pattern
        if 'if val Some' not in content:
            continue

        # Apply fixes
        content = fix_if_val_pattern(content)

        if content != original_content:
            spl_file.write_text(content, encoding='utf-8')
            files_modified += 1
            replacements = original_content.count('if val Some') - content.count('if val Some')
            total_replacements += replacements
            print(f"Fixed {spl_file}: {replacements} replacements")

    print(f"\nTotal: {files_modified} files modified, {total_replacements} patterns fixed")

if __name__ == '__main__':
    main()
