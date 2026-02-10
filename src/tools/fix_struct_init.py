#!/usr/bin/env python3
"""
Fix struct initialization syntax errors from desugaring.

The issue: Some(value) was replaced with invalid syntax:
    field: has_field = true, field_value = value

Should be:
    has_field: true,
    field_value: value
"""

import re
import sys
from pathlib import Path

def fix_struct_init(content: str) -> str:
    """Fix struct initialization with Some() replacements."""
    
    # Pattern: field: has_field = true, field_value = X
    # Should be split into two separate field initializations
    
    # Find and fix the pattern
    pattern = r'(\w+):\s*has_field\s*=\s*true,\s*field_value\s*=\s*([^,\n]+)'
    
    def replace_func(match):
        field_name = match.group(1)
        value = match.group(2).strip()
        
        # Generate correct syntax
        return f"# DESUGARED: {field_name}: Some({value})\n            has_{field_name}: true,\n            {field_name}_value: {value}"
    
    fixed = re.sub(pattern, replace_func, content)
    
    # Also fix simple nil cases that weren't handled
    # Pattern: field: nil, where field should be desugared
    lines = fixed.split('\n')
    result = []
    
    for i, line in enumerate(lines):
        # Check if this is a field with nil in struct initialization
        nil_match = re.match(r'(\s+)(\w+):\s*nil,?\s*(#.*)?$', line)
        if nil_match:
            indent, field_name, comment = nil_match.groups()
            
            # Check if previous or next lines suggest this is an Option field
            # by looking for has_* pattern nearby
            context = '\n'.join(lines[max(0, i-5):min(len(lines), i+5)])
            
            if f'has_{field_name}' in context or field_name in ['pending_token', 'block_registry', 'current_block_kind', 'unified_registry']:
                # This is likely an Option field
                result.append(f'{indent}# DESUGARED: {field_name}: nil')
                result.append(f'{indent}has_{field_name}: false,')
                if comment:
                    result.append(f'{indent}# {comment}')
            else:
                result.append(line)
        else:
            result.append(line)
    
    return '\n'.join(result)

def fix_file(file_path: Path) -> bool:
    """Fix a single file. Returns True if changes were made."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        fixed = fix_struct_init(content)
        
        if fixed != content:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(fixed)
            print(f"  ✓ Fixed: {file_path.name}")
            return True
        else:
            return False
    except Exception as e:
        print(f"  ✗ Error fixing {file_path}: {e}")
        return False

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 fix_struct_init.py <directory>")
        print("Example: python3 fix_struct_init.py src/compiler_core")
        sys.exit(1)
    
    directory = Path(sys.argv[1])
    
    print("="*70)
    print("Fixing Struct Initialization Syntax")
    print("="*70)
    print()
    
    files_fixed = 0
    files_checked = 0
    
    for spl_file in directory.rglob('*.spl'):
        files_checked += 1
        if fix_file(spl_file):
            files_fixed += 1
    
    print()
    print(f"Checked {files_checked} files")
    print(f"Fixed {files_fixed} files")
    print()
    
    if files_fixed > 0:
        print("✅ Fixes applied! Re-run validation to verify.")
    else:
        print("✓ No fixes needed.")

if __name__ == '__main__':
    main()
