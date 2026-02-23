#!/usr/bin/env python3
"""
Remove trait impl blocks (impl Trait for Type:) from desugared code.
These are not supported in Core Simple and need to be removed or commented out.
"""

import re
import sys
from pathlib import Path

def remove_trait_impl_blocks(content: str) -> tuple[str, int]:
    """Remove or comment out trait impl blocks."""
    lines = content.split('\n')
    result = []
    removed_count = 0
    i = 0
    
    while i < len(lines):
        line = lines[i]
        
        # Check for trait impl: impl Trait for Type:
        trait_impl_match = re.match(r'^(\s*)impl\s+(\w+)\s+for\s+(\w+):', line)
        
        if trait_impl_match:
            indent, trait_name, type_name = trait_impl_match.groups()
            removed_count += 1
            
            # Comment out the impl line
            result.append(f"{indent}# REMOVED: impl {trait_name} for {type_name}:")
            result.append(f"{indent}# (Trait implementations not supported in Core Simple)")
            
            # Skip the entire impl block
            i += 1
            block_indent = len(indent)
            
            while i < len(lines):
                next_line = lines[i]
                stripped = next_line.lstrip()
                
                if not stripped:
                    # Keep empty lines
                    result.append(next_line)
                    i += 1
                    continue
                
                next_indent = len(next_line) - len(stripped)
                
                # If we're back to same or lower indent, block ended
                if next_indent <= block_indent:
                    break
                
                # Comment out the block content
                result.append(f"{next_line[:next_indent]}# {stripped}")
                i += 1
        else:
            result.append(line)
            i += 1
    
    return '\n'.join(result), removed_count

def process_file(file_path: Path) -> bool:
    """Process a single file. Returns True if changes were made."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        fixed, count = remove_trait_impl_blocks(content)
        
        if count > 0:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(fixed)
            print(f"  ✓ {file_path.name}: Removed {count} trait impl blocks")
            return True
        return False
    except Exception as e:
        print(f"  ✗ Error processing {file_path}: {e}")
        return False

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 remove_trait_impls.py <directory>")
        sys.exit(1)
    
    directory = Path(sys.argv[1])
    
    print("="*70)
    print("Removing Trait Impl Blocks")
    print("="*70)
    print()
    
    files_modified = 0
    total_impls_removed = 0
    
    for spl_file in directory.rglob('*.spl'):
        if process_file(spl_file):
            files_modified += 1
    
    print()
    print(f"Modified {files_modified} files")
    print()
    print("✅ Trait impl blocks removed!")
    print("   These are commented out and won't cause parsing errors.")

if __name__ == '__main__':
    main()
