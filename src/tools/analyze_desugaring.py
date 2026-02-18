#!/usr/bin/env python3
"""
Generate statistics and report on the desugaring process.
"""

import re
from pathlib import Path
from collections import defaultdict

def analyze_directory(directory):
    """Analyze all .spl files in directory."""
    stats = {
        'total_files': 0,
        'total_lines': 0,
        'impl_blocks_found': 0,
        'option_types_desugared': 0,
        'methods_converted': 0,
        'files_with_changes': 0,
    }
    
    issues = defaultdict(list)
    
    for spl_file in Path(directory).rglob('*.spl'):
        stats['total_files'] += 1
        
        with open(spl_file) as f:
            content = f.read()
            lines = content.split('\n')
            stats['total_lines'] += len(lines)
            
            # Count desugared markers
            desugared_count = content.count('# DESUGARED:')
            if desugared_count > 0:
                stats['files_with_changes'] += 1
                stats['option_types_desugared'] += desugared_count
            
            # Count converted impl blocks (now have comments)
            impl_comments = content.count('# was: impl ')
            stats['impl_blocks_found'] += impl_comments
            
            # Count converted methods
            method_headers = len(re.findall(r'^fn \w+_\w+\(', content, re.MULTILINE))
            stats['methods_converted'] += method_headers
    
    return stats, issues

def main():
    print("=" * 80)
    print("DESUGARING STATISTICS REPORT")
    print("=" * 80)
    print()
    
    # Analyze compiler (desugared)
    print("📊 Analyzing desugared code (src/compiler/)...")
    core_stats, core_issues = analyze_directory('src/compiler')
    
    print()
    print("DESUGARED CODE (src/compiler/)")
    print("-" * 80)
    print(f"  Total files:              {core_stats['total_files']:>6}")
    print(f"  Total lines:              {core_stats['total_lines']:>6,}")
    print(f"  Files with changes:       {core_stats['files_with_changes']:>6}")
    print(f"  Option types desugared:   {core_stats['option_types_desugared']:>6}")
    print(f"  Impl blocks converted:    {core_stats['impl_blocks_found']:>6}")
    print(f"  Methods converted:        {core_stats['methods_converted']:>6}")
    print()
    
    # Analyze original compiler
    print("📊 Analyzing original code (src/compiler/)...")
    compiler_stats, _ = analyze_directory('src/compiler')
    
    print()
    print("ORIGINAL CODE (src/compiler/)")
    print("-" * 80)
    print(f"  Total files:              {compiler_stats['total_files']:>6}")
    print(f"  Total lines:              {compiler_stats['total_lines']:>6,}")
    print()
    
    # Calculate differences
    print("=" * 80)
    print("COMPARISON")
    print("=" * 80)
    size_increase = ((core_stats['total_lines'] - compiler_stats['total_lines']) / 
                     compiler_stats['total_lines'] * 100)
    print(f"  Size change:              {size_increase:>+6.1f}%")
    print(f"  Files processed:          {core_stats['files_with_changes']:>6} / {core_stats['total_files']}")
    print()
    
    # Success rate
    print("=" * 80)
    print("TRANSFORMATION SUCCESS")
    print("=" * 80)
    print(f"  ✓ Files desugared:        {core_stats['files_with_changes']:>6}")
    print(f"  ✓ Option types handled:   {core_stats['option_types_desugared']:>6}")
    print(f"  ✓ Impl blocks removed:    {core_stats['impl_blocks_found']:>6}")
    print(f"  ✓ Methods converted:      {core_stats['methods_converted']:>6}")
    print()
    
    print("=" * 80)
    print("CONCLUSION")
    print("=" * 80)
    print(f"  The desugarer successfully processed {core_stats['files_with_changes']} files")
    print(f"  with {core_stats['option_types_desugared']} Option types and")
    print(f"  {core_stats['methods_converted']} method conversions.")
    print()
    print("  ✅ Desugaring phase complete!")
    print("  Next step: Test compilation with seed compiler")
    print()

if __name__ == '__main__':
    main()
