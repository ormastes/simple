#!/usr/bin/env python3
"""
Extract testable code examples from Category B specs to _spec.spl files.
Keep original .md files as architectural reference.

Usage:
    python scripts/extract_tests_from_spec.py doc/spec/functions.md tests/specs/functions_spec.spl
    python scripts/extract_tests_from_spec.py --all  # Extract from all Category B files
"""

import re
import sys
import argparse
from pathlib import Path
from typing import Dict, List, Tuple

# Category B files: Extract examples, keep reference docs
CATEGORY_B_FILES = [
    ('functions.md', 'functions_spec.spl'),
    ('traits.md', 'traits_spec.spl'),
    ('memory.md', 'memory_spec.spl'),
    ('modules.md', 'modules_spec.spl'),
    ('data_structures.md', 'data_structures_spec.spl'),
    ('concurrency.md', 'concurrency_spec.spl'),
    ('macro.md', 'macro_spec.spl'),
    ('metaprogramming.md', 'metaprogramming_spec.spl'),
]

def extract_metadata(md_content: str) -> Dict[str, str]:
    """Extract any available metadata from markdown."""
    # Try to find any metadata in the header
    status_match = re.search(r'\*\*Status:\*\*\s*(.+)', md_content)
    feature_ids_match = re.search(r'\*\*Feature IDs?:\*\*\s*(.+)', md_content)
    
    # Get title
    title_match = re.search(r'^#\s+(.+)', md_content, re.MULTILINE)
    title = title_match.group(1).strip() if title_match else ""
    
    return {
        'title': title,
        'status': status_match.group(1).strip() if status_match else 'Reference',
        'feature_ids': feature_ids_match.group(1).strip() if feature_ids_match else '',
    }

def extract_code_examples(md_content: str) -> List[Tuple[str, str, str, int]]:
    """Extract code blocks with context.
    
    Returns list of (section, context, code, line_number) tuples.
    """
    examples = []
    
    # Split by sections (##)
    sections = re.split(r'\n##\s+', md_content)
    
    for section_text in sections:
        # Get section name (first line)
        lines = section_text.split('\n')
        section_name = lines[0].strip() if lines else "General"
        
        # Find all code blocks
        code_blocks = list(re.finditer(r'```simple\n(.*?)```', section_text, re.DOTALL))
        
        for match in code_blocks:
            code = match.group(1).strip()
            
            # Skip empty code blocks
            if not code or len(code) < 5:
                continue
            
            # Get context (paragraph before code block)
            before_code = section_text[:match.start()]
            paragraphs = [p.strip() for p in before_code.split('\n\n') if p.strip()]
            
            # Get last paragraph that isn't a header
            context = ""
            for para in reversed(paragraphs):
                if not para.startswith('#') and len(para) > 10:
                    context = para
                    break
            
            # Clean context
            context = re.sub(r'\*\*(.+?)\*\*', r'\1', context)
            context = re.sub(r'\[(.+?)\]\(.+?\)', r'\1', context)
            
            # Estimate line number
            line_num = section_text[:match.start()].count('\n') + 1
            
            examples.append((section_name, context, code, line_num))
    
    return examples

def generate_spec_spl(
    md_path: Path,
    title: str,
    status: str,
    feature_ids: str,
    examples: List[Tuple[str, str, str, int]]
) -> str:
    """Generate _spec.spl with extracted test cases only."""
    
    # Infer topic from filename
    topic = md_path.stem.replace('_', '-')
    
    # Build header
    header = f'''"""
# {title} - Test Specification

**Status:** {status}
**Feature IDs:** {feature_ids}
**Source:** {md_path.name}
**Type:** Extracted Examples (Category B)

## Overview

This file contains executable test cases extracted from {md_path.name}.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/spec/{md_path.name}

## Extracted Test Cases

{len(examples)} test cases extracted covering:
- Core functionality examples
- Edge cases and validation
- Integration patterns
"""

'''
    
    # Generate test cases
    test_content = ""
    
    if examples:
        for i, (section, context, code, line_num) in enumerate(examples, 1):
            # Generate test name
            test_name = section.lower()
            test_name = re.sub(r'[^\w\s-]', '', test_name)
            test_name = re.sub(r'[-\s]+', '_', test_name)
            test_name = f"{test_name}_{i}"
            
            # Build test
            test_content += f'## Test: {section} (Line ~{line_num})\n\n'
            
            if context and len(context) > 20:
                # Limit context to 100 chars for readability
                context_short = context[:100] + "..." if len(context) > 100 else context
                test_content += f'"""\n{context_short}\n"""\n'
            
            # Check if code already has test structure
            if 'test ' in code or code.strip().startswith('fn '):
                # Already structured, use as-is
                test_content += f'{code}\n\n'
            else:
                # Wrap in test function
                test_content += f'test "{test_name}":\n'
                
                # Indent code
                indented = '\n'.join(f'    {line}' if line.strip() else ''
                                    for line in code.split('\n'))
                test_content += f'{indented}\n'
                test_content += f'    assert_compiles()\n\n'
    else:
        test_content = '''# No testable code examples found

test "placeholder":
    """
    Placeholder test - add test cases as implementation progresses.
    """
    assert_compiles()
'''
    
    return header + test_content

def extract_tests(
    input_md: Path,
    output_spl: Path,
    dry_run: bool = False,
    verbose: bool = False
) -> bool:
    """Extract test cases from markdown spec to _spec.spl file."""
    
    if not input_md.exists():
        print(f"Error: Input file not found: {input_md}")
        return False
    
    with open(input_md, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Extract components
    metadata = extract_metadata(content)
    examples = extract_code_examples(content)
    
    # Generate output
    spl_content = generate_spec_spl(
        input_md,
        metadata['title'],
        metadata['status'],
        metadata['feature_ids'],
        examples
    )
    
    # Print info
    print(f"\n{'[DRY RUN] ' if dry_run else ''}Extracting: {input_md.name}")
    print(f"  → Output: {output_spl}")
    print(f"  Status: {metadata['status']}")
    print(f"  Code examples: {len(examples)}")
    
    if verbose:
        print(f"  Title: {metadata['title']}")
        if examples:
            print(f"  Example sections:")
            sections = {}
            for section, _, _, _ in examples:
                sections[section] = sections.get(section, 0) + 1
            for section, count in sorted(sections.items())[:5]:
                print(f"    - {section}: {count}")
    
    # Write output
    if not dry_run:
        output_spl.parent.mkdir(parents=True, exist_ok=True)
        with open(output_spl, 'w', encoding='utf-8') as f:
            f.write(spl_content)
        print(f"  ✅ Created: {output_spl}")
    else:
        print(f"  [DRY RUN] Would create: {output_spl}")
        if verbose:
            print("\n--- Preview (first 40 lines) ---")
            preview_lines = spl_content.split('\n')[:40]
            print('\n'.join(preview_lines))
            print("--- End preview ---\n")
    
    return True

def extract_all_category_b(
    base_dir: Path,
    output_dir: Path,
    dry_run: bool = False,
    verbose: bool = False
) -> Tuple[int, int]:
    """Extract tests from all Category B files."""
    
    success = 0
    total = len(CATEGORY_B_FILES)
    
    print(f"\n{'=' * 60}")
    print(f"Extracting tests from {total} Category B files")
    print(f"{'=' * 60}")
    
    for md_file, spl_file in CATEGORY_B_FILES:
        input_path = base_dir / md_file
        output_path = output_dir / spl_file
        
        if extract_tests(input_path, output_path, dry_run, verbose):
            success += 1
    
    print(f"\n{'=' * 60}")
    print(f"Extraction {'preview' if dry_run else 'complete'}: {success}/{total} successful")
    print(f"{'=' * 60}\n")
    
    return success, total

def main():
    parser = argparse.ArgumentParser(
        description='Extract test cases from Category B spec markdown files',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
Examples:
  # Extract from single file
  python scripts/extract_tests_from_spec.py doc/spec/functions.md tests/specs/functions_spec.spl
  
  # Dry run
  python scripts/extract_tests_from_spec.py --dry-run doc/spec/traits.md tests/specs/traits_spec.spl
  
  # Extract from all Category B files
  python scripts/extract_tests_from_spec.py --all
  
  # With verbose output
  python scripts/extract_tests_from_spec.py --all --verbose
'''
    )
    
    parser.add_argument(
        'input_md',
        nargs='?',
        type=Path,
        help='Input markdown file (doc/spec/*.md)'
    )
    
    parser.add_argument(
        'output_spl',
        nargs='?',
        type=Path,
        help='Output spec file (tests/specs/*_spec.spl)'
    )
    
    parser.add_argument(
        '--all',
        action='store_true',
        help='Extract from all Category B files'
    )
    
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='Preview extraction without writing files'
    )
    
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Show detailed extraction info'
    )
    
    args = parser.parse_args()
    
    # Validate arguments
    if args.all:
        base_dir = Path('doc/spec')
        output_dir = Path('tests/specs')
        success, total = extract_all_category_b(
            base_dir, output_dir, args.dry_run, args.verbose
        )
        sys.exit(0 if success == total else 1)
    
    elif args.input_md and args.output_spl:
        success = extract_tests(
            args.input_md,
            args.output_spl,
            args.dry_run,
            args.verbose
        )
        sys.exit(0 if success else 1)
    
    else:
        parser.print_help()
        sys.exit(1)

if __name__ == '__main__':
    main()
