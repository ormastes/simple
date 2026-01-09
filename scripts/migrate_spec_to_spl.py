#!/usr/bin/env python3
"""
Convert doc/spec/*.md to tests/specs/*_spec.spl with docstring format.

Usage:
    python scripts/migrate_spec_to_spl.py doc/spec/syntax.md tests/specs/syntax_spec.spl
    python scripts/migrate_spec_to_spl.py --dry-run doc/spec/types.md
    python scripts/migrate_spec_to_spl.py --all  # Migrate all Category A files
"""

import re
import sys
import argparse
from pathlib import Path
from typing import Dict, List, Tuple, Optional

# Category A files: Direct migrations with Feature IDs
CATEGORY_A_FILES = [
    ('syntax.md', 'syntax_spec.spl', '#10-19'),
    ('types.md', 'types_spec.spl', '#20-29'),
    ('type_inference.md', 'type_inference_spec.spl', '#13'),
    ('async_default.md', 'async_default_spec.spl', '#276-285'),
    ('suspension_operator.md', 'suspension_operator_spec.spl', '#270-275'),
    ('capability_effects.md', 'capability_effects_spec.spl', '#880-884'),
    ('sandboxing.md', 'sandboxing_spec.spl', '#916-923'),
]

def extract_metadata(md_content: str) -> Dict[str, str]:
    """Extract Status, Feature IDs, Keywords from markdown frontmatter."""
    status_match = re.search(r'\*\*Status:\*\*\s*(.+)', md_content)
    feature_ids_match = re.search(r'\*\*Feature IDs?:\*\*\s*(.+)', md_content)
    keywords_match = re.search(r'\*\*Keywords?:\*\*\s*(.+)', md_content)
    last_updated_match = re.search(r'\*\*Last Updated:\*\*\s*(.+)', md_content)
    topics_match = re.search(r'\*\*Topics?:\*\*\s*(.+)', md_content)
    
    return {
        'status': status_match.group(1).strip() if status_match else 'Draft',
        'feature_ids': feature_ids_match.group(1).strip() if feature_ids_match else '',
        'keywords': keywords_match.group(1).strip() if keywords_match else '',
        'last_updated': last_updated_match.group(1).strip() if last_updated_match else '',
        'topics': topics_match.group(1).strip() if topics_match else ''
    }

def extract_title(md_content: str) -> str:
    """Extract title from first heading."""
    title_match = re.search(r'^#\s+(.+)', md_content, re.MULTILINE)
    if title_match:
        # Remove feature IDs from title
        title = title_match.group(1).strip()
        title = re.sub(r'\s*\(#[\d-]+\)', '', title)
        return title
    return "Untitled Specification"

def extract_overview(md_content: str) -> str:
    """Extract overview/introduction section."""
    # Try to find Overview section
    overview_match = re.search(
        r'##\s+Overview\s*\n+(.*?)(?=\n##|\Z)', 
        md_content, 
        re.DOTALL
    )
    if overview_match:
        return overview_match.group(1).strip()
    
    # Fallback: Extract first paragraph after frontmatter
    # Skip frontmatter (everything before first ##)
    content_start = re.search(r'\n##\s+', md_content)
    if content_start:
        before_sections = md_content[:content_start.start()]
        # Get last paragraph before sections
        paragraphs = [p.strip() for p in before_sections.split('\n\n') if p.strip()]
        if paragraphs:
            # Filter out metadata lines
            for para in reversed(paragraphs):
                if not para.startswith('**') and not para.startswith('#'):
                    return para
    
    return "TODO: Add overview from markdown"

def extract_code_examples(md_content: str) -> List[Tuple[str, str, str]]:
    """Extract code blocks with surrounding context.
    
    Returns list of (context, code, section) tuples.
    """
    examples = []
    
    # Find all sections with code blocks
    sections = re.split(r'\n##\s+', md_content)
    
    for section in sections[1:]:  # Skip before first ##
        section_name = section.split('\n')[0].strip()
        
        # Find all code blocks in this section
        code_blocks = re.finditer(
            r'```simple\n(.*?)```', 
            section, 
            re.DOTALL
        )
        
        for match in code_blocks:
            code = match.group(1).strip()
            
            # Get context (paragraph before code block)
            before_code = section[:match.start()]
            paragraphs = before_code.split('\n\n')
            context = paragraphs[-1].strip() if paragraphs else ""
            
            # Clean up context (remove markdown formatting)
            context = re.sub(r'\*\*(.+?)\*\*', r'\1', context)
            context = re.sub(r'\[(.+?)\]\(.+?\)', r'\1', context)
            
            examples.append((context, code, section_name))
    
    return examples

def extract_related_specs(md_content: str) -> List[Tuple[str, str]]:
    """Extract related specifications section."""
    related = []
    
    related_match = re.search(
        r'##\s+Related Specifications?\s*\n+(.*?)(?=\n##|\Z)',
        md_content,
        re.DOTALL
    )
    
    if related_match:
        lines = related_match.group(1).strip().split('\n')
        for line in lines:
            link_match = re.match(r'-\s+\[(.+?)\]\((.+?)\)\s*-\s*(.+)', line)
            if link_match:
                name, path, desc = link_match.groups()
                related.append((name, desc))
    
    return related

def generate_spec_spl(
    md_path: Path, 
    spl_path: Path,
    metadata: Dict[str, str],
    title: str,
    overview: str,
    examples: List[Tuple[str, str, str]],
    related: List[Tuple[str, str]]
) -> str:
    """Generate _spec.spl content."""
    
    # Build header docstring
    header = f'''"""
# {title}

**Status:** {metadata['status']}
**Feature IDs:** {metadata['feature_ids']}
**Keywords:** {metadata['keywords']}
'''
    
    if metadata['last_updated']:
        header += f"**Last Updated:** {metadata['last_updated']}\n"
    
    if metadata['topics']:
        header += f"**Topics:** {metadata['topics']}\n"
    
    try:
        rel_path = md_path.relative_to(Path.cwd())
    except ValueError:
        rel_path = md_path
    header += f"**Migrated From:** {rel_path}\n"
    
    # Add overview
    header += f"\n## Overview\n\n{overview}\n"
    
    # Add related specs if any
    if related:
        header += "\n## Related Specifications\n\n"
        for name, desc in related:
            header += f"- **{name}** - {desc}\n"
    
    header += '"""\n\n'
    
    # Add examples as test cases
    test_content = ""
    
    if examples:
        test_content += "# Test cases extracted from specification\n\n"
        
        for i, (context, code, section) in enumerate(examples, 1):
            # Generate test name from section
            test_name = section.lower().replace(' ', '_').replace('-', '_')
            test_name = re.sub(r'[^a-z0-9_]', '', test_name)
            
            if not test_name:
                test_name = f"example_{i}"
            else:
                test_name = f"{test_name}_{i}"
            
            test_content += f'## Test: {section}\n\n'
            
            if context:
                test_content += f'"""\n### Scenario: {context[:80]}...\n\n'
                test_content += f'{context}\n"""\n'
            
            # Check if code is a complete test or just an example
            if 'test ' in code or 'fn ' in code:
                # Already has test structure, include as-is
                test_content += f'{code}\n\n'
            else:
                # Wrap in test function
                test_content += f'test "{test_name}":\n'
                test_content += f'    """\n    {section}\n    """\n'
                
                # Indent code
                indented_code = '\n'.join(f'    {line}' if line.strip() else '' 
                                         for line in code.split('\n'))
                test_content += f'{indented_code}\n'
                test_content += f'    assert_compiles()\n\n'
    else:
        test_content = '''# TODO: Add test cases from specification examples

test "placeholder":
    """
    Placeholder test - replace with actual test cases from specification.
    """
    assert_compiles()
'''
    
    return header + test_content

def migrate_file(
    input_md: Path, 
    output_spl: Path,
    dry_run: bool = False,
    verbose: bool = False
) -> bool:
    """Convert markdown spec to _spec.spl format."""
    
    if not input_md.exists():
        print(f"Error: Input file not found: {input_md}")
        return False
    
    with open(input_md, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Extract components
    metadata = extract_metadata(content)
    title = extract_title(content)
    overview = extract_overview(content)
    examples = extract_code_examples(content)
    related = extract_related_specs(content)
    
    # Generate output
    spl_content = generate_spec_spl(
        input_md, output_spl, metadata, title, overview, examples, related
    )
    
    # Print info
    print(f"\n{'[DRY RUN] ' if dry_run else ''}Migrating: {input_md.name}")
    print(f"  → Output: {output_spl}")
    print(f"  Status: {metadata['status']}")
    print(f"  Feature IDs: {metadata['feature_ids']}")
    print(f"  Code examples: {len(examples)}")
    
    if verbose:
        print(f"\n  Title: {title}")
        print(f"  Overview length: {len(overview)} chars")
        print(f"  Related specs: {len(related)}")
    
    # Write output
    if not dry_run:
        output_spl.parent.mkdir(parents=True, exist_ok=True)
        with open(output_spl, 'w', encoding='utf-8') as f:
            f.write(spl_content)
        print(f"  ✅ Created: {output_spl}")
    else:
        print(f"  [DRY RUN] Would create: {output_spl}")
        if verbose:
            print("\n--- Preview (first 50 lines) ---")
            preview_lines = spl_content.split('\n')[:50]
            print('\n'.join(preview_lines))
            print("--- End preview ---\n")
    
    return True

def migrate_all_category_a(
    base_dir: Path,
    output_dir: Path,
    dry_run: bool = False,
    verbose: bool = False
) -> Tuple[int, int]:
    """Migrate all Category A files.
    
    Returns (success_count, total_count)
    """
    success = 0
    total = len(CATEGORY_A_FILES)
    
    print(f"\n{'=' * 60}")
    print(f"Migrating {total} Category A files (Direct migrations)")
    print(f"{'=' * 60}")
    
    for md_file, spl_file, feature_ids in CATEGORY_A_FILES:
        input_path = base_dir / md_file
        output_path = output_dir / spl_file
        
        if migrate_file(input_path, output_path, dry_run, verbose):
            success += 1
    
    print(f"\n{'=' * 60}")
    print(f"Migration {'preview' if dry_run else 'complete'}: {success}/{total} successful")
    print(f"{'=' * 60}\n")
    
    return success, total

def main():
    parser = argparse.ArgumentParser(
        description='Migrate doc/spec/*.md to tests/specs/*_spec.spl',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
Examples:
  # Migrate single file
  python scripts/migrate_spec_to_spl.py doc/spec/syntax.md tests/specs/syntax_spec.spl
  
  # Dry run (preview)
  python scripts/migrate_spec_to_spl.py --dry-run doc/spec/types.md tests/specs/types_spec.spl
  
  # Migrate all Category A files
  python scripts/migrate_spec_to_spl.py --all
  
  # Migrate all with verbose output
  python scripts/migrate_spec_to_spl.py --all --verbose
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
        help='Migrate all Category A files'
    )
    
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='Preview migration without writing files'
    )
    
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Show detailed migration info'
    )
    
    args = parser.parse_args()
    
    # Validate arguments
    if args.all:
        base_dir = Path('doc/spec')
        output_dir = Path('tests/specs')
        success, total = migrate_all_category_a(
            base_dir, output_dir, args.dry_run, args.verbose
        )
        sys.exit(0 if success == total else 1)
    
    elif args.input_md and args.output_spl:
        success = migrate_file(
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
