#!/usr/bin/env python3
"""
Spec Generator - Generate markdown documentation from _spec.spl files.

Enhanced with:
- Symbol linking (hybrid approach)
- Test name to symbol conversion
- Smart path resolution
- Root TOC generation
- Category organization

Reads executable specification files (tests/specs/*_spec.spl) and generates
formatted markdown documentation suitable for doc/spec/generated/

Usage:
    python scripts/spec_gen.py --input tests/specs/syntax_spec.spl
    python scripts/spec_gen.py --all
    python scripts/spec_gen.py --all --output doc/spec/generated/
    python scripts/spec_gen.py --index  # Generate root TOC
"""

import re
import sys
import argparse
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional, Set
from collections import defaultdict

class SpecFile:
    """Represents a parsed _spec.spl file."""
    def __init__(self, path: Path):
        self.path = path
        self.header_docstring = ""
        self.metadata = {}
        self.test_cases = []
        
class TestCase:
    """Represents a test case from a spec file."""
    def __init__(self, name: str, section: str, line_num: int):
        self.name = name
        self.section = section
        self.line_number = line_num
        self.docstring = ""
        self.code = ""
        self.symbols = []  # Linked symbols (hybrid detection)
        self.related_tests = []  # Related test names

# Category definitions for TOC organization
CATEGORIES = {
    "Core Language": ["syntax", "functions", "traits", "memory", "modules"],
    "Type System": ["types", "type_inference"],
    "Async/Concurrency": ["async_default", "suspension_operator", "concurrency"],
    "Advanced Features": ["capability_effects", "metaprogramming", "macro"],
    "Data Structures": ["data_structures"],
    "Testing & Quality": ["sandboxing"],
}

def categorize_spec(spec_name: str) -> str:
    """Determine category for a spec file."""
    for category, specs in CATEGORIES.items():
        if any(s in spec_name for s in specs):
            return category
    return "Miscellaneous"

def convert_test_name_to_symbols(test_name: str) -> List[str]:
    """Convert test name to potential symbol names.
    
    Examples:
        type_inference_basic -> ["type_inference", "TypeInference"]
        apply_subst_generic -> ["apply_subst", "ApplySubst"]
    """
    # Remove common prefixes
    name = test_name.replace("test_", "").replace("_test", "")
    
    # Split by underscore
    parts = name.split("_")
    
    # Filter out numbers and common suffixes
    filtered = [p for p in parts if not p.isdigit() and p not in ("basic", "advanced", "simple", "complex")]
    
    if not filtered:
        return []
    
    # Generate variations
    symbols = []
    
    # Snake case (function name): type_inference
    snake_case = "_".join(filtered)
    symbols.append(snake_case)
    
    # Pascal case (type name): TypeInference
    pascal_case = "".join(p.capitalize() for p in filtered)
    symbols.append(pascal_case)
    
    # Also try each individual part
    for part in filtered:
        if len(part) > 2:  # Skip very short parts
            symbols.append(part)
            symbols.append(part.capitalize())
    
    return list(set(symbols))  # Remove duplicates

def extract_symbols_from_docstring(docstring: str) -> Tuple[List[str], List[str]]:
    """Extract explicit symbol links and related tests from docstring.
    
    Returns: (symbols, related_tests)
    """
    symbols = []
    related = []
    
    # Extract **Links:** or **Symbols:**
    link_patterns = [
        r'\*\*Links?:\*\*\s*(.+)',
        r'\*\*Symbols?:\*\*\s*(.+)',
    ]
    
    for pattern in link_patterns:
        matches = re.findall(pattern, docstring, re.MULTILINE)
        for match in matches:
            # Split by comma
            parts = [p.strip() for p in match.split(',')]
            symbols.extend(parts)
    
    # Extract **Related:**
    related_match = re.search(r'\*\*Related:\*\*\s*(.+)', docstring)
    if related_match:
        parts = [p.strip() for p in related_match.group(1).split(',')]
        related.extend(parts)
    
    return symbols, related

def scan_code_for_symbols(code: str) -> Set[str]:
    """Scan code for potential symbol references.
    
    Looks for:
    - Function calls: symbol()
    - Method calls: object.method()
    - Type usage: Type::variant
    - Constructors: Type::new()
    """
    symbols = set()
    
    # Pattern for qualified names: Type::method, module::Type
    qualified = re.findall(r'([A-Z][a-zA-Z0-9_]*)::[a-z_][a-zA-Z0-9_]*', code)
    symbols.update(qualified)
    
    # Pattern for function calls: function_name(
    functions = re.findall(r'\b([a-z_][a-z0-9_]*)\s*\(', code)
    symbols.update(functions)
    
    # Pattern for method calls: .method_name(
    methods = re.findall(r'\.([a-z_][a-z0-9_]*)\s*\(', code)
    symbols.update(methods)
    
    # Pattern for type names (capitalized)
    types = re.findall(r'\b([A-Z][a-zA-Z0-9]*)\b', code)
    symbols.update(types)
    
    # Filter out common keywords and very short names
    filtered = {s for s in symbols if len(s) > 2 and s not in ('Int', 'Str', 'Bool', 'None', 'Some')}
    
    return filtered

def extract_symbols_hybrid(test_case: TestCase, imports: Set[str]) -> List[str]:
    """Extract symbols using hybrid approach:
    1. Explicit docstring metadata
    2. Test name conversion
    3. Code scanning
    """
    all_symbols = []
    
    # Method 1: Explicit docstring links
    doc_symbols, related = extract_symbols_from_docstring(test_case.docstring)
    all_symbols.extend(doc_symbols)
    test_case.related_tests = related
    
    # Method 2: Test name conversion
    name_symbols = convert_test_name_to_symbols(test_case.name)
    all_symbols.extend(name_symbols)
    
    # Method 3: Code scanning
    code_symbols = scan_code_for_symbols(test_case.code)
    all_symbols.extend(code_symbols)
    
    # Deduplicate and filter
    unique_symbols = []
    seen = set()
    for sym in all_symbols:
        if sym and sym not in seen:
            seen.add(sym)
            unique_symbols.append(sym)
    
    return unique_symbols


def parse_spec_file(filepath: Path) -> SpecFile:
    """Parse a _spec.spl file and extract documentation."""
    spec = SpecFile(filepath)
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Extract header docstring (first """ ... """)
    header_match = re.search(r'"""(.*?)"""', content, re.DOTALL)
    if header_match:
        spec.header_docstring = header_match.group(1).strip()
        spec.metadata = parse_metadata(spec.header_docstring)
    
    # Extract test cases
    spec.test_cases = extract_test_cases(content)
    
    return spec

def parse_metadata(docstring: str) -> Dict[str, str]:
    """Parse metadata from docstring header."""
    metadata = {}
    
    # Extract lines like **Key:** value
    for match in re.finditer(r'\*\*(.+?):\*\*\s*(.+)', docstring):
        key = match.group(1).strip()
        value = match.group(2).strip()
        metadata[key] = value
    
    return metadata

def extract_test_cases(content: str) -> List[TestCase]:
    """Extract all test cases from the file."""
    cases = []
    lines = content.split('\n')
    
    i = 0
    while i < len(lines):
        line = lines[i]
        
        # Look for ## Test: markers
        if line.strip().startswith('## Test:'):
            section = line.strip()[8:].strip()
            
            # Extract line number info if present
            line_num = 0
            if '(Line' in section:
                match = re.search(r'\(Line ~?(\d+)\)', section)
                if match:
                    line_num = int(match.group(1))
                    section = re.sub(r'\s*\(Line ~?\d+\)', '', section)
            
            # Look ahead for docstring and test code
            j = i + 1
            test_docstring = ""
            test_name = ""
            test_code = []
            
            # Skip blank lines, extract docstring
            while j < len(lines):
                stripped = lines[j].strip()
                
                if stripped.startswith('"""'):
                    # Extract multi-line docstring
                    doc_lines = []
                    j += 1
                    while j < len(lines) and not lines[j].strip().startswith('"""'):
                        doc_lines.append(lines[j])
                        j += 1
                    test_docstring = '\n'.join(doc_lines).strip()
                    j += 1  # Skip closing """
                    continue
                
                # Look for test or function definition
                if stripped.startswith('test "') or stripped.startswith('fn '):
                    test_name = extract_test_name(lines[j])
                    
                    # Extract code until next ## Test: or end
                    code_start = j
                    j += 1
                    while j < len(lines) and not lines[j].strip().startswith('## Test:'):
                        j += 1
                    
                    test_code = lines[code_start:j]
                    break
                
                if stripped == "":
                    j += 1
                else:
                    # Unrecognized content, move on
                    j += 1
                    if j - i > 20:  # Don't search too far
                        break
            
            # Create test case if we found code
            if test_name and test_code:
                tc = TestCase(test_name, section, line_num)
                tc.docstring = test_docstring
                tc.code = '\n'.join(test_code).strip()
                cases.append(tc)
                i = j - 1
        
        i += 1
    
    return cases

def extract_test_name(line: str) -> str:
    """Extract test name from test or function definition."""
    # test "name":
    match = re.search(r'test\s+"([^"]+)"', line)
    if match:
        return match.group(1)
    
    # fn name():
    match = re.search(r'fn\s+(\w+)\s*\(', line)
    if match:
        return match.group(1)
    
    return "unnamed_test"

def generate_markdown(spec: SpecFile, output_path: Optional[Path] = None) -> str:
    """Generate markdown documentation from parsed spec."""
    
    # Build markdown content
    md_lines = []
    
    # Extract title from header
    title_match = re.search(r'^#\s+(.+)', spec.header_docstring, re.MULTILINE)
    title = title_match.group(1) if title_match else spec.path.stem.replace('_spec', ' ').title()
    
    # Header
    md_lines.append(f"# {title}")
    md_lines.append("")
    md_lines.append("> **⚠️ GENERATED FILE** - Do not edit directly!")
    try:
        rel_path = spec.path.relative_to(Path.cwd())
    except ValueError:
        rel_path = spec.path
    md_lines.append(f"> **Source:** `{rel_path}`")
    md_lines.append(f"> **Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    md_lines.append(">")
    md_lines.append("> To update this file, edit the source _spec.spl file and run:")
    md_lines.append("> ```bash")
    md_lines.append(f"> python scripts/spec_gen.py --input {spec.path}")
    md_lines.append("> ```")
    md_lines.append("")
    
    # Metadata
    if spec.metadata:
        for key, value in spec.metadata.items():
            if key not in ['Migrated From', 'Source', 'Type']:
                md_lines.append(f"**{key}:** {value}")
        md_lines.append("")
    
    # Overview from header docstring
    # Extract content after metadata
    overview_match = re.search(r'##\s+Overview\s*\n+(.*?)(?=\n##|\Z)', spec.header_docstring, re.DOTALL)
    if overview_match:
        md_lines.append("## Overview")
        md_lines.append("")
        md_lines.append(overview_match.group(1).strip())
        md_lines.append("")
    
    # Related specs from header
    related_match = re.search(r'##\s+Related Specifications\s*\n+(.*?)(?=\n##|\Z)', spec.header_docstring, re.DOTALL)
    if related_match:
        md_lines.append("## Related Specifications")
        md_lines.append("")
        md_lines.append(related_match.group(1).strip())
        md_lines.append("")
    
    md_lines.append("---")
    md_lines.append("")
    
    # Test cases summary
    if spec.test_cases:
        md_lines.append(f"## Test Cases ({len(spec.test_cases)} total)")
        md_lines.append("")
        md_lines.append("| Test | Section | Description |")
        md_lines.append("|------|---------|-------------|")
        
        for i, tc in enumerate(spec.test_cases, 1):
            desc = tc.docstring.split('\n')[0][:60] + "..." if tc.docstring and len(tc.docstring) > 60 else (tc.docstring or "")
            desc = desc.replace('|', '\\|').replace('\n', ' ')
            md_lines.append(f"| [{tc.name}](#test-{i}) | {tc.section} | {desc} |")
        
        md_lines.append("")
        md_lines.append("---")
        md_lines.append("")
    
    # Detailed test cases
    for i, tc in enumerate(spec.test_cases, 1):
        md_lines.append(f"### Test {i}: {tc.section}")
        md_lines.append("")
        
        if tc.line_number:
            md_lines.append(f"*Source line: ~{tc.line_number}*")
            md_lines.append("")
        
        md_lines.append(f"**Test name:** `{tc.name}`")
        md_lines.append("")
        
        if tc.docstring:
            md_lines.append("**Description:**")
            md_lines.append("")
            md_lines.append(tc.docstring)
            md_lines.append("")
        
        md_lines.append("**Code:**")
        md_lines.append("")
        md_lines.append("```simple")
        md_lines.append(tc.code)
        md_lines.append("```")
        md_lines.append("")
    
    # Footer
    md_lines.append("---")
    md_lines.append("")
    md_lines.append("*This file was auto-generated from the executable specification.*")
    md_lines.append(f"*Source: `{spec.path}`*")
    md_lines.append("")
    
    markdown = '\n'.join(md_lines)
    
    # Write to file if output path specified
    if output_path:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(markdown)
        print(f"✅ Generated: {output_path}")
    
    return markdown

def generate_all(specs_dir: Path, output_dir: Path) -> Tuple[int, int]:
    """Generate markdown for all _spec.spl files."""
    
    spec_files = list(specs_dir.glob('*_spec.spl'))
    success = 0
    total = len(spec_files)
    
    print(f"\n{'=' * 60}")
    print(f"Generating markdown for {total} spec files")
    print(f"{'=' * 60}\n")
    
    for spec_path in sorted(spec_files):
        try:
            spec = parse_spec_file(spec_path)
            
            # Output filename
            output_name = spec_path.stem.replace('_spec', '') + '.md'
            output_path = output_dir / output_name
            
            generate_markdown(spec, output_path)
            success += 1
        except Exception as e:
            print(f"❌ Error processing {spec_path.name}: {e}")
    
    print(f"\n{'=' * 60}")
    print(f"Generation complete: {success}/{total} successful")
    print(f"{'=' * 60}\n")
    
    return success, total

def main():
    parser = argparse.ArgumentParser(
        description='Generate markdown documentation from _spec.spl files',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
Examples:
  # Generate from single file
  python scripts/spec_gen.py --input tests/specs/syntax_spec.spl
  
  # Specify output file
  python scripts/spec_gen.py --input tests/specs/types_spec.spl --output doc/spec/generated/types.md
  
  # Generate all specs
  python scripts/spec_gen.py --all
  
  # Generate all to specific directory
  python scripts/spec_gen.py --all --output doc/spec/generated/
'''
    )
    
    parser.add_argument(
        '--input',
        type=Path,
        help='Input _spec.spl file'
    )
    
    parser.add_argument(
        '--output',
        type=Path,
        help='Output markdown file or directory'
    )
    
    parser.add_argument(
        '--all',
        action='store_true',
        help='Generate markdown for all specs in tests/specs/'
    )
    
    args = parser.parse_args()
    
    if args.all:
        specs_dir = Path('tests/specs')
        output_dir = args.output if args.output else Path('doc/spec/generated')
        success, total = generate_all(specs_dir, output_dir)
        sys.exit(0 if success == total else 1)
    
    elif args.input:
        spec = parse_spec_file(args.input)
        
        # Determine output path
        if args.output:
            output_path = args.output
        else:
            output_name = args.input.stem.replace('_spec', '') + '.md'
            output_path = Path('doc/spec/generated') / output_name
        
        generate_markdown(spec, output_path)
        sys.exit(0)
    
    else:
        parser.print_help()
        sys.exit(1)

if __name__ == '__main__':
    main()
