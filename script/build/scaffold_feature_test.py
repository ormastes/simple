#!/usr/bin/env python3
"""
Feature Test Scaffolding Tool

Generates BDD test templates from existing feature markdown files.
The generated tests need to be manually completed with real assertions.

Usage:
    python scripts/scaffold_feature_test.py doc/old_features/infrastructure/0001_lexer.md
    python scripts/scaffold_feature_test.py doc/old_features/infrastructure/0001_lexer.md > \
        simple/std_lib/test/features/infrastructure_spec.spl
"""

import sys
import re
from pathlib import Path
from typing import Dict, List, Optional


def parse_overview_table(content: str) -> Dict[str, str]:
    """Extract metadata from the Overview table."""
    metadata = {}

    # Find overview table
    overview_section = re.search(r'## Overview\s*\n\s*\|(.*?)\n\s*\n', content, re.DOTALL)
    if not overview_section:
        return metadata

    # Parse table rows
    lines = overview_section.group(1).strip().split('\n')
    for line in lines:
        if '|' not in line or line.startswith('|---'):
            continue

        parts = [p.strip() for p in line.split('|')]
        if len(parts) >= 3:
            key = parts[1].replace('**', '').strip()
            value = parts[2].strip()
            metadata[key] = value

    return metadata


def extract_section(content: str, section_name: str) -> Optional[str]:
    """Extract content from a specific markdown section."""
    pattern = rf'## {re.escape(section_name)}\s*\n\s*(.*?)(?=\n## |\Z)'
    match = re.search(pattern, content, re.DOTALL)
    if match:
        return match.group(1).strip()
    return None


def parse_file_table(content: str) -> List[str]:
    """Extract file paths from implementation files table."""
    files = []

    # Look for Files subsection
    files_section = re.search(r'### Files\s*\n.*?\|(.*?)\n\s*\n', content, re.DOTALL)
    if not files_section:
        return files

    lines = files_section.group(1).strip().split('\n')
    for line in lines:
        if '|' not in line or line.startswith('|---'):
            continue

        parts = [p.strip() for p in line.split('|')]
        if len(parts) >= 2:
            file_path = parts[1].strip('` ')
            if file_path and not file_path.startswith('File'):
                files.append(file_path)

    return files


def parse_test_table(content: str, section_name: str) -> List[str]:
    """Extract test file paths from testing section."""
    tests = []

    # Look for specific test subsection
    pattern = rf'### {re.escape(section_name)}\s*\n.*?\|(.*?)(?=\n###|\n##|\Z)'
    test_section = re.search(pattern, content, re.DOTALL)
    if not test_section:
        return tests

    lines = test_section.group(1).strip().split('\n')
    for line in lines:
        if '|' not in line or line.startswith('|---'):
            continue

        parts = [p.strip() for p in line.split('|')]
        if len(parts) >= 2:
            test_path = parts[1].strip('` ')
            if test_path and not test_path.startswith('Test File'):
                tests.append(test_path)

    return tests


def extract_code_examples(content: str) -> List[str]:
    """Extract code examples from Examples section."""
    examples = []

    examples_section = extract_section(content, "Examples")
    if not examples_section:
        return examples

    # Find code blocks
    code_blocks = re.findall(r'```simple\n(.*?)```', examples_section, re.DOTALL)
    examples.extend(code_blocks)

    return examples


def parse_dependencies(content: str) -> tuple[List[int], List[int]]:
    """Extract depends_on and required_by feature IDs."""
    depends_on = []
    required_by = []

    deps_section = extract_section(content, "Dependencies")
    if not deps_section:
        return depends_on, required_by

    # Parse "Depends on: #1, #2, #3" format
    depends_match = re.search(r'Depends on:\s*(.+)', deps_section)
    if depends_match:
        dep_text = depends_match.group(1)
        if dep_text.lower() != 'none':
            ids = re.findall(r'#(\d+)', dep_text)
            depends_on = [int(id) for id in ids]

    # Parse "Required by: #4, #5" format
    required_match = re.search(r'Required by:\s*(.+)', deps_section)
    if required_match:
        req_text = required_match.group(1)
        if req_text.lower() != 'none':
            ids = re.findall(r'#(\d+)', req_text)
            required_by = [int(id) for id in ids]

    return depends_on, required_by


def generate_test_scaffold(md_path: Path) -> str:
    """Generate BDD test scaffold from markdown file."""
    content = md_path.read_text()

    # Parse metadata
    metadata = parse_overview_table(content)

    # Extract feature ID and name
    feature_id = metadata.get('Feature ID', '').strip('#')
    feature_name = metadata.get('Feature Name', '')
    category = metadata.get('Category', '')
    difficulty_str = metadata.get('Difficulty', '3')
    difficulty = int(difficulty_str.split()[0]) if difficulty_str else 3
    status = metadata.get('Status', '✅ Complete')
    impl_type = metadata.get('Implementation', 'R')

    # Extract sections
    description = extract_section(content, "Description") or ""
    spec_section = extract_section(content, "Specification") or ""

    # Parse spec reference
    spec_ref = ""
    spec_match = re.search(r'\[([^\]]+)\]\(\.\.\/\.\.\/([^\)]+)\)', spec_section)
    if spec_match:
        spec_ref = spec_match.group(2)

    # Extract implementation files
    impl_section = extract_section(content, "Implementation") or ""
    files = parse_file_table(impl_section)

    # Extract test files
    testing_section = extract_section(content, "Testing") or ""
    rust_tests = parse_test_table(testing_section, "Rust Tests")

    # Extract notes
    notes = extract_section(content, "Notes") or ""

    # Extract dependencies
    depends_on, required_by = parse_dependencies(content)

    # Generate BDD test scaffold
    output = []
    output.append(f"# Scaffolded from {md_path}")
    output.append("# TODO: Add real test assertions before marking complete")
    output.append("")
    output.append(f"use spec.feature_doc.feature_metadata")
    output.append("")
    output.append(f'describe "{feature_name} (#{feature_id})":')
    output.append("    feature_metadata(")
    output.append(f"        id: {feature_id},")
    output.append(f'        name: "{feature_name}",')
    output.append(f'        category: "{category}",')
    output.append(f"        difficulty: {difficulty},")
    output.append(f'        status: "{status}",')
    output.append(f'        impl_type: "{impl_type}",')
    output.append(f'        spec_ref: "{spec_ref}",')

    # Files list
    if files:
        output.append("        files: [")
        for f in files:
            output.append(f'            "{f}",')
        output.append("        ],")
    else:
        output.append("        files: [],")

    # Tests list
    if rust_tests:
        output.append("        tests: [")
        for t in rust_tests:
            output.append(f'            "{t}",')
        output.append("        ],")
    else:
        output.append("        tests: [],")

    # Description (triple-quoted string)
    if description:
        output.append('        description: """')
        output.append(description)
        output.append('        """,')
    else:
        output.append('        description: "",')

    # Dependencies
    if depends_on:
        deps_str = ", ".join(str(d) for d in depends_on)
        output.append(f"        dependencies: [{deps_str}],")
    else:
        output.append("        dependencies: [],")

    if required_by:
        reqs_str = ", ".join(str(r) for r in required_by)
        output.append(f"        required_by: [{reqs_str}],")
    else:
        output.append("        required_by: [],")

    # Notes
    if notes:
        output.append('        notes: """')
        output.append(notes)
        output.append('        """')
    else:
        output.append('        notes: ""')

    output.append("    )")
    output.append("")

    # Add test stubs
    output.append("    # TODO: Add test contexts and examples")
    output.append("    context \"Basic Functionality\":")
    output.append("        it \"works as expected\":")
    output.append("            # TODO: Import required modules")
    output.append("            # TODO: Add test setup")
    output.append("            # TODO: Write assertions")
    output.append('            skip "TODO: Add real assertion"')
    output.append("")

    return "\n".join(output)


def main():
    if len(sys.argv) < 2:
        print("Usage: python scripts/scaffold_feature_test.py <markdown_file>")
        print("")
        print("Examples:")
        print("  python scripts/scaffold_feature_test.py doc/old_features/infrastructure/0001_lexer.md")
        print("  python scripts/scaffold_feature_test.py doc/old_features/infrastructure/0001_lexer.md > output.spl")
        sys.exit(1)

    md_path = Path(sys.argv[1])

    if not md_path.exists():
        print(f"Error: File not found: {md_path}", file=sys.stderr)
        sys.exit(1)

    scaffold = generate_test_scaffold(md_path)
    print(scaffold)


if __name__ == "__main__":
    main()
