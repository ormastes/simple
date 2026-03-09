#!/usr/bin/env python3
"""
doxygen_xml_to_markdown.py - Convert Doxygen XML output to Markdown

Usage:
    python3 doxygen_xml_to_markdown.py <xml_dir> <output_dir>

Example:
    python3 doxygen_xml_to_markdown.py build/23.Shared_Memory/src/doxygen/xml build/23.Shared_Memory/src/markdown
"""

import xml.etree.ElementTree as ET
import os
import sys
from pathlib import Path
import re

def clean_text(text):
    """Clean text from XML elements"""
    if text is None:
        return ""
    # Remove extra whitespace
    text = re.sub(r'\s+', ' ', text.strip())
    return text

def parse_param(param_elem):
    """Parse parameter element"""
    param_type = clean_text(param_elem.findtext('.//type', ''))
    param_name = clean_text(param_elem.findtext('.//declname', ''))
    return f"{param_type} {param_name}".strip()

def parse_function(member_elem, output_file):
    """Parse function/method element and write to markdown"""
    name = clean_text(member_elem.findtext('name', 'unknown'))
    definition = clean_text(member_elem.findtext('definition', ''))
    args_string = clean_text(member_elem.findtext('argsstring', ''))

    # Brief description
    brief = member_elem.find('.//briefdescription/para')
    brief_text = clean_text(brief.text if brief is not None else '')

    # Detailed description
    detailed = member_elem.find('.//detaileddescription/para')
    detailed_text = clean_text(detailed.text if detailed is not None else '')

    # Return type
    return_type = clean_text(member_elem.findtext('.//type', ''))

    output_file.write(f"### `{name}()`\n\n")

    if brief_text:
        output_file.write(f"**Brief**: {brief_text}\n\n")

    output_file.write(f"```cpp\n")
    output_file.write(f"{return_type} {name}{args_string}\n")
    output_file.write(f"```\n\n")

    if detailed_text:
        output_file.write(f"{detailed_text}\n\n")

    # Parameters
    params = member_elem.findall('.//param')
    if params:
        output_file.write("**Parameters:**\n\n")
        for param in params:
            param_str = parse_param(param)
            output_file.write(f"- `{param_str}`\n")
        output_file.write("\n")

    # Return value
    return_desc = member_elem.find('.//detaileddescription//simplesect[@kind="return"]')
    if return_desc is not None:
        return_text = clean_text(return_desc.findtext('.//para', ''))
        if return_text:
            output_file.write(f"**Returns**: {return_text}\n\n")

    output_file.write("---\n\n")

def parse_class(compound_elem, output_dir):
    """Parse class element and create markdown file"""
    class_name = clean_text(compound_elem.findtext('compoundname', 'unknown'))

    # Create output file
    output_file_path = output_dir / f"class_{class_name.replace('::', '_')}.md"

    with open(output_file_path, 'w') as f:
        f.write(f"# Class: `{class_name}`\n\n")

        # Brief description
        brief = compound_elem.find('.//briefdescription/para')
        if brief is not None:
            brief_text = clean_text(brief.text)
            if brief_text:
                f.write(f"{brief_text}\n\n")

        # Detailed description
        detailed = compound_elem.find('.//detaileddescription/para')
        if detailed is not None:
            detailed_text = clean_text(detailed.text)
            if detailed_text:
                f.write(f"## Description\n\n{detailed_text}\n\n")

        # Public methods
        public_methods = compound_elem.findall('.//sectiondef[@kind="public-func"]/memberdef[@kind="function"]')
        if public_methods:
            f.write("## Public Methods\n\n")
            for method in public_methods:
                parse_function(method, f)

        # Private methods
        private_methods = compound_elem.findall('.//sectiondef[@kind="private-func"]/memberdef[@kind="function"]')
        if private_methods:
            f.write("## Private Methods\n\n")
            for method in private_methods:
                parse_function(method, f)

def parse_file(compound_elem, output_dir):
    """Parse file element and create markdown file"""
    file_name = clean_text(compound_elem.findtext('compoundname', 'unknown'))

    # Create output file
    safe_name = file_name.replace('/', '_').replace('\\', '_')
    output_file_path = output_dir / f"file_{safe_name}.md"

    with open(output_file_path, 'w') as f:
        f.write(f"# File: `{file_name}`\n\n")

        # Brief description
        brief = compound_elem.find('.//briefdescription/para')
        if brief is not None:
            brief_text = clean_text(brief.text)
            if brief_text:
                f.write(f"{brief_text}\n\n")

        # Detailed description
        detailed = compound_elem.find('.//detaileddescription/para')
        if detailed is not None:
            detailed_text = clean_text(detailed.text)
            if detailed_text:
                f.write(f"## Description\n\n{detailed_text}\n\n")

        # Functions
        functions = compound_elem.findall('.//memberdef[@kind="function"]')
        if functions:
            f.write("## Functions\n\n")
            for func in functions:
                parse_function(func, f)

def create_index(output_dir, classes, files):
    """Create index.md file"""
    index_path = output_dir / "index.md"

    with open(index_path, 'w') as f:
        f.write("# API Documentation\n\n")
        f.write("Generated from Doxygen XML output.\n\n")

        if classes:
            f.write("## Classes\n\n")
            for class_name in sorted(classes):
                link = f"class_{class_name.replace('::', '_')}.md"
                f.write(f"- [{class_name}]({link})\n")
            f.write("\n")

        if files:
            f.write("## Files\n\n")
            for file_name in sorted(files):
                safe_name = file_name.replace('/', '_').replace('\\', '_')
                link = f"file_{safe_name}.md"
                f.write(f"- [{file_name}]({link})\n")
            f.write("\n")

def convert_xml_to_markdown(xml_dir, output_dir):
    """Convert Doxygen XML output to Markdown files"""
    xml_path = Path(xml_dir)
    output_path = Path(output_dir)

    # Create output directory
    output_path.mkdir(parents=True, exist_ok=True)

    # Find index.xml
    index_file = xml_path / "index.xml"
    if not index_file.exists():
        print(f"Error: {index_file} not found")
        return False

    print(f"Reading {index_file}...")
    tree = ET.parse(index_file)
    root = tree.getroot()

    classes = []
    files = []

    # Parse compounds
    for compound in root.findall('.//compound'):
        kind = compound.get('kind')
        refid = compound.get('refid')

        # Load the compound XML file
        compound_file = xml_path / f"{refid}.xml"
        if not compound_file.exists():
            continue

        compound_tree = ET.parse(compound_file)
        compound_root = compound_tree.getroot()
        compound_def = compound_root.find('.//compounddef')

        if compound_def is None:
            continue

        if kind in ['class', 'struct']:
            class_name = clean_text(compound_def.findtext('compoundname', ''))
            print(f"  Processing class: {class_name}")
            parse_class(compound_def, output_path)
            classes.append(class_name)

        elif kind == 'file':
            file_name = clean_text(compound_def.findtext('compoundname', ''))
            print(f"  Processing file: {file_name}")
            parse_file(compound_def, output_path)
            files.append(file_name)

    # Create index
    print("Creating index.md...")
    create_index(output_path, classes, files)

    print(f"\nMarkdown files generated in: {output_path}")
    print(f"  Classes: {len(classes)}")
    print(f"  Files: {len(files)}")

    return True

def main():
    if len(sys.argv) != 3:
        print("Usage: python3 doxygen_xml_to_markdown.py <xml_dir> <output_dir>")
        print("\nExample:")
        print("  python3 doxygen_xml_to_markdown.py \\")
        print("    build/23.Shared_Memory/src/doxygen/xml \\")
        print("    build/23.Shared_Memory/src/markdown")
        sys.exit(1)

    xml_dir = sys.argv[1]
    output_dir = sys.argv[2]

    if not os.path.isdir(xml_dir):
        print(f"Error: XML directory not found: {xml_dir}")
        print("Run 'ninja doxygen_<module>' first to generate XML output")
        sys.exit(1)

    success = convert_xml_to_markdown(xml_dir, output_dir)
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()
