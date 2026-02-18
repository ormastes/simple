#!/usr/bin/env python3
"""
Simple Language Desugarer
Transforms Full Simple code to Core Simple compatible code.

Usage:
    python3 desugarer.py input.spl output.spl
    python3 desugarer.py --dir src/compiler --output-dir src/compiler
"""

import re
import sys
import os
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict, Optional, Tuple

@dataclass
class StructField:
    name: str
    type_: str
    is_optional: bool = False

@dataclass
class Method:
    name: str
    is_static: bool
    params: List[Tuple[str, str]]  # (name, type)
    return_type: str
    body: str

@dataclass
class ImplBlock:
    type_name: str
    methods: List[Method]

class SimpleDesugarer:
    """Main desugarer that applies all transformation passes."""
    
    def __init__(self, source: str):
        self.source = source
        self.lines = source.split('\n')
        self.output_lines = []
        
    def desugar(self) -> str:
        """Apply all desugaring transformations."""
        print("Pass 1: Extracting impl blocks...")
        source = self.pass1_extract_impl_blocks()
        
        print("Pass 2: Desugaring Option types...")
        source = self.pass2_desugar_options(source)
        
        print("Pass 3: Converting pattern matching...")
        source = self.pass3_desugar_patterns(source)
        
        print("Pass 4: Replacing operators...")
        source = self.pass4_desugar_operators(source)
        
        print("Pass 5: Converting method calls...")
        source = self.pass5_convert_method_calls(source)
        
        return source
    
    # =========================================================================
    # Pass 1: Extract impl Blocks
    # =========================================================================
    
    def pass1_extract_impl_blocks(self) -> str:
        """Extract impl blocks and convert methods to module functions."""
        result = []
        i = 0
        lines = self.source.split('\n')
        
        while i < len(lines):
            line = lines[i]
            
            # Check for impl block
            impl_match = re.match(r'^impl\s+(\w+):', line)
            if impl_match:
                type_name = impl_match.group(1)
                print(f"  Found impl block for: {type_name}")
                
                # Extract the entire impl block
                impl_block, end_idx = self.extract_impl_block(lines, i)
                
                # Convert methods to functions
                functions = self.convert_impl_to_functions(type_name, impl_block)
                result.extend(functions)
                
                i = end_idx
            else:
                result.append(line)
                i += 1
        
        return '\n'.join(result)
    
    def extract_impl_block(self, lines: List[str], start: int) -> Tuple[List[str], int]:
        """Extract impl block content."""
        block = [lines[start]]
        indent_level = 0
        i = start + 1
        
        # Find the indented content
        while i < len(lines):
            line = lines[i]
            
            # Count leading spaces
            stripped = line.lstrip()
            if not stripped:
                block.append(line)
                i += 1
                continue
            
            spaces = len(line) - len(stripped)
            
            # First non-empty line sets the indent
            if indent_level == 0 and stripped:
                indent_level = spaces
            
            # If we're back to original indent or less, impl block ended
            if stripped and spaces <= len(lines[start]) - len(lines[start].lstrip()):
                break
            
            block.append(line)
            i += 1
        
        return block, i
    
    def convert_impl_to_functions(self, type_name: str, impl_block: List[str]) -> List[str]:
        """Convert impl block methods to module-level functions."""
        functions = []
        functions.append(f"\n# ============================================================================")
        functions.append(f"# {type_name} Methods (was: impl {type_name}:)")
        functions.append(f"# ============================================================================\n")
        
        i = 1  # Skip the "impl Type:" line
        while i < len(impl_block):
            line = impl_block[i]
            
            # Look for method definitions
            # Pattern: "    static fn name(...) -> ReturnType:"
            # Pattern: "    me method(...) -> ReturnType:"
            static_match = re.match(r'^(\s+)static\s+fn\s+(\w+)\((.*?)\)\s*->\s*(\w+):', line)
            me_match = re.match(r'^(\s+)me\s+(\w+)\((.*?)\)\s*->\s*(\w+):', line)
            
            if static_match:
                indent, method_name, params, return_type = static_match.groups()
                func_name = f"{type_name.lower()}_{method_name}"
                
                # Extract method body
                body, end_idx = self.extract_method_body(impl_block, i)
                
                # Generate function
                functions.append(f"fn {func_name}({params}) -> {return_type}:")
                functions.extend(body)
                functions.append("")
                
                i = end_idx
                
            elif me_match:
                indent, method_name, params, return_type = me_match.groups()
                func_name = f"{type_name.lower()}_{method_name}"
                
                # Add self parameter
                if params:
                    params = f"self: {type_name}, {params}"
                else:
                    params = f"self: {type_name}"
                
                # Extract method body
                body, end_idx = self.extract_method_body(impl_block, i)
                
                # Generate function
                functions.append(f"fn {func_name}({params}) -> {return_type}:")
                functions.extend(body)
                functions.append("")
                
                i = end_idx
            else:
                i += 1
        
        return functions
    
    def extract_method_body(self, lines: List[str], start: int) -> Tuple[List[str], int]:
        """Extract method body (indented content after method signature)."""
        body = []
        base_indent = len(lines[start]) - len(lines[start].lstrip())
        i = start + 1
        
        while i < len(lines):
            line = lines[i]
            stripped = line.lstrip()
            
            if not stripped:
                body.append(line)
                i += 1
                continue
            
            indent = len(line) - len(stripped)
            
            # If indent is back to method level or less, we're done
            if indent <= base_indent:
                break
            
            body.append(line)
            i += 1
        
        return body, i
    
    # =========================================================================
    # Pass 2: Desugar Option Types
    # =========================================================================
    
    def pass2_desugar_options(self, source: str) -> str:
        """Convert Option<T> types to has_field + field_value pattern."""
        result = []
        lines = source.split('\n')
        i = 0
        
        while i < len(lines):
            line = lines[i]
            
            # Check if we're in a struct definition
            struct_match = re.match(r'^struct\s+(\w+):', line)
            if struct_match:
                struct_name = struct_match.group(1)
                print(f"  Processing struct: {struct_name}")
                
                # Extract struct and desugar its Option fields
                struct_lines, end_idx = self.extract_struct(lines, i)
                desugared = self.desugar_struct_options(struct_lines)
                result.extend(desugared)
                
                i = end_idx
            else:
                result.append(line)
                i += 1
        
        return '\n'.join(result)
    
    def extract_struct(self, lines: List[str], start: int) -> Tuple[List[str], int]:
        """Extract struct definition."""
        struct_lines = [lines[start]]
        base_indent = len(lines[start]) - len(lines[start].lstrip())
        i = start + 1
        
        while i < len(lines):
            line = lines[i]
            stripped = line.lstrip()
            
            if not stripped:
                struct_lines.append(line)
                i += 1
                continue
            
            indent = len(line) - len(stripped)
            
            # If we're back to struct indent or less, done
            if indent <= base_indent:
                break
            
            struct_lines.append(line)
            i += 1
        
        return struct_lines, i
    
    def desugar_struct_options(self, struct_lines: List[str]) -> List[str]:
        """Desugar Option types in struct fields."""
        result = []
        result.append(struct_lines[0])  # struct Name:
        
        for line in struct_lines[1:]:
            # Look for: "    field: Type?"
            option_match = re.match(r'^(\s+)(\w+):\s+(\w+)\?(.*)$', line)
            if option_match:
                indent, field_name, type_name, rest = option_match.groups()
                print(f"    Desugaring Option field: {field_name}: {type_name}?")
                
                # Convert to has_field + field_value
                result.append(f"{indent}# DESUGARED: {field_name}: {type_name}?")
                result.append(f"{indent}has_{field_name}: bool")
                result.append(f"{indent}{field_name}_value: {type_name}")
            else:
                result.append(line)
        
        return result
    
    # =========================================================================
    # Pass 3: Desugar Pattern Matching
    # =========================================================================
    
    def pass3_desugar_patterns(self, source: str) -> str:
        """Convert pattern matching to if-else chains."""
        # This is complex - for now, add a placeholder
        # Real implementation would parse match expressions and convert them
        
        # Simple replacement for common patterns
        result = source
        
        # Replace .? operator (Option check)
        result = re.sub(r'(\w+)\.?\?:', r'has_\1:', result)
        result = re.sub(r'if not self\.(\w+)\.?\?:', r'if not self.has_\1:', result)
        result = re.sub(r'if (\w+)\.?\?:', r'if has_\1:', result)
        
        # Replace .unwrap() calls
        result = re.sub(r'(\w+)\.unwrap\(\)', r'\1_value', result)
        result = re.sub(r'self\.(\w+)\.unwrap\(\)', r'self.\1_value', result)
        
        # Replace Some(...) in field initialization
        result = re.sub(r'Some\(([^)]+)\)', r'has_field = true, field_value = \1', result)
        
        # Replace nil with false for Option fields in struct initialization
        # This needs to be done carefully to only affect Option fields
        lines = result.split('\n')
        in_struct_init = False
        result_lines = []
        
        for line in lines:
            # Detect struct initialization
            if re.match(r'\s+\w+\(', line):
                in_struct_init = True
            elif in_struct_init and re.match(r'\s+\)', line):
                in_struct_init = False
            
            # Replace nil for fields that look like Option fields (ending with _token, _registry, _kind, etc.)
            if in_struct_init:
                # pending_token: nil → has_pending_token: false, pending_token_value: Token.default()
                line = re.sub(r'(\w+):\s*nil,?\s*#.*$', 
                             lambda m: f"# DESUGARED: {m.group(1)}: nil\n            has_{m.group(1)}: false,\n            {m.group(1)}_value: nil,  # TODO: provide default", 
                             line)
                # Simple case without comment
                line = re.sub(r'(\w+):\s*nil,?\s*$', 
                             lambda m: f"has_{m.group(1)}: false,  # DESUGARED: {m.group(1)}: nil", 
                             line)
            
            result_lines.append(line)
        
        return '\n'.join(result_lines)
    
    # =========================================================================
    # Pass 4: Desugar Operators
    # =========================================================================
    
    def pass4_desugar_operators(self, source: str) -> str:
        """Replace advanced operators like ?. and ??"""
        result = source
        
        # This is simplified - real implementation would parse expressions
        # and generate proper if-else blocks
        
        return result
    
    # =========================================================================
    # Pass 5: Convert Method Calls
    # =========================================================================
    
    def pass5_convert_method_calls(self, source: str) -> str:
        """Convert obj.method() to module_method(obj)."""
        result = []
        
        for line in source.split('\n'):
            # Skip comments and empty lines
            if line.strip().startswith('#') or not line.strip():
                result.append(line)
                continue
            
            # Look for method calls: obj.method(args)
            # This is a simplified version - real parser would be more robust
            converted = line
            
            # Pattern: identifier.method(args)
            # But avoid struct field access: obj.field
            method_call_pattern = r'(\w+)\.(\w+)\(([^)]*)\)'
            
            def replace_method_call(match):
                obj, method, args = match.groups()
                # Try to determine type from obj name
                if obj == 'self':
                    # We don't know the type here, so keep it as is for now
                    return match.group(0)
                elif obj[0].isupper():
                    # Looks like a type name (static method)
                    return f"{obj.lower()}_{method}({args})"
                else:
                    # Instance method call
                    if args:
                        return f"{obj}_{method}({obj}, {args})"
                    else:
                        return f"{obj}_{method}({obj})"
            
            # Don't convert if it's in a string or comment
            if '"' not in line and "'" not in line:
                converted = re.sub(method_call_pattern, replace_method_call, line)
            
            result.append(converted)
        
        return '\n'.join(result)


def main():
    if len(sys.argv) < 3:
        print("Usage: python3 desugarer.py input.spl output.spl")
        print("   or: python3 desugarer.py --dir src/compiler --output-dir src/compiler")
        sys.exit(1)
    
    if sys.argv[1] == '--dir':
        # Batch mode
        input_dir = Path(sys.argv[2])
        output_dir = Path(sys.argv[4])
        output_dir.mkdir(exist_ok=True, parents=True)
        
        # Process all .spl files recursively
        for input_file in input_dir.rglob('*.spl'):
            print(f"\n{'='*70}")
            print(f"Processing: {input_file}")
            print('='*70)
            
            try:
                with open(input_file) as f:
                    source = f.read()
                
                desugarer = SimpleDesugarer(source)
                output = desugarer.desugar()
                
                # Preserve directory structure
                rel_path = input_file.relative_to(input_dir)
                output_file = output_dir / rel_path
                output_file.parent.mkdir(exist_ok=True, parents=True)
                
                with open(output_file, 'w') as f:
                    f.write(output)
                
                print(f"✓ Written to: {output_file}")
            except Exception as e:
                print(f"✗ Error processing {input_file}: {e}")
    else:
        # Single file mode
        input_file = sys.argv[1]
        output_file = sys.argv[2]
        
        print(f"Reading: {input_file}")
        with open(input_file) as f:
            source = f.read()
        
        print("Desugaring...")
        desugarer = SimpleDesugarer(source)
        output = desugarer.desugar()
        
        print(f"Writing: {output_file}")
        with open(output_file, 'w') as f:
            f.write(output)
        
        print("✓ Done!")

if __name__ == '__main__':
    main()
