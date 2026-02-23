#!/usr/bin/env python3
"""
Second-pass fixer: stub out function bodies that contain compilation errors.
Takes the fixed .cpp file and a list of error line numbers, and replaces
broken function bodies with stub returns.
"""

import re
import sys


def count_braces(line):
    """Count net braces { - } ignoring string literals and comments."""
    count = 0
    in_string = False
    in_char = False
    in_line_comment = False
    in_block_comment = False
    escape = False
    i = 0
    while i < len(line):
        c = line[i]
        if escape:
            escape = False
            i += 1
            continue
        if c == '\\' and (in_string or in_char):
            escape = True
            i += 1
            continue
        if in_line_comment:
            i += 1
            continue
        if in_block_comment:
            if c == '*' and i + 1 < len(line) and line[i+1] == '/':
                in_block_comment = False
                i += 2
                continue
            i += 1
            continue
        if c == '/' and i + 1 < len(line):
            if line[i+1] == '/':
                in_line_comment = True
                i += 2
                continue
            if line[i+1] == '*':
                in_block_comment = True
                i += 2
                continue
        if c == '"' and not in_char:
            in_string = not in_string
            i += 1
            continue
        if c == "'" and not in_string:
            in_char = not in_char
            i += 1
            continue
        if not in_string and not in_char:
            if c == '{':
                count += 1
            elif c == '}':
                count -= 1
        i += 1
    return count


def find_function_boundaries(lines):
    """Find all top-level function definitions and their boundaries.
    Returns list of (start_line, end_line, return_type, func_name)."""
    functions = []
    i = 0
    while i < len(lines):
        line = lines[i]
        # Match top-level function definition
        if not line.startswith(' ') and not line.startswith('\t') and not line.startswith('//'):
            m = re.match(
                r'^((?:static\s+)?(?:inline\s+)?(?:const\s+)?'
                r'(?:int64_t|void|const char\*|bool|double|int32_t|SplArray\*|SplDict\*|SplValue|'
                r'MirType|MirOperand|MirBody|MirBlock|LocalId|MirInst|BlockId|'
                r'HirType|HirExpr|Span|SymbolId|SymbolTable|Token|'
                r'MirFunction|MirPlace|MirRvalue|MirTerminator|'
                r'ScopeId|TypeId|ImplBlockEx|TraitRef|TraitDefEx|'
                r'AssocTypeDef|AssocTypeImpl|AssocTypeProjection|'
                r'ArchRulesConfig|VolatileAttr|DimExpr|LayerType|SdnValue|'
                r'CompilerConfig|Logger|CompileContext|ErrorContext|CompileError|'
                r'CompileResult|Backend|Module|LlvmCompileResult|NativeCompileResult|'
                r'Option_\w+|std::vector<\w+>|\w+\*|\w+))'
                r'\s+(\w+)\(.*\)\s*\{?\s*$', line)
            if m and line.rstrip().endswith('{'):
                ret_type = m.group(1).strip()
                func_name = m.group(2)
                # Find end of function
                depth = count_braces(line)
                j = i + 1
                while j < len(lines) and depth > 0:
                    depth += count_braces(lines[j])
                    j += 1
                functions.append((i, j - 1, ret_type, func_name))
                i = j
                continue
        i += 1
    return functions


def stub_return(ret_type):
    """Generate a stub return statement for the given return type."""
    ret_type = ret_type.strip()
    # Remove leading qualifiers
    clean = re.sub(r'^(static|inline|const)\s+', '', ret_type).strip()
    clean = re.sub(r'^(static|inline|const)\s+', '', clean).strip()

    if clean == 'void':
        return '    return;\n'
    elif clean == 'bool':
        return '    return false;\n'
    elif clean == 'double':
        return '    return 0.0;\n'
    elif clean in ('const char*',):
        return '    return "";\n'
    elif clean in ('int64_t', 'int32_t'):
        return '    return 0;\n'
    elif clean == 'SplArray*':
        return '    return spl_array_new();\n'
    elif clean == 'SplValue':
        return '    return spl_nil();\n'
    elif clean.endswith('*'):
        # Any pointer type - return NULL
        return '    return NULL;\n'
    elif clean.startswith('std::vector'):
        return '    return {};\n'
    elif clean[0].isupper():
        # Struct type - return default-initialized
        return f'    return {clean}{{}};\n'
    else:
        return '    return 0;\n'


def main():
    if len(sys.argv) != 4:
        print("Usage: stub_broken.py <input.cpp> <error_lines.txt> <output.cpp>")
        sys.exit(1)

    input_path = sys.argv[1]
    error_lines_path = sys.argv[2]
    output_path = sys.argv[3]

    with open(input_path, 'r', encoding='utf-8', errors='replace') as f:
        lines = f.readlines()

    # Read error line numbers (1-indexed)
    with open(error_lines_path, 'r') as f:
        error_lines = set(int(line.strip()) for line in f if line.strip())

    # Find function boundaries
    functions = find_function_boundaries(lines)
    print(f"Found {len(functions)} functions")

    # Find functions that contain errors
    broken_funcs = set()
    for start, end, ret_type, name in functions:
        for line_no in range(start + 1, end + 1):  # +1 for 1-indexed
            if (line_no + 1) in error_lines:  # error_lines are 1-indexed
                broken_funcs.add((start, end, ret_type, name))
                break

    print(f"Found {len(broken_funcs)} broken functions to stub out")

    # Build set of lines to skip
    skip_ranges = set()
    for start, end, _, _ in broken_funcs:
        for i in range(start + 1, end + 1):  # Keep the function signature, skip body + closing brace
            skip_ranges.add(i)

    # Rebuild file
    result = []
    stubbed_names = []
    i = 0
    while i < len(lines):
        if i in skip_ranges:
            # Check if this is the first line of a body being skipped
            is_first_skip = (i - 1) not in skip_ranges
            if is_first_skip:
                # Find the function info
                for start, end, ret_type, name in broken_funcs:
                    if start + 1 == i:
                        result.append(f'    /* STUBBED: {name} */\n')
                        result.append(stub_return(ret_type))
                        result.append('}\n')
                        stubbed_names.append(name)
                        break
            i += 1
            continue
        result.append(lines[i])
        i += 1

    print(f"Stubbed functions: {len(stubbed_names)}")
    if stubbed_names[:10]:
        print(f"  First 10: {', '.join(stubbed_names[:10])}")

    with open(output_path, 'w', encoding='utf-8') as f:
        f.writelines(result)

    print(f"Output: {len(result)} lines (was {len(lines)})")


if __name__ == '__main__':
    main()
