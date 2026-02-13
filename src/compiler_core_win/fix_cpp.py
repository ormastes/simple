#!/usr/bin/env python3
"""
Post-process the generated compiler_core1.cpp to fix compilation issues.
"""

import re
import sys

# C++ reserved words that appear as struct field names
CPP_RESERVED = {
    'default': 'default_val',
    'mutable': 'is_mutable',
    'register': 'register_val',
    'volatile': 'is_volatile',
    'operator': 'operator_val',
    # 'template' handled specially in Phase 0 to avoid breaking template<T>
    'class': 'class_val',
    'namespace': 'namespace_val',
    'new': 'new_val',
    'delete': 'delete_val',
    'this': 'this_val',
    'throw': 'throw_val',
    'try': 'try_val',
    'catch': 'catch_val',
    'virtual': 'virtual_val',
    'friend': 'friend_val',
    'private': 'private_val',
    'protected': 'protected_val',
    'public': 'public_val',
    'export': 'export_val',
    'typeid': 'typeid_val',
    'explicit': 'is_explicit',
}

CPP_MACROS = {
    'stdout': 'stdout_str',
    'stderr': 'stderr_str',
    'stdin': 'stdin_str',
}

# Regex for matching top-level function definitions
FUNC_DEF_RE = re.compile(
    r'^(?:static\s+)?(?:inline\s+)?'
    r'(?:const\s+)?'
    r'(?:int64_t|void|const char\*|bool|double|int32_t|SplArray\*|SplDict\*|SplValue|'
    r'MirType|MirOperand|MirBody|MirBlock|LocalId|MirInst|BlockId|'
    r'HirType|HirExpr|Span|SymbolId|SymbolTable|Token|'
    r'MirFunction|MirPlace|MirRvalue|MirTerminator|'
    r'ScopeId|TypeId|ImplBlockEx|TraitRef|TraitDefEx|'
    r'AssocTypeDef|AssocTypeImpl|AssocTypeProjection|'
    r'ArchRulesConfig|VolatileAttr|DimExpr|LayerType|SdnValue|'
    r'CompilerConfig|Logger|CompileContext|ErrorContext|CompileError|'
    r'CompileResult|Backend|Module|LlvmCompileResult|NativeCompileResult|'
    r'Option_\w+|'
    r'std::vector<\w+>|'
    r'\w+\*|'
    r'\w+)'
    r'\s+(\w+)\('
)

# Regex for matching forward declarations
FWD_DECL_RE = re.compile(
    r'^(?:int64_t|void|const char\*|bool|double|int32_t|SplArray\*|SplValue|'
    r'MirType|MirOperand|MirBody|MirBlock|LocalId|MirInst|BlockId|'
    r'HirType|HirExpr|Span|SymbolId|SymbolTable|Token|'
    r'MirFunction|MirPlace|MirRvalue|MirTerminator|'
    r'ScopeId|TypeId|ArchRulesConfig|VolatileAttr|DimExpr|LayerType|SdnValue|'
    r'CompilerConfig|Logger|CompileContext|ErrorContext|CompileError|'
    r'CompileResult|Backend|Module|LlvmCompileResult|NativeCompileResult|'
    r'Option_\w+|'
    r'std::vector<\w+>|'
    r'\w+)'
    r'\s+\w+\([^)]*\)\s*;'
)


def count_braces(line):
    """Count net braces { - } in a line, ignoring braces inside string literals and comments."""
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


def extract_struct_body(lines, start_idx):
    """Extract a struct definition from start_idx. Returns (body_lines, end_idx)."""
    body = [lines[start_idx]]
    depth = lines[start_idx].count('{') - lines[start_idx].count('}')
    i = start_idx + 1
    while i < len(lines) and depth > 0:
        body.append(lines[i])
        depth += lines[i].count('{') - lines[i].count('}')
        i += 1
    return body, i


def get_struct_deps(body_lines):
    """Get the set of struct types referenced in a struct body."""
    deps = set()
    for line in body_lines:
        for m in re.finditer(r'\b([A-Z]\w+)\b', line):
            name = m.group(1)
            if name not in ('SplArray', 'SplValue', 'SplDict', 'FILE',
                          'Option', 'Dict', 'MAX_IDENT', 'MAX_LINE',
                          'NULL', 'INT64_MAX', 'INT64_MIN'):
                deps.add(name)
    return deps


def fix_reserved_in_struct_field(line):
    """Fix C++ reserved words used as struct field names."""
    for reserved, replacement in CPP_RESERVED.items():
        line = re.sub(r'(\s+\w[\w*&<> ]*\s+)\b' + reserved + r'\b(\s*[;=])',
                     r'\1' + replacement + r'\2', line)
    for macro, replacement in CPP_MACROS.items():
        line = re.sub(r'(\s+[\w*& <>]+\s+)\b' + macro + r'\b(\s*;)',
                     r'\1' + replacement + r'\2', line)
    return line


def is_inline_method(line):
    """Check if a line inside a struct body is an inline method definition."""
    stripped = line.strip()
    if re.match(r'int64_t\s+(fn|me|static fn)\s+\w+\(', stripped):
        return True
    if re.match(r'int64_t\s+return\b', stripped):
        return True
    if re.match(r'int64_t\s+(Ok|Err)\(', stripped):
        return True
    return False


def is_constructor_in_struct(line, struct_name):
    stripped = line.strip()
    if re.match(r'int64_t\s+' + re.escape(struct_name) + r'\(', stripped):
        return True
    return False


def clean_struct_body(body_lines, struct_name):
    """Remove inline method definitions from struct body, fix reserved words."""
    cleaned = []
    for line in body_lines:
        if is_inline_method(line):
            continue
        if is_constructor_in_struct(line, struct_name):
            continue
        # Remove lines with unmatched quotes (broken string interpolation)
        if has_unmatched_quotes(line):
            continue
        # Remove lines that have "return" keyword inside struct (method body leak)
        stripped = line.strip()
        if stripped.startswith('int64_t return ') or stripped.startswith('return '):
            if stripped != '};':  # Don't skip closing brace
                continue
        # Remove lines with Simple keywords that leaked into struct
        if re.match(r'\s*int64_t\s+(if|for|while|match)\b', stripped):
            continue
        line = fix_reserved_in_struct_field(line)
        # Fix "void fieldname;" → "int64_t fieldname;" (from unresolved types)
        line = re.sub(r'^(\s+)void (\w+);', r'\1int64_t \2;', line)
        cleaned.append(line)
    return cleaned


def has_unmatched_quotes(line):
    stripped = line.strip()
    if stripped.startswith('//') or stripped.startswith('#') or stripped.startswith('/*'):
        return False
    quote_count = 0
    in_esc = False
    for c in line:
        if in_esc:
            in_esc = False
            continue
        if c == '\\':
            in_esc = True
            continue
        if c == '"':
            quote_count += 1
    return quote_count % 2 != 0


def is_lambda_line(line):
    if '\\' not in line:
        return False
    stripped = line.strip()
    if stripped.startswith('//') or stripped.startswith('/*'):
        return False
    if re.search(r'\\[a-z]+\s*[,:]', stripped):
        bs_pos = stripped.find('\\')
        in_string = False
        for c in stripped[:bs_pos]:
            if c == '"':
                in_string = not in_string
        return not in_string
    return False


def is_toplevel_func_start(line):
    """Check if a line starts a top-level function definition."""
    if line.startswith(' ') or line.startswith('\t'):
        return False
    if line.startswith('struct ') or line.startswith('//') or line.startswith('#'):
        return False
    if line.startswith('static const ') or line.startswith('extern '):
        return False
    if line.strip() == '':
        return False
    # Must match function definition pattern and end with {
    m = FUNC_DEF_RE.match(line)
    if m and (line.rstrip().endswith('{') or line.rstrip().endswith(') {')):
        return True
    return False


def is_toplevel_fwd_decl(line):
    """Check if a line is a top-level forward declaration."""
    if line.startswith(' ') or line.startswith('\t'):
        return False
    return bool(FWD_DECL_RE.match(line))


def is_simple_fn_line(line):
    """Check if line is an untranspiled Simple fn declaration inside a function body."""
    stripped = line.strip()
    return bool(re.match(r'fn \w+\(.*\)\s*[;:]?\s*$', stripped)) or \
           bool(re.match(r'return fn \w+\(.*\)\s*[;:]?\s*$', stripped))


def build_naming_map(lines):
    """Build map from PascalCase__method to lowercase_method where applicable."""
    defined = set()
    for line in lines:
        if line.startswith(' ') or line.startswith('\t'):
            continue
        m = FUNC_DEF_RE.match(line)
        if m:
            defined.add(m.group(1))
        # Also check forward declarations
        m2 = re.match(r'^[\w* <>]+\s+(\w+)\([^)]*\)\s*;', line)
        if m2:
            defined.add(m2.group(1))

    rename_map = {}
    pascal_calls = set()
    for line in lines:
        for m in re.finditer(r'\b([A-Z]\w+__\w+)\b', line):
            call = m.group(1)
            if call not in defined:
                pascal_calls.add(call)

    for call in pascal_calls:
        parts = call.split('__', 1)
        if len(parts) == 2:
            struct_name = parts[0]
            method = parts[1]
            lower = re.sub(r'(?<=[a-z])([A-Z])', r'_\1', struct_name).lower()
            lowercase = lower + '_' + method
            if lowercase in defined:
                rename_map[call] = lowercase

    return rename_map


def fix_brace_balance(lines):
    """Fix unclosed function bodies by inserting closing braces.

    When we detect a new top-level function definition while depth > 0,
    we close the previous function(s).
    """
    result = []
    depth = 0

    for i, line in enumerate(lines):
        # If this looks like a top-level function definition and we're still inside a function
        if depth > 0 and is_toplevel_func_start(line):
            while depth > 0:
                result.append('}\n')
                depth -= 1

        # If this is a top-level forward declaration and we're inside a function
        if depth > 0 and is_toplevel_fwd_decl(line):
            while depth > 0:
                result.append('}\n')
                depth -= 1

        # Remove untranspiled Simple fn declarations inside function bodies
        if depth > 0 and is_simple_fn_line(line):
            desc = line.strip()[:70].replace('{', '(').replace('}', ')')
            result.append('    /* UNTRANSPILED_FN: ' + desc + ' */\n')
            continue

        result.append(line)
        depth += count_braces(line)

    while depth > 0:
        result.append('}\n')
        depth -= 1

    return result


def fix_cpp(input_path, output_path):
    with open(input_path, 'r', encoding='utf-8', errors='replace') as f:
        lines = f.readlines()

    # === Phase 0: Global text fixes ===
    processed = []
    for line in lines:
        # Remove problematic #define macros from codegen preamble
        if line.strip() == '#define template template_spl':
            processed.append('// (removed #define template)\n')
            continue
        if line.strip() == '#define assert spl_assert':
            processed.append('// (removed #define assert)\n')
            continue
        # Fix "bool mutable" parameter
        line = re.sub(r'\bbool mutable\b', 'bool is_mutable', line)
        # Fix ".mutable" member access
        line = re.sub(r'\.mutable\b', '.is_mutable', line)
        # Fix "const char* char" → "const char* ch" (char is C++ keyword)
        line = re.sub(r'const char\*\s+char\b', 'const char* ch', line)
        # Fix "int64_t operator" → "int64_t op_val" (operator is C++ keyword)
        line = re.sub(r'int64_t operator\b', 'int64_t op_val', line)
        # Fix "case _:" → "default:"
        line = re.sub(r'\bcase _:', 'default:', line)
        # Fix AsmOption.X → AsmOption::X
        line = line.replace('AsmOption.Volatile', 'AsmOption::Volatile')
        line = line.replace('AsmOption.AlignStack', 'AsmOption::AlignStack')
        # Fix spl_nil() assignments to non-SplValue types
        # Replace "= spl_nil()" with "= NULL" for pointer fields
        # and "= 0" for integer fields
        line = re.sub(r'= spl_nil\(\)', '= NULL', line)
        # Fix C++ reserved words used as identifiers
        # "default" as field/variable name
        line = re.sub(r'(\w)\s+default\s*;', r'\1 default_val;', line)
        line = re.sub(r'(\w)\s+default\s*=', r'\1 default_val =', line)
        line = re.sub(r'\.default\b', '.default_val', line)
        # "void param_name" in function signatures → "int64_t param_name"
        # (from unresolved generic types like List<HirExpr>)
        line = re.sub(r'\bvoid (\w+)([,)])', r'int64_t \1\2', line)
        # Fix "void varname;" and "void varname =" in function bodies
        line = re.sub(r'^(\s+)void (\w+)\s*;', r'\1int64_t \2;', line)
        line = re.sub(r'^(\s+)void (\w+)\s*=', r'\1int64_t \2 =', line)
        # Fix "template" as identifier (variable/field/param) but NOT C++ "template<"
        # Replace ".template" member access
        line = re.sub(r'\.template\b(?!\s*<)', '.template_val', line)
        # Replace "int64_t template" variable/param declarations
        line = re.sub(r'(int64_t|const char\*|bool|void|SplArray\*)\s+template\b', r'\1 template_val', line)
        # Fix "explicit" as field/variable name (C++ keyword)
        line = re.sub(r'(\w)\s+explicit\s*;', r'\1 is_explicit;', line)
        line = re.sub(r'(\w)\s+explicit\s*=', r'\1 is_explicit =', line)
        line = re.sub(r'\.explicit\b', '.is_explicit', line)
        # Fix ALL C++ reserved words as parameter/variable names comprehensively
        for reserved, replacement in [
            ('new', 'new_val'), ('delete', 'delete_val'),
            ('template', 'template_val'), ('class', 'class_val'),
            ('namespace', 'namespace_val'), ('this', 'this_val'),
            ('throw', 'throw_val'), ('try', 'try_val'), ('catch', 'catch_val'),
            ('virtual', 'virtual_val'), ('friend', 'friend_val'),
            ('private', 'private_val'), ('protected', 'protected_val'),
            ('public', 'public_val'), ('export', 'export_val'),
            ('explicit', 'is_explicit'), ('typedef', 'typedef_val'),
            ('typeid', 'typeid_val'), ('register', 'register_val'),
            ('volatile', 'is_volatile'), ('operator', 'operator_val'),
        ]:
            # In parameter lists: "Type reserved_word," or "Type reserved_word)"
            line = re.sub(r'(\w[\w*& <>]*)\s+' + reserved + r'\b(?!\s*[<(])', r'\1 ' + replacement, line)
        # Fix "int mutable" / "bool mutable" parameter
        line = re.sub(r'\bint mutable\b', 'int is_mutable', line)
        # Fix conflicting extern "C" declarations (remove duplicates that clash with runtime.h)
        # Comment out extern "C" lines with int64_t params that duplicate runtime.h's const char* versions
        if line.strip().startswith('extern "C"'):
            stripped_ec = line.strip()
            # Remove duplicates with (int64_t, int64_t) signature that conflict with (const char*) from runtime.h
            if re.search(r'\w+\(int64_t \w+_ptr, int64_t \w+_len\)', stripped_ec):
                line = '// ' + line
            elif 'spl_shell_output' in stripped_ec or 'spl_shell(' in stripped_ec:
                line = '// ' + line
        # Fix standalone "Result" type → "SplResult" (but not Result__ or XyzResult)
        line = re.sub(r'(?<![A-Za-z_])Result(?!_)\b', 'SplResult', line)
        # Fix enum dot notation: EnumName.Variant → EnumName_Variant
        line = re.sub(r'\b(TargetOS|TargetArch|CompileMode)\.(\w+)', r'\1_\2', line)
        processed.append(line)
    lines = processed

    # === Phase 1: Collect and clean struct definitions + constants ===
    struct_blocks = {}
    struct_names_order = []
    collected_constants = []  # Constants found in struct section

    idx = 0
    while idx < len(lines):
        m = re.match(r'^struct (\w+) \{', lines[idx])
        if m:
            name = m.group(1)
            body, end_idx = extract_struct_body(lines, idx)
            if name not in struct_blocks:
                cleaned = clean_struct_body(body, name)
                struct_blocks[name] = cleaned
                struct_names_order.append(name)
            idx = end_idx
            continue
        # Also collect constants (they appear interspersed with structs)
        mc = re.match(r'^static const int64_t (\w+) = ', lines[idx])
        if mc:
            collected_constants.append((mc.group(1), lines[idx]))
        idx += 1

    # Topological sort
    def topo_sort(sblocks, order):
        deps = {}
        for name in order:
            d = get_struct_deps(sblocks[name])
            deps[name] = d & set(order)
            deps[name].discard(name)

        in_degree = {n: 0 for n in order}
        for n in order:
            for d in deps[n]:
                if d in in_degree:
                    in_degree[n] += 1

        adj = {n: [] for n in order}
        for n in order:
            for d in deps[n]:
                if d in adj:
                    adj[d].append(n)

        queue = [n for n in order if in_degree[n] == 0]
        result = []
        while queue:
            queue.sort(key=lambda x: order.index(x))
            node = queue.pop(0)
            result.append(node)
            for neighbor in adj[node]:
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    queue.append(neighbor)

        for n in order:
            if n not in result:
                result.append(n)
        return result

    sorted_structs = topo_sort(struct_blocks, struct_names_order)

    # === Phase 2: Build naming map ===
    naming_map = build_naming_map(lines)
    print(f"Built naming map with {len(naming_map)} renames")

    # === Phase 3: Rebuild the file ===
    result = []
    emitted_structs = set()
    emitted_constants = set()

    # Find section boundaries
    struct_section_start = None
    for idx in range(len(lines)):
        if re.match(r'^struct \w+\s*[;{]', lines[idx]):
            struct_section_start = idx
            break

    func_section_start = None
    for idx in range(len(lines)):
        if idx <= (struct_section_start or 0):
            continue
        line = lines[idx]
        if is_toplevel_func_start(line) or is_toplevel_fwd_decl(line):
            func_section_start = idx
            break

    # 1. Preamble
    idx = 0
    added_includes = False
    added_compat = False
    while idx < (struct_section_start or len(lines)):
        line = lines[idx]
        # Add extra includes right after the vector include (before extern "C")
        if not added_includes and line.strip() == '' and idx > 5 and idx < 15:
            result.append('#include <algorithm>\n')
            result.append('\n')
            added_includes = True

        # Add compat macros after extern "C" { runtime.h } block
        if not added_compat and added_includes and line.strip() == '}' and idx > 8:
            result.append(line)
            result.append('\n')
            result.append('// Compatibility macros\n')
            result.append('#define nil 0\n')
            result.append('template<typename T> T spl_Ok(T v) { return v; }\n')
            result.append('inline int64_t spl_Err(const char* msg) { return 0; }\n')
            result.append('inline int64_t spl_Err(int64_t v) { return 0; }\n')
            result.append('\n')
            result.append('namespace AsmOption { static const int64_t Volatile = 1; static const int64_t AlignStack = 2; }\n')
            result.append('inline void asm_add_option(int64_t, int64_t) {}\n')
            result.append('\n')
            result.append('// Missing runtime stubs\n')
            result.append('extern "C" {\n')
            result.append('int64_t rt_dir_exists(const char* path) { return 0; }\n')
            result.append('const char* rt_path_join(const char* a, const char* b) {\n')
            result.append('    static char buf[4096];\n')
            result.append('    snprintf(buf, sizeof(buf), "%s/%s", a, b);\n')
            result.append('    return buf;\n')
            result.append('}\n')
            result.append('int64_t rt_get_host_target_code() { return 4; } // Windows\n')
            result.append('int64_t rt_cpu_count() { return 1; }\n')
            result.append('const char* rt_env_get(const char* name) { char* v = getenv(name); return v ? v : ""; }\n')
            result.append('const char* rt_process_run(const char* cmd, SplArray* args) { return ""; }\n')
            result.append('SplArray* rt_debug_stack_trace_lines() { return spl_array_new(); }\n')
            result.append('}\n')
            result.append('\n')
            added_compat = True
            idx += 1
            continue

        m = re.match(r'^static const int64_t (\w+) = (\d+);', line)
        if m:
            name = m.group(1)
            if name in emitted_constants:
                idx += 1
                continue
            emitted_constants.add(name)
        result.append(line)
        idx += 1

    if struct_section_start is not None:
        # 2. Forward declarations
        for name in sorted_structs:
            result.append(f'struct {name};\n')
        result.append('\n')

        # 3. Struct definitions
        for name in sorted_structs:
            if name in struct_blocks:
                for bline in struct_blocks[name]:
                    result.append(bline)
                result.append('\n')
                emitted_structs.add(name)

        # 3b. Emit collected constants (deduped)
        result.append('\n// Constants\n')
        for cname, cline in collected_constants:
            if cname not in emitted_constants:
                result.append(cline)
                emitted_constants.add(cname)
        result.append('\n')

        # Post-struct stubs that need struct types
        result.append('// Post-struct stubs\n')
        result.append('inline int64_t HirExprKind_InlineAsm_new(int64_t, SplArray*, Span) { return 0; }\n')
        result.append('\n')
        # Add CompileResult as a struct (seed generates it as enum but code uses it as struct)
        result.append('struct CompileResult { int64_t kind; const char* message; bool is_success() const { return kind == 0; } };\n')
        # Add CoercionResult if not already defined
        if 'CoercionResult' not in struct_blocks:
            result.append('struct CoercionResult { int64_t kind; int64_t value; };\n')
        result.append('\n')

        # 4. Skip entire original struct/constant section up to function section
        # We already emitted sorted structs above and constants above
        idx = func_section_start or struct_section_start

    # 5. Functions section - collect all remaining lines first
    func_lines = []
    while idx < len(lines):
        line = lines[idx]

        # Remove duplicate static const
        m = re.match(r'^static const int64_t (\w+) = (\d+);', line)
        if m:
            name = m.group(1)
            if name in emitted_constants:
                idx += 1
                continue
            emitted_constants.add(name)

        # Remove duplicate struct definitions
        m = re.match(r'^struct (\w+) \{', line)
        if m:
            name = m.group(1)
            if name in emitted_structs or name in struct_blocks:
                _, end_idx = extract_struct_body(lines, idx)
                idx = end_idx
                continue

        # Remove stray lambda lines
        if is_lambda_line(line):
            func_lines.append('    /* LAMBDA_REMOVED */\n')
            idx += 1
            continue

        # Fix missing terminating quotes
        if has_unmatched_quotes(line):
            func_lines.append('    /* BROKEN_STRING */\n')
            idx += 1
            continue

        # Fix Ok/Err calls (convert to function calls instead of macros)
        # "return Ok(...)" → "return spl_Ok(...)"
        # "return Err(...)" → "return spl_Err(...)"
        line = re.sub(r'\bOk\(', 'spl_Ok(', line)
        line = re.sub(r'\bErr\(', 'spl_Err(', line)

        # Fix PascalCase__method naming mismatches
        for pascal, lower in naming_map.items():
            line = re.sub(r'\b' + re.escape(pascal) + r'\b', lower, line)

        # Fix constructor calls with named args: "StructName(field: val)" → "StructName{}"
        if re.search(r'\b[A-Z]\w+\(\w+:', line) and '::' not in line:
            stripped = line.strip()
            if not stripped.startswith('//') and not stripped.startswith('/*'):
                # Only fix return statements with constructor calls
                m2 = re.match(r'^(\s*)return\s+([A-Z]\w+)\((\w+):', line)
                if m2:
                    func_lines.append(f'{m2.group(1)}return {m2.group(2)}{{}}; /* TODO_CTOR */\n')
                    idx += 1
                    continue

        # Fix "match X:" that wasn't converted (already turned to "match X:;")
        if re.match(r'.*= match \w+.*:;', line.strip()):
            # Replace "var = match expr:;" with "var = 0; /* TODO_MATCH */"
            line = re.sub(r'= match \w+[^;]*:;', '= 0; /* TODO_MATCH */', line)

        # Fix "if condition:" that was left as Simple syntax
        line = re.sub(r'= if (\w+):;', r'= (\1) ? 1 : 0; /* TODO_IF_EXPR */', line)

        # Fix "else:;" leftover
        if line.strip() == 'else:;':
            func_lines.append('    /* ELSE_REMOVED */\n')
            idx += 1
            continue

        # Fix void main() → void spl_main() to avoid conflict with runtime's int main()
        if re.match(r'^void main\(\)', line):
            line = line.replace('void main()', 'void spl_main()', 1)
        # Fix main() forward declaration too
        if line.strip() == 'void main();':
            line = line.replace('void main();', 'void spl_main();')

        # Remove broken forward declarations with garbled syntax
        stripped = line.strip()
        if stripped.endswith(');') and '(' in stripped:
            params = stripped.split('(', 1)[-1]
            # Check for garbled parameter lists containing stray > ] or type names after int64_t
            if re.search(r'int64_t\s+[A-Z]\w*>', params) or re.search(r'int64_t\s*[\]>]', params):
                desc = stripped[:70].replace('{', '(').replace('}', ')')
                func_lines.append(f'/* BROKEN_FWD_DECL: {desc} */\n')
                idx += 1
                continue
        # Also fix garbled function definitions (not just declarations)
        if (stripped.endswith(') {') or stripped.endswith('){')) and '(' in stripped:
            params = stripped.split('(', 1)[-1]
            if re.search(r'int64_t\s+[A-Z]\w*>', params) or re.search(r'int64_t\s*[\]>]', params):
                # Use a comment without braces to avoid brace counting issues
                desc = stripped[:70].replace('{', '(').replace('}', ')')
                func_lines.append(f'/* BROKEN_FUNC_DEF: {desc} */\n')
                # Skip body: track brace depth and skip until function closes
                depth = count_braces(stripped)
                idx += 1
                while idx < len(lines) and depth > 0:
                    body_line = lines[idx]
                    depth += count_braces(body_line)
                    idx += 1
                continue
        # Fix destructuring pattern leak in function signatures
        if '_destruct_' in stripped:
            desc = stripped[:70].replace('{', '(').replace('}', ')')
            func_lines.append(f'/* BROKEN_DESTRUCT: {desc} */\n')
            idx += 1
            continue

        # Remove untranspiled Simple statements
        if stripped.startswith('from ') and 'import' in stripped:
            desc = stripped[:60].replace('{', '(').replace('}', ')')
            func_lines.append(f'    /* REMOVED_IMPORT: {desc} */\n')
            idx += 1
            continue
        if stripped.startswith('type ') and '=' in stripped:
            func_lines.append(f'    /* REMOVED_TYPE_ALIAS */\n')
            idx += 1
            continue
        if stripped.startswith('abstract class ') or stripped.startswith('trait '):
            func_lines.append(f'    /* REMOVED_ABSTRACT */\n')
            idx += 1
            continue
        if re.match(r'^_as_\d+\s*=', stripped):
            func_lines.append(f'    /* REMOVED_AS_PATTERN */\n')
            idx += 1
            continue
        # Remove "/* TODO: } */" lines that contain counted braces
        if '/* TODO:' in line and '}' in line:
            func_lines.append(f'    /* REMOVED_TODO */\n')
            idx += 1
            continue

        func_lines.append(line)
        idx += 1

    # === Phase 4: Fix brace balance ===
    func_lines = fix_brace_balance(func_lines)

    # === Phase 4b: Remove duplicate function definitions ===
    # Key by function name only to catch duplicates with different
    # return types or parameter names
    defined_func_names = set()
    deduped = []
    fi = 0
    while fi < len(func_lines):
        fline = func_lines[fi]
        # Check if this is a function definition
        if not fline.startswith(' ') and not fline.startswith('\t') and not fline.startswith('//') and not fline.startswith('#') and not fline.startswith('/*'):
            m = re.match(r'^[\w* <>]+\s+(\w+)\([^)]*\)\s*\{', fline)
            if m:
                func_key = m.group(1)
                if func_key in defined_func_names:
                    # Skip this duplicate function
                    depth = count_braces(fline)
                    fi += 1
                    while fi < len(func_lines) and depth > 0:
                        depth += count_braces(func_lines[fi])
                        fi += 1
                    continue
                defined_func_names.add(func_key)
        deduped.append(fline)
        fi += 1
    func_lines = deduped

    # === Phase 4c: Remove orphan closing braces ===
    # Sometimes broken function removal leaves orphan } at top level
    cleaned_func = []
    depth = 0
    for fline in func_lines:
        bc = count_braces(fline)
        new_depth = depth + bc
        if new_depth < 0:
            # This } would go negative - it's an orphan
            cleaned_func.append('/* ORPHAN_BRACE */\n')
            new_depth = 0
        else:
            cleaned_func.append(fline)
        depth = new_depth
    func_lines = cleaned_func

    # === Phase 4d: Remove conflicting forward declarations ===
    # Collect all function definitions (with bodies) to know actual return types
    defined_returns = {}  # func_name -> return_type
    for fline in func_lines:
        m = re.match(r'^([\w* <>]+)\s+(\w+)\([^)]*\)\s*\{', fline)
        if m:
            ret = m.group(1).strip()
            name = m.group(2)
            defined_returns[name] = ret

    # Also collect extern "C" forward declarations
    for fline in func_lines:
        m = re.match(r'^extern "C"\s+([\w* <>]+)\s+(\w+)\([^)]*\)\s*;', fline)
        if m:
            ret = m.group(1).strip()
            name = m.group(2)
            if name not in defined_returns:
                defined_returns[name] = ret

    # Remove forward declarations that conflict with earlier declarations/definitions
    seen_fwd = {}  # func_name -> return_type (first forward decl seen)
    filtered_func = []
    seen_static_vars = set()
    for fline in func_lines:
        # Remove duplicate static variable declarations
        ms = re.match(r'^static int64_t (\w+);', fline)
        if ms:
            varname = ms.group(1)
            if varname in seen_static_vars:
                continue
            seen_static_vars.add(varname)

        # Check forward declarations
        m = re.match(r'^(?:extern "C"\s+)?([\w* <>]+)\s+(\w+)\([^)]*\)\s*;', fline)
        if m:
            ret = m.group(1).strip()
            name = m.group(2)
            # Conflict with a function definition
            if name in defined_returns and defined_returns[name] != ret:
                filtered_func.append(f'/* REMOVED_CONFLICT_FWD: {fline.rstrip()} */\n')
                continue
            # Duplicate forward declaration with different return type
            if name in seen_fwd and seen_fwd[name] != ret:
                filtered_func.append(f'/* REMOVED_DUP_FWD: {fline.rstrip()} */\n')
                continue
            seen_fwd[name] = ret
        filtered_func.append(fline)
    func_lines = filtered_func

    result.extend(func_lines)

    # === Phase 5: Generate stubs for undefined functions ===
    # Collect defined functions
    defined_funcs = set()
    for line in result:
        if line.startswith(' ') or line.startswith('\t'):
            continue
        m = FUNC_DEF_RE.match(line)
        if m:
            defined_funcs.add(m.group(1))
        m2 = re.match(r'^[\w* <>]+\s+(\w+)\([^)]*\)\s*;', line)
        if m2:
            defined_funcs.add(m2.group(1))

    # Also collect functions defined in function bodies (with bodies)
    for line in result:
        if line.startswith(' ') or line.startswith('\t'):
            continue
        # Match function definition with opening brace
        m2 = re.match(r'^[\w* <>]+\s+(\w+)\(.*\)\s*\{', line)
        if m2:
            defined_funcs.add(m2.group(1))
        # Match function forward declaration
        m3 = re.match(r'^[\w* <>]+\s+(\w+)\([^)]*\)\s*;', line)
        if m3:
            defined_funcs.add(m3.group(1))

    # Find all undefined PascalCase__method calls
    needed_stubs = set()
    for line in result:
        for m in re.finditer(r'\b([A-Z]\w+__\w+)\b', line):
            call = m.group(1)
            if call not in defined_funcs and not call.startswith('AsmOption'):
                needed_stubs.add(call)

    # Also find undefined lowercase function calls
    for line in result:
        for m in re.finditer(r'\b(miroperandkind_\w+|value_\w+)\b', line):
            call = m.group(1)
            if call not in defined_funcs:
                needed_stubs.add(call)

    # Generate stubs
    stubs = []
    stubs.append('\n// === Auto-generated stub functions ===\n')
    for call in sorted(needed_stubs):
        parts = call.split('__', 1)
        if len(parts) == 2:
            struct_name = parts[0]
            method = parts[1]
            # Check if struct_name is an emitted struct (safe to reference)
            is_emitted = struct_name in emitted_structs
            if method.endswith('_push'):
                stubs.append(f'void {call}(...) {{ }}\n')
            elif method.endswith('_len'):
                stubs.append(f'int64_t {call}(...) {{ return 0; }}\n')
            elif method.endswith('_get'):
                stubs.append(f'int64_t {call}(...) {{ return 0; }}\n')
            elif method.endswith('_contains_key') or method.endswith('_contains'):
                stubs.append(f'bool {call}(...) {{ return false; }}\n')
            elif method == 'default' and is_emitted:
                stubs.append(f'{struct_name} {call}() {{ return {struct_name}{{}}; }}\n')
            elif (method == 'new' or method.startswith('new_')) and is_emitted:
                stubs.append(f'{struct_name} {call}(...) {{ return {struct_name}{{}}; }}\n')
            elif method == 'emit' or method.startswith('emit_'):
                stubs.append(f'void {call}(...) {{ }}\n')
            else:
                stubs.append(f'int64_t {call}(...) {{ return 0; }}\n')
        else:
            stubs.append(f'int64_t {call}(...) {{ return 0; }}\n')
    stubs.append('\n')

    # Find insert position: after all struct definitions, before first function
    # We need stubs to come after structs so they can reference struct types
    insert_pos = None
    last_struct_end = None
    for i, line in enumerate(result):
        # Track end of struct definitions (closing brace with semicolon)
        if re.match(r'^struct \w+\s*\{', line):
            # Find closing }; for this struct
            for j in range(i, min(i + 200, len(result))):
                if result[j].strip().startswith('};'):
                    last_struct_end = j + 1
                    break
        # Track where functions start
        if insert_pos is None and (is_toplevel_func_start(line) or is_toplevel_fwd_decl(line)):
            insert_pos = i
    # Prefer inserting after last struct, fall back to before first function
    if last_struct_end and last_struct_end > (insert_pos or 0):
        insert_pos = last_struct_end
    elif insert_pos is None:
        insert_pos = len(result)

    if insert_pos and stubs:
        result = result[:insert_pos] + stubs + result[insert_pos:]
        print(f"Generated {len(needed_stubs)} stub functions")

    # Write output
    with open(output_path, 'w', encoding='utf-8') as f:
        f.writelines(result)

    print(f"Processed {len(lines)} lines -> {len(result)} lines")
    print(f"Defined {len(emitted_constants)} unique constants, {len(struct_blocks)} structs (sorted)")


if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: fix_cpp.py <input.cpp> <output.cpp>")
        sys.exit(1)
    fix_cpp(sys.argv[1], sys.argv[2])
