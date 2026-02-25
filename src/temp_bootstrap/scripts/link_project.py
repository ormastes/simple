#!/usr/bin/env python3
"""
Bootstrap Project Linker: Rewrite generated C files with module-prefixed function names.

This script handles multi-file linking for the Simple compiler bootstrap by:
1. Scanning .spl source files for function definitions and import statements
2. Building a global function registry and per-file import maps
3. Rewriting .c files with module-prefixed function names
4. Generating a unified C file that can be compiled to a single binary

Usage:
    python3 link_project.py <spl_source_dir> <c_files_dir> <output.c> [--entry=<module>]
"""

import os
import re
import sys
from pathlib import Path
from collections import defaultdict


def file_path_to_module_prefix(file_path: str, base_dir: str) -> str:
    """Convert a .spl file path to a module prefix.

    src/compiler/00.common/config.spl -> compiler__common__config
    """
    rel = os.path.relpath(file_path, base_dir)
    # Strip .spl extension
    rel = rel.replace('.spl', '')
    # Split into parts
    parts = rel.replace('\\', '/').split('/')
    # Strip numbered directory prefixes: 00.common -> common
    cleaned = []
    for p in parts:
        # Match pattern like "00.common", "10.frontend", "95.interp"
        m = re.match(r'^\d+\.(.+)$', p)
        if m:
            cleaned.append(m.group(1))
        else:
            cleaned.append(p)
    return '__'.join(cleaned)


def file_path_to_import_path(file_path: str, base_dir: str) -> str:
    """Convert a .spl file path to the dotted import path.

    src/compiler/00.common/config.spl -> compiler.common.config
    """
    rel = os.path.relpath(file_path, base_dir)
    rel = rel.replace('.spl', '')
    parts = rel.replace('\\', '/').split('/')
    cleaned = []
    for p in parts:
        m = re.match(r'^\d+\.(.+)$', p)
        if m:
            cleaned.append(m.group(1))
        else:
            cleaned.append(p)
    return '.'.join(cleaned)


def c_filename_to_module_prefix(c_filename: str) -> str:
    """Convert a C filename back to a module prefix.

    src_compiler_00.common_config.c -> compiler__common__config
    """
    # Only strip the trailing .c extension
    if c_filename.endswith('.c'):
        name = c_filename[:-2]
    else:
        name = c_filename
    # Strip 'src_' prefix
    if name.startswith('src_'):
        name = name[4:]
    # Split on _ (path separators in the flattened filename)
    parts = name.split('_')
    cleaned = []
    for p in parts:
        # Strip numbered directory prefixes: 00.common -> common
        m = re.match(r'^(\d+)\.(.+)$', p)
        if m:
            cleaned.append(m.group(2))
        else:
            cleaned.append(p)
    return '__'.join(cleaned)


def extract_spl_functions(source: str) -> list:
    """Extract function names from Simple source code."""
    funcs = []
    for line in source.split('\n'):
        line = line.strip()
        # fn name(, me name(, static fn name(
        m = re.match(r'^(?:pub\s+)?(?:static\s+)?(?:fn|me)\s+(\w+)\s*[\(<]', line)
        if m:
            funcs.append(m.group(1))
        # Also match: fn name() -> type:
        m = re.match(r'^(?:pub\s+)?(?:static\s+)?(?:fn|me)\s+(\w+)\s*\(', line)
        if m and m.group(1) not in funcs:
            funcs.append(m.group(1))
    return funcs


def extract_spl_class_names(source: str) -> list:
    """Extract class/struct/enum names from Simple source."""
    names = []
    for line in source.split('\n'):
        line = line.strip()
        m = re.match(r'^(?:pub\s+)?(?:class|struct|enum)\s+(\w+)', line)
        if m:
            names.append(m.group(1))
    return names


def extract_spl_imports(source: str) -> list:
    """Extract import information from Simple source.

    Returns list of (module_path_segments, imported_names) tuples.
    module_path_segments: ['compiler', 'common', 'config']
    imported_names: ['get_config', 'set_config'] or ['*'] for glob
    """
    imports = []
    lines = source.split('\n')
    i = 0
    while i < len(lines):
        line = lines[i].strip()

        # Skip comments
        if line.startswith('#'):
            i += 1
            continue

        # Match: use path.to.module.{name1, name2}
        m = re.match(r'^(?:common\s+)?use\s+(.+)$', line)
        if not m:
            i += 1
            continue

        use_text = m.group(1).strip()

        # Handle multi-line imports (collect continuation lines)
        while use_text.count('{') > use_text.count('}'):
            i += 1
            if i < len(lines):
                use_text += ' ' + lines[i].strip()
            else:
                break

        # Parse the use statement
        parsed = parse_use_path(use_text)
        if parsed:
            imports.extend(parsed)

        i += 1

    return imports


def parse_use_path(text: str) -> list:
    """Parse a use path into (module_path_segments, imported_names) tuples."""
    results = []

    # Remove trailing comments
    if '#' in text:
        text = text[:text.index('#')]
    text = text.strip().rstrip(':')

    # Handle: module.path.{name1, name2}
    m = re.match(r'^([\w.]+)\.\{([^}]+)\}(.*)$', text)
    if m:
        path_str = m.group(1)
        names_str = m.group(2)
        rest = m.group(3).strip()

        segments = path_str.split('.')
        names = [n.strip().split(' as ')[0].strip() for n in names_str.split(',') if n.strip()]
        results.append((segments, names))

        # Handle comma-separated additional imports
        if rest.startswith(','):
            rest = rest[1:].strip()
            more = parse_use_path(rest)
            if more:
                results.extend(more)
        return results

    # Handle: module.path.*
    m = re.match(r'^([\w.]+)\.\*$', text)
    if m:
        path_str = m.group(1)
        segments = path_str.split('.')
        results.append((segments, ['*']))
        return results

    # Handle: module.path.Name (single import)
    m = re.match(r'^([\w.]+)\.(\w+)$', text)
    if m:
        path_str = m.group(1)
        name = m.group(2)
        segments = path_str.split('.')
        results.append((segments, [name]))
        return results

    # Handle: Name (bare import, likely a keyword or very short path)
    m = re.match(r'^(\w+)$', text)
    if m:
        results.append(([m.group(1)], ['*']))
        return results

    return results


def resolve_module_path(segments: list, name_to_prefix: dict, path_to_prefix: dict,
                        short_name_to_prefix: dict) -> str:
    """Resolve a module path to a module prefix.

    Tries: full dotted path, then partial paths, then last segment.
    """
    # Try full path
    full_path = '.'.join(segments)
    if full_path in path_to_prefix:
        return path_to_prefix[full_path]

    # Try without first segment (e.g., 'compiler.common.config' might be stored as 'common.config')
    if len(segments) > 1:
        for start in range(len(segments)):
            partial = '.'.join(segments[start:])
            if partial in path_to_prefix:
                return path_to_prefix[partial]

    # Try last segment as short name
    last = segments[-1]
    if last in short_name_to_prefix:
        matches = short_name_to_prefix[last]
        if len(matches) == 1:
            return matches[0]
        # Try to disambiguate using more path info
        for prefix in matches:
            if all(seg in prefix for seg in segments):
                return prefix
        # Return first match as fallback
        return matches[0]

    return None


def extract_c_functions(c_source: str) -> list:
    """Extract function names from generated C source (definitions only)."""
    funcs = []
    for line in c_source.split('\n'):
        # Match function definitions (not declarations or comments)
        m = re.match(r'^(?:int64_t|void)\s+(\w+)\s*\(', line)
        if m:
            name = m.group(1)
            if name not in ('main',):  # Keep main special
                funcs.append(name)
    return funcs


def extract_c_forward_decls(c_source: str) -> list:
    """Extract forward declarations."""
    decls = []
    for line in c_source.split('\n'):
        m = re.match(r'^((?:int64_t|void)\s+(\w+)\s*\([^)]*\));$', line)
        if m:
            decls.append((m.group(2), m.group(1)))
    return decls


def rename_in_code(line: str, pattern: str, rename_map: dict) -> str:
    """Apply rename_map to a line of C code, skipping string literals."""
    result = []
    i = 0
    in_string = False
    while i < len(line):
        if line[i] == '"' and (i == 0 or line[i-1] != '\\'):
            in_string = not in_string
            result.append(line[i])
            i += 1
            continue
        if in_string:
            result.append(line[i])
            i += 1
            continue
        # Outside strings: try to match a word boundary + pattern
        # Check if we're at a word boundary
        if i > 0 and (line[i-1].isalnum() or line[i-1] == '_'):
            result.append(line[i])
            i += 1
            continue
        # Try to match any name in rename_map
        m = re.match(r'(\w+)', line[i:])
        if m:
            word = m.group(1)
            # Check if the word ends at a word boundary
            end = i + len(word)
            if end < len(line) and (line[end].isalnum() or line[end] == '_'):
                # Not a full word match
                result.append(line[i])
                i += 1
                continue
            if word in rename_map:
                result.append(rename_map[word])
                i += len(word)
                continue
            else:
                result.append(word)
                i += len(word)
                continue
        result.append(line[i])
        i += 1
    return ''.join(result)


def rewrite_c_file(c_source: str, module_prefix: str,
                   local_func_names: set, import_map: dict,
                   all_defined_funcs: dict) -> str:
    """Rewrite a C file with module-prefixed function names.

    local_func_names: set of function names defined in this module
    import_map: {name -> qualified_prefix} from imports
    all_defined_funcs: {name -> [module_prefix1, ...]} global registry
    """
    # Build the name replacement map for this file
    rename_map = {}

    # Local functions get current module prefix
    for name in local_func_names:
        if name == 'simple_main':
            rename_map[name] = f'{module_prefix}__simple_main'
        elif name == 'main':
            continue  # Don't rename C main
        else:
            rename_map[name] = f'{module_prefix}__{name}'

    # Imported functions get their module's prefix
    for name, target_prefix in import_map.items():
        if name not in rename_map:  # Don't override local definitions
            rename_map[name] = f'{target_prefix}__{name}'

    # String constant prefix for this module (avoid _str_N conflicts)
    str_prefix = module_prefix.replace('__', '_')

    # Find all _str_N references in the source and add them to rename_map
    for m in re.finditer(r'\b(_str_\d+)\b', c_source):
        old_name = m.group(1)
        # _str_N -> _str_{module}_N
        num = old_name.split('_str_')[1]
        new_name = f'_str_{str_prefix}_{num}'
        rename_map[old_name] = new_name

    # For names that appear in calls but aren't local or imported,
    # try to find them in the global registry
    # (We'll do this during the actual rewriting)

    lines = c_source.split('\n')
    output_lines = []
    in_function_body = False
    brace_depth = 0

    # First pass: collect all function call names used in the file
    call_names_used = set()
    for line in lines:
        # Find function calls: name(
        for m in re.finditer(r'\b(\w+)\s*\(', line):
            name = m.group(1)
            if not name.startswith(('_v', 'bb', 'int', 'void', 'if', 'goto', 'return',
                                    'sizeof', 'format', 'static', 'extern', 'const',
                                    'char', 'double', 'int32_t', 'int64_t', 'intptr_t',
                                    'memset', 'memcpy', 'strlen', 'strcmp', 'malloc', 'free',
                                    'fmod', 'pow', 'sqrt', 'floor', 'ceil', 'round',
                                    'fabs', 'abs', 'labs')):
                call_names_used.add(name)

    # Resolve unknown calls through global registry (if unambiguous)
    for name in call_names_used:
        if name not in rename_map and name in all_defined_funcs:
            if name.startswith(('rt_', '__spl_', '__bootstrap')):
                continue  # Runtime functions, don't rename
            prefixes = all_defined_funcs[name]
            if len(prefixes) == 1:
                # Unambiguous - use the only definition
                rename_map[name] = f'{prefixes[0]}__{name}'

    # Build regex for name replacement
    # Sort by length (longest first) to avoid partial replacements
    if rename_map:
        # We need word-boundary matching
        pattern_names = sorted(rename_map.keys(), key=len, reverse=True)
        # Escape regex special chars
        pattern = '|'.join(re.escape(n) for n in pattern_names)
    else:
        pattern = None

    for line in lines:
        # Skip #include and extern declarations (runtime declarations)
        if line.startswith('#include') or line.startswith('extern '):
            output_lines.append(line)
            continue

        # Skip the C main entry point
        if line.startswith('int main('):
            output_lines.append(line)
            continue
        if '(int)simple_main()' in line:
            output_lines.append(line)
            continue

        # Skip comments and empty lines
        if line.startswith('/*') or line.startswith(' *') or line.startswith('//') or not line.strip():
            output_lines.append(line)
            continue

        # Prefix string constant labels to avoid cross-module conflicts
        if line.strip().startswith('static const char _str_'):
            # _str_N -> _str_{module}_N
            new_line = re.sub(r'\b_str_(\d+)\b', f'_str_{str_prefix}_\\1', line)
            output_lines.append(new_line)
            continue

        # For all other lines, apply the rename map (but skip inside string literals)
        if pattern:
            new_line = rename_in_code(line, pattern, rename_map)
            output_lines.append(new_line)
        else:
            output_lines.append(line)

    return '\n'.join(output_lines)


def generate_extern_declarations(module_prefix: str, import_map: dict,
                                all_defined_funcs: dict, local_func_names: set) -> str:
    """Generate extern declarations for cross-module functions."""
    lines = []
    declared = set()

    for name, target_prefix in import_map.items():
        qualified = f'{target_prefix}__{name}'
        if qualified not in declared and name not in local_func_names:
            # We don't know the exact signature, so declare as variadic
            lines.append(f'extern int64_t {qualified}();')
            declared.add(qualified)

    return '\n'.join(lines)


def main():
    if len(sys.argv) < 4:
        print(f"Usage: {sys.argv[0]} <spl_source_dir> <c_files_dir> <output.c> [--entry=<module_prefix>]")
        sys.exit(1)

    spl_dir = sys.argv[1]
    c_dir = sys.argv[2]
    output_path = sys.argv[3]
    entry_module = None

    for arg in sys.argv[4:]:
        if arg.startswith('--entry='):
            entry_module = arg.split('=', 1)[1]

    print(f"[1/6] Scanning .spl source files in {spl_dir}...")

    # ========== Phase 1: Scan .spl files ==========
    spl_files = []
    for root, dirs, files in os.walk(spl_dir):
        for f in sorted(files):
            if f.endswith('.spl'):
                spl_files.append(os.path.join(root, f))

    print(f"  Found {len(spl_files)} .spl files")

    # Per-module data
    module_functions = {}  # module_prefix -> [func_names]
    module_classes = {}    # module_prefix -> [class_names]
    module_imports = {}    # module_prefix -> [(path_segments, imported_names)]

    # Maps for import resolution
    path_to_prefix = {}    # dotted.path -> module_prefix
    short_name_to_prefix = defaultdict(list)  # last_segment -> [module_prefix, ...]

    for spl_file in spl_files:
        try:
            source = open(spl_file, 'r', errors='replace').read()
        except:
            continue

        prefix = file_path_to_module_prefix(spl_file, spl_dir)
        import_path = file_path_to_import_path(spl_file, spl_dir)

        funcs = extract_spl_functions(source)
        classes = extract_spl_class_names(source)
        imports = extract_spl_imports(source)

        module_functions[prefix] = funcs
        module_classes[prefix] = classes
        module_imports[prefix] = imports

        # Build path maps
        path_to_prefix[import_path] = prefix
        # Also store partial paths
        parts = import_path.split('.')
        for start in range(len(parts)):
            partial = '.'.join(parts[start:])
            path_to_prefix[partial] = prefix

        # Short name (last segment)
        short_name = parts[-1]
        if prefix not in short_name_to_prefix[short_name]:
            short_name_to_prefix[short_name].append(prefix)

    # Build global function registry: func_name -> [module_prefix, ...]
    global_func_registry = defaultdict(list)
    for prefix, funcs in module_functions.items():
        for func in funcs:
            global_func_registry[func].append(prefix)

    # Also register class names (constructors)
    for prefix, classes in module_classes.items():
        for cls in classes:
            global_func_registry[cls].append(prefix)

    print(f"  {sum(len(v) for v in module_functions.values())} function definitions")
    print(f"  {sum(len(v) for v in module_imports.values())} import statements")
    print(f"  {len(global_func_registry)} unique function names")

    # ========== Phase 2: Resolve imports ==========
    print(f"\n[2/6] Resolving imports...")

    per_module_import_map = {}  # module_prefix -> {local_name -> target_prefix}
    unresolved_count = 0
    resolved_count = 0

    for prefix, imports in module_imports.items():
        import_map = {}

        for path_segments, names in imports:
            target_prefix = resolve_module_path(
                path_segments, short_name_to_prefix, path_to_prefix, short_name_to_prefix
            )

            if target_prefix is None:
                unresolved_count += 1
                continue

            if names == ['*']:
                # Glob import: import all functions from target module
                target_funcs = module_functions.get(target_prefix, [])
                target_classes = module_classes.get(target_prefix, [])
                for func in target_funcs:
                    import_map[func] = target_prefix
                for cls in target_classes:
                    import_map[cls] = target_prefix
                resolved_count += 1
            else:
                for name in names:
                    name = name.strip()
                    if name:
                        import_map[name] = target_prefix
                resolved_count += 1

        per_module_import_map[prefix] = import_map

    print(f"  Resolved: {resolved_count}, Unresolved: {unresolved_count}")

    # ========== Phase 3: Scan C files ==========
    print(f"\n[3/6] Scanning C files in {c_dir}...")

    all_c_files = sorted([f for f in os.listdir(c_dir) if f.endswith('.c')])

    # Deduplicate: prefer files with numbered directory prefixes (e.g., 00.common)
    # over symlink duplicates (e.g., common)
    numbered_files = [f for f in all_c_files if re.search(r'\d+\.', f)]
    unnumbered_files = [f for f in all_c_files if not re.search(r'\d+\.', f)]

    def canonical_name(f):
        return re.sub(r'\d+\.', '', f)

    numbered_canonicals = {canonical_name(f) for f in numbered_files}
    c_files = list(numbered_files)
    for f in unnumbered_files:
        if canonical_name(f) not in numbered_canonicals:
            c_files.append(f)
    c_files.sort()

    print(f"  Found {len(all_c_files)} C files ({len(all_c_files) - len(c_files)} symlink duplicates removed)")
    print(f"  Using {len(c_files)} unique C files")

    # Map C filename -> module_prefix
    c_file_to_prefix = {}
    for cf in c_files:
        prefix = c_filename_to_module_prefix(cf)
        c_file_to_prefix[cf] = prefix

    # Collect C function definitions per file
    c_module_funcs = {}  # module_prefix -> set of func names
    for cf in c_files:
        prefix = c_file_to_prefix[cf]
        with open(os.path.join(c_dir, cf), 'r') as f:
            content = f.read()
        funcs = set(extract_c_functions(content))
        c_module_funcs[prefix] = funcs

    # Build C-level global registry
    c_global_registry = defaultdict(list)
    for prefix, funcs in c_module_funcs.items():
        for func in funcs:
            c_global_registry[func].append(prefix)

    # ========== Phase 4: Rewrite C files ==========
    print(f"\n[4/6] Rewriting C files with module prefixes...")

    rewritten_files = {}  # filename -> rewritten content
    total_renames = 0

    for cf in c_files:
        prefix = c_file_to_prefix[cf]
        with open(os.path.join(c_dir, cf), 'r') as f:
            content = f.read()

        local_funcs = c_module_funcs.get(prefix, set())
        import_map = per_module_import_map.get(prefix, {})

        rewritten = rewrite_c_file(
            content, prefix, local_funcs, import_map, c_global_registry
        )
        rewritten_files[cf] = rewritten

    # ========== Phase 5: Write rewritten C files ==========
    output_dir = output_path + '.d'
    os.makedirs(output_dir, exist_ok=True)
    print(f"\n[5/6] Writing rewritten C files to {output_dir}...")

    # Write each rewritten file to output directory
    for cf in c_files:
        content = rewritten_files[cf]
        outfile = os.path.join(output_dir, cf)
        with open(outfile, 'w') as f:
            f.write(content)

    # Write entry point file
    if entry_module:
        entry_file = os.path.join(output_dir, '_entry.c')
        with open(entry_file, 'w') as f:
            f.write("/* Bootstrap entry point */\n")
            f.write("#include <stdint.h>\n")
            f.write(f"extern int64_t {entry_module}__simple_main();\n")
            f.write(f"int main(int argc, char** argv) {{\n")
            f.write(f"    return (int){entry_module}__simple_main();\n")
            f.write(f"}}\n")

    # Also write a merged version for convenience
    print(f"  Also generating merged file: {output_path}")
    with open(output_path, 'w') as out:
        out.write("/* Generated by Simple Bootstrap Project Linker */\n")
        out.write("#include <stdint.h>\n#include <stdlib.h>\n#include <string.h>\n#include <math.h>\n\n")

        # Runtime declarations
        if c_files:
            first_content = rewritten_files[c_files[0]]
            for line in first_content.split('\n'):
                if line.startswith('extern ') and ('rt_' in line or 'doctest_' in line or 'simple_contract' in line):
                    out.write(line + '\n')
        out.write('\n')

        out.write("static int64_t __bootstrap_lambda_stub(void) { return 0; }\n\n")

        # Forward declarations with () for cross-module compat
        all_func_names = {}
        for cf in c_files:
            content = rewritten_files[cf]
            for line in content.split('\n'):
                m = re.match(r'^(int64_t|void)\s+(\w+)\s*\(', line)
                if m and not line.strip().endswith(';'):
                    ret_type = m.group(1)
                    func_name = m.group(2)
                    if func_name != 'main':
                        if func_name not in all_func_names or ret_type == 'int64_t':
                            all_func_names[func_name] = ret_type

        for func_name in sorted(all_func_names.keys()):
            out.write(f'{all_func_names[func_name]} {func_name}();\n')
        out.write('\n')

        # Function bodies
        for cf in c_files:
            prefix = c_file_to_prefix[cf]
            content = rewritten_files[cf]
            out.write(f"\n/* Module: {prefix} */\n")
            skip_main = False
            for line in content.split('\n'):
                if line.startswith('#include') or line.startswith('extern '):
                    continue
                if line.startswith('int main('):
                    skip_main = True; continue
                if skip_main:
                    if line.strip() == '}': skip_main = False
                    continue
                if re.match(r'^(?:int64_t|void)\s+\w+\s*\([^)]*\);$', line):
                    continue
                if line.strip() in ('/* Forward declarations */', '/* String constants */', '/* Entry point */'):
                    continue
                if 'static int64_t __bootstrap_lambda_stub' in line:
                    continue
                out.write(line + '\n')

        if entry_module:
            out.write(f"\nint main(int argc, char** argv) {{ return (int){entry_module}__simple_main(); }}\n")

        file_size = out.tell()

    print(f"  Merged file size: {file_size:,} bytes ({file_size/1024/1024:.1f} MB)")
    print(f"  Individual files: {output_dir}/ ({len(c_files)} files)")

    # ========== Phase 6: Summary ==========
    print(f"\n[6/6] Summary:")
    total_funcs = sum(len(funcs) for funcs in c_module_funcs.values())
    print(f"  Modules: {len(c_files)}")
    print(f"  Total functions: {total_funcs}")
    print(f"  Import resolutions: {resolved_count}")
    print(f"  Unresolved imports: {unresolved_count}")
    print(f"  Output: {output_path}")

    if entry_module:
        print(f"  Entry: {entry_module}__simple_main()")
    else:
        print(f"  No entry point (use --entry=<module_prefix>)")

    print(f"\nTo compile:")
    print(f"  clang -O2 -std=gnu89 -w {output_path} src/runtime/runtime.c src/runtime/runtime_memtrack.c -I src/runtime -o bootstrap_compiler -lm -lpthread")


if __name__ == '__main__':
    main()
