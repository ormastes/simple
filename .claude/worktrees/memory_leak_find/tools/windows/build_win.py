#!/usr/bin/env python3
"""
Windows build script: Transpile compiler with core2 (self-hosted core compiler).

Usage:
    python src/compiler_core_win/build_win.py

Pipeline:
    1. Collect compiler .spl files (with exclusions)
    2. Desugar lambdas, optional chaining, bitwise ops
    3. Transpile with core2_new.exe
    4. Post-process C++ (fix_cpp.py)
    5. Compile with g++
"""

import os
import re
import sys
import shutil
import subprocess
import tempfile

IS_WINDOWS = sys.platform == 'win32'

# === Configuration ===
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
SRC = os.path.join(ROOT, 'src', 'compiler')
SHIM = os.path.join(ROOT, 'src', 'compiler_core_win', 'ffi_shim.spl')
CORE2 = os.path.join(ROOT, 'build', 'bootstrap', 'core2_new.exe')
OUTDIR = os.path.join(ROOT, 'build', 'bootstrap')
SEED_DIR = os.path.join(ROOT, 'src', 'compiler_seed')
RUNTIME_LIB = os.path.join(ROOT, 'build', 'seed', 'libspl_runtime.a')

RAW_CPP = os.path.join(OUTDIR, 'cc_v2_raw.cpp')
FIXED_CPP = os.path.join(OUTDIR, 'cc_v2_fixed.cpp')
STUBBED_CPP = os.path.join(OUTDIR, 'cc_v2_stubbed.cpp')
ERROR_LOG = os.path.join(OUTDIR, 'cc_v2_errors.log')
COMPILE_LOG = os.path.join(OUTDIR, 'cc_v2_compile.log')
OUTPUT_EXE = os.path.join(OUTDIR, 'compiler_v2.exe')

# Excluded directories and file patterns
EXCLUDE_DIRS = {
    'test', 'test_pkg', 'blocks', 'baremetal', 'treesitter',
    'borrow_check', 'gc_analysis', 'irdsl', 'macro_check', 'weaving',
}

EXCLUDE_SUBDIRS = {
    'backend/cuda', 'backend/vulkan', 'backend/native',
}

EXCLUDE_PREFIXES = [
    'test_', 'backend/lean_', 'backend/wasm_',
    'bidir_phase', 'aop_proceed',
    'dim_constraints',
]

EXCLUDE_FILES = {
    'aop.spl', 'coverage.spl', 'smf_writer_test.spl',
}

# Type definition files that should come early
TYPE_FILES = [
    'ast.spl', 'hir.spl', 'hir_types.spl', 'hir_definitions.spl',
    'mir.spl', 'mir_data.spl', 'lexer_types.spl', 'parser_types.spl',
    'backend_types.spl', 'driver_types.spl', 'error.spl', 'error_codes.spl',
    'config.spl', 'traits.spl', 'type_infer_types.spl',
]


def should_exclude(rel_path):
    """Check if a file should be excluded from the build."""
    parts = rel_path.replace('\\', '/').split('/')
    basename = parts[-1]

    # Check excluded directories
    for part in parts[:-1]:
        if part in EXCLUDE_DIRS:
            return True

    # Check excluded subdirectories
    rel_dir = '/'.join(parts[:-1])
    for excl_sub in EXCLUDE_SUBDIRS:
        if rel_dir.startswith(excl_sub):
            return True

    # Check excluded prefixes
    for prefix in EXCLUDE_PREFIXES:
        if '/' in prefix:
            if rel_path.replace('\\', '/').startswith(prefix):
                return True
        else:
            if basename.startswith(prefix):
                return True

    # Check excluded files
    if basename in EXCLUDE_FILES:
        return True

    return False


def collect_files():
    """Collect all .spl files in dependency order."""
    files = []
    added = set()

    # 1. FFI shim first
    files.append(SHIM)
    added.add(os.path.normpath(SHIM))

    # 2. __init__.spl files
    init_files = []
    for dirpath, dirnames, filenames in os.walk(SRC):
        for fname in filenames:
            if fname == '__init__.spl':
                full = os.path.join(dirpath, fname)
                rel = os.path.relpath(full, SRC).replace('\\', '/')
                if not should_exclude(rel):
                    init_files.append(full)
    init_files.sort()
    for f in init_files:
        norm = os.path.normpath(f)
        if norm not in added:
            files.append(f)
            added.add(norm)

    # 3. Type definition files
    for tf in TYPE_FILES:
        full = os.path.join(SRC, tf)
        if os.path.isfile(full):
            norm = os.path.normpath(full)
            if norm not in added:
                files.append(full)
                added.add(norm)

    # 4. All other .spl files (sorted for determinism)
    all_spl = []
    for dirpath, dirnames, filenames in os.walk(SRC):
        for fname in sorted(filenames):
            if not fname.endswith('.spl'):
                continue
            full = os.path.join(dirpath, fname)
            rel = os.path.relpath(full, SRC).replace('\\', '/')
            if should_exclude(rel):
                continue
            norm = os.path.normpath(full)
            if norm not in added:
                all_spl.append(full)
                added.add(norm)
    all_spl.sort()
    files.extend(all_spl)

    return files


# === Desugaring ===

def desugar_lambda(line, indent_str):
    """Try to desugar a lambda expression on this line. Returns new lines or None."""
    stripped = line.rstrip('\n').rstrip()

    # Pattern 1: val x = items.map(\var: expr)
    m = re.match(r'^(\s*)(val|var)\s+(\w+)\s*=\s*(.+?)\.map\(\\(\w+):\s*(.+?)\)(.*)$', stripped)
    if m:
        ind, kw, varname, collection, param, expr, rest = m.groups()
        tmp = f"__{varname}_list"
        new_lines = []
        new_lines.append(f"{ind}var {tmp}: [text] = []\n")
        new_lines.append(f"{ind}for {param} in {collection}:\n")
        new_lines.append(f"{ind}    {tmp}.push({expr})\n")
        new_lines.append(f"{ind}{kw} {varname} = {tmp}{rest}\n")
        return new_lines

    # Pattern 2: val x = name_map(items, \var: expr)
    m = re.match(r'^(\s*)(val|var)\s+(\w+)\s*=\s*(\w+_map)\((\w+),\s*\\(\w+):\s*(.+?)\)(.*)$', stripped)
    if m:
        ind, kw, varname, fn_name, collection, param, expr, rest = m.groups()
        tmp = f"__{varname}_list"
        new_lines = []
        new_lines.append(f"{ind}var {tmp} = []\n")
        new_lines.append(f"{ind}for {param} in {collection}:\n")
        new_lines.append(f"{ind}    {tmp}.push({expr})\n")
        new_lines.append(f"{ind}{kw} {varname} = {tmp}{rest}\n")
        return new_lines

    # Pattern 3: val x = items.filter(\var: cond)
    m = re.match(r'^(\s*)(val|var)\s+(\w+)\s*=\s*(.+?)\.filter\(\\(\w+):\s*(.+?)\)(.*)$', stripped)
    if m:
        ind, kw, varname, collection, param, cond, rest = m.groups()
        tmp = f"__{varname}_list"
        new_lines = []
        new_lines.append(f"{ind}var {tmp} = []\n")
        new_lines.append(f"{ind}for {param} in {collection}:\n")
        new_lines.append(f"{ind}    if {cond}:\n")
        new_lines.append(f"{ind}        {tmp}.push({param})\n")
        new_lines.append(f"{ind}{kw} {varname} = {tmp}{rest}\n")
        return new_lines

    # Pattern 4: val x = name_filter(items, \var: cond)
    m = re.match(r'^(\s*)(val|var)\s+(\w+)\s*=\s*(\w+_filter)\((\w+),\s*\\(\w+):\s*(.+?)\)(.*)$', stripped)
    if m:
        ind, kw, varname, fn_name, collection, param, cond, rest = m.groups()
        tmp = f"__{varname}_list"
        new_lines = []
        new_lines.append(f"{ind}var {tmp} = []\n")
        new_lines.append(f"{ind}for {param} in {collection}:\n")
        new_lines.append(f"{ind}    if {cond}:\n")
        new_lines.append(f"{ind}        {tmp}.push({param})\n")
        new_lines.append(f"{ind}{kw} {varname} = {tmp}{rest}\n")
        return new_lines

    # Pattern 5: assignment: x = items.map(\var: expr)
    m = re.match(r'^(\s*)(\w[\w.]*)\s*=\s*(.+?)\.map\(\\(\w+):\s*(.+?)\)(.*)$', stripped)
    if m and 'val ' not in stripped[:20] and 'var ' not in stripped[:20]:
        ind, target, collection, param, expr, rest = m.groups()
        tmp = "__tmp_map"
        new_lines = []
        new_lines.append(f"{ind}var {tmp} = []\n")
        new_lines.append(f"{ind}for {param} in {collection}:\n")
        new_lines.append(f"{ind}    {tmp}.push({expr})\n")
        new_lines.append(f"{ind}{target} = {tmp}{rest}\n")
        return new_lines

    # Pattern 6: .any(\var: cond) -> loop with early return
    m = re.match(r'^(\s*)(val|var)\s+(\w+)\s*=\s*(.+?)\.any\(\\(\w+):\s*(.+?)\)(.*)$', stripped)
    if m:
        ind, kw, varname, collection, param, cond, rest = m.groups()
        new_lines = []
        new_lines.append(f"{ind}var {varname} = false\n")
        new_lines.append(f"{ind}for {param} in {collection}:\n")
        new_lines.append(f"{ind}    if {cond}:\n")
        new_lines.append(f"{ind}        {varname} = true\n")
        return new_lines

    # Pattern 7: .find(\var: cond) -> loop
    m = re.match(r'^(\s*)(val|var)\s+(\w+)\s*=\s*(.+?)\.find\(\\(\w+):\s*(.+?)\)(.*)$', stripped)
    if m:
        ind, kw, varname, collection, param, cond, rest = m.groups()
        new_lines = []
        new_lines.append(f"{ind}var {varname} = nil\n")
        new_lines.append(f"{ind}for {param} in {collection}:\n")
        new_lines.append(f"{ind}    if {cond}:\n")
        new_lines.append(f"{ind}        {varname} = {param}\n")
        return new_lines

    return None


def in_string_context(line):
    """Check if ALL backslashes in the line are inside string literals."""
    in_str = False
    i = 0
    while i < len(line):
        if line[i] == '"' and (i == 0 or line[i-1] != '\\'):
            in_str = not in_str
        elif line[i] == '\\' and not in_str and i + 1 < len(line) and line[i+1].isalpha():
            return False
        i += 1
    return True


def desugar_optional_chaining(line):
    """Replace obj.?field with explicit nil check pattern.
    For simple cases in expressions, replace .? with .
    (the object will be nil-checked at a higher level or the C++ will handle it)."""
    if '.?' not in line:
        return line
    # Simple approach: replace .? with . (C++ will use null pointer which we handle in fix_cpp)
    # More robust approach would require multi-line rewriting
    return line.replace('.?', '.')


def desugar_bitwise(line):
    """Replace bitwise operators with function calls."""
    # Don't touch comments or strings
    stripped = line.lstrip()
    if stripped.startswith('#') or stripped.startswith('//'):
        return line

    # Replace ~expr with bitwise_not_i64(expr) - only when ~ is used as unary operator
    # Pattern: ~ followed by word or (
    line = re.sub(r'~(\w)', r'bitwise_not_i64(\1)', line)

    return line


def desugar_file(filepath):
    """Read a .spl file and apply all desugaring transformations."""
    if IS_WINDOWS:
        with open(filepath, 'r', encoding='utf-8', errors='replace', newline='') as f:
            content = f.read()
        # Normalize CRLF to LF so the core parser doesn't choke on \r
        content = content.replace('\r\n', '\n').replace('\r', '\n')
        lines = content.split('\n')
        lines = [line + '\n' for line in lines]
        if lines and lines[-1] == '\n':
            lines[-1] = ''
    else:
        with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
            lines = f.readlines()

    result = []
    changed = False
    in_docstring = False

    for line in lines:
        stripped = line.lstrip()

        # Track docstrings
        if stripped.startswith('"""') or stripped.startswith('r"""'):
            check = stripped[1:] if stripped.startswith('r') else stripped
            count = check.count('"""')
            if count == 1:
                in_docstring = not in_docstring
            result.append(line)
            continue

        if in_docstring:
            result.append(line)
            continue

        # Skip comments
        if stripped.startswith('#'):
            result.append(line)
            continue

        # Desugar lambdas
        if '\\' in line and not in_string_context(line):
            indent_str = ' ' * (len(line) - len(line.lstrip()))
            new_lines = desugar_lambda(line, indent_str)
            if new_lines is not None:
                result.extend(new_lines)
                changed = True
                continue

        # Desugar optional chaining
        if '.?' in line:
            line = desugar_optional_chaining(line)
            changed = True

        result.append(line)

    return result, changed


def prepare_desugared_files(file_list, tmp_dir):
    """Copy and desugar all files into a temp directory. Returns new file list."""
    new_files = []
    lambda_count = 0
    opt_chain_count = 0

    for filepath in file_list:
        # Keep paths relative and create in tmp_dir
        if filepath == SHIM:
            rel = 'ffi_shim.spl'
        else:
            rel = os.path.relpath(filepath, os.path.dirname(SRC))
        dst = os.path.join(tmp_dir, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)

        new_lines, changed = desugar_file(filepath)
        if changed:
            lambda_count += 1

        open_kwargs = {'encoding': 'utf-8'}
        if IS_WINDOWS:
            open_kwargs['newline'] = '\n'  # Force LF on Windows
        with open(dst, 'w', **open_kwargs) as f:
            f.writelines(new_lines)

        new_files.append(dst)

    print(f"  Desugared {lambda_count} files")
    return new_files


def test_parse_file(filepath):
    """Test if a single file parses without errors. Returns True if clean."""
    proc = subprocess.run(
        [CORE2, filepath],
        capture_output=True, timeout=30
    )
    # If stderr contains "error: parse errors", the file has issues
    stderr = proc.stderr.decode('utf-8', errors='replace')
    return 'error: parse errors' not in stderr


def filter_parseable_files(file_list):
    """Test each file individually and return only those that parse cleanly."""
    clean = []
    broken = []
    for i, f in enumerate(file_list):
        if (i + 1) % 50 == 0:
            print(f"    Testing {i+1}/{len(file_list)}...")
        try:
            if test_parse_file(f):
                clean.append(f)
            else:
                broken.append(os.path.basename(f))
        except subprocess.TimeoutExpired:
            broken.append(os.path.basename(f) + " (timeout)")
    print(f"  Clean: {len(clean)}, Broken: {len(broken)}")
    if broken:
        print(f"  Broken files: {', '.join(broken[:30])}")
        if len(broken) > 30:
            print(f"    ... and {len(broken) - 30} more")
    return clean


def transpile(file_list, output_cpp, error_log):
    """Run core2_new.exe on the file list."""
    cmd = [CORE2] + file_list
    print(f"  Running core2_new.exe with {len(file_list)} files...")

    with open(output_cpp, 'w', encoding='utf-8') as out_f, \
         open(error_log, 'w', encoding='utf-8') as err_f:
        proc = subprocess.run(cmd, stdout=out_f, stderr=err_f, timeout=300)

    # Report
    cpp_size = os.path.getsize(output_cpp)
    err_size = os.path.getsize(error_log) if os.path.exists(error_log) else 0
    print(f"  Output: {cpp_size:,} bytes ({output_cpp})")
    print(f"  Errors: {err_size:,} bytes ({error_log})")
    print(f"  Exit code: {proc.returncode}")

    if err_size > 0:
        with open(error_log, 'r', encoding='utf-8', errors='replace') as f:
            err_lines = f.readlines()
        # Show first 30 error lines
        print(f"  First errors:")
        for line in err_lines[:30]:
            print(f"    {line.rstrip()}")
        if len(err_lines) > 30:
            print(f"    ... ({len(err_lines)} total error lines)")

    return proc.returncode


def run_fix_cpp(input_cpp, output_cpp):
    """Run fix_cpp.py post-processor."""
    fix_script = os.path.join(ROOT, 'src', 'compiler_core_win', 'fix_cpp.py')
    print(f"  Running fix_cpp.py...")
    proc = subprocess.run(
        [sys.executable, fix_script, input_cpp, output_cpp],
        capture_output=True, text=True
    )
    print(proc.stdout)
    if proc.stderr:
        print(f"  fix_cpp errors: {proc.stderr[:500]}")
    return proc.returncode


def compile_cpp(input_cpp, output_exe, log_file):
    """Compile with g++."""
    cmd = [
        'g++', '-std=c++20', '-O2', '-fpermissive',
        f'-I{SEED_DIR}',
        input_cpp,
        RUNTIME_LIB,
        '-o', output_exe,
        '-Wl,--allow-multiple-definition',
        '-lm',
    ]
    print(f"  Compiling with g++...")
    with open(log_file, 'w', encoding='utf-8') as f:
        proc = subprocess.run(cmd, stderr=f, stdout=f, timeout=600)

    if proc.returncode == 0:
        print(f"  SUCCESS: {output_exe}")
    else:
        log_size = os.path.getsize(log_file)
        print(f"  FAILED (exit {proc.returncode}), errors in {log_file} ({log_size:,} bytes)")
        # Show first errors
        with open(log_file, 'r', encoding='utf-8', errors='replace') as f:
            lines = f.readlines()
        for line in lines[:30]:
            print(f"    {line.rstrip()}")
        if len(lines) > 30:
            print(f"    ... ({len(lines)} total lines)")

    return proc.returncode


def extract_error_lines(log_file):
    """Extract error line numbers from g++ error output."""
    error_lines = set()
    with open(log_file, 'r', encoding='utf-8', errors='replace') as f:
        for line in f:
            # Match patterns like "file.cpp:1234:56: error:"
            m = re.search(r':(\d+):\d+: error:', line)
            if m:
                error_lines.add(int(m.group(1)))
    return error_lines


def run_stub_broken(input_cpp, error_lines_file, output_cpp):
    """Run stub_broken.py to stub functions with compilation errors."""
    stub_script = os.path.join(ROOT, 'src', 'compiler_core_win', 'stub_broken.py')
    print(f"  Running stub_broken.py...")
    proc = subprocess.run(
        [sys.executable, stub_script, input_cpp, error_lines_file, output_cpp],
        capture_output=True, text=True
    )
    print(proc.stdout)
    if proc.stderr:
        print(f"  stub_broken errors: {proc.stderr[:500]}")
    return proc.returncode


def main():
    print("=" * 60)
    print("Building compiler with core2 (self-hosted core compiler)")
    print("=" * 60)

    # Check prerequisites
    if not os.path.isfile(CORE2):
        print(f"ERROR: core2_new.exe not found at {CORE2}")
        print("Run the bootstrap chain first (Phase 2)")
        sys.exit(1)

    if not os.path.isfile(RUNTIME_LIB):
        print(f"ERROR: libspl_runtime.a not found at {RUNTIME_LIB}")
        sys.exit(1)

    # Phase 1: Collect files
    print("\n[Phase 1] Collecting compiler files...")
    file_list = collect_files()
    print(f"  Found {len(file_list)} files")

    # Phase 2: Desugar
    print("\n[Phase 2] Desugaring (lambdas, optional chaining)...")
    tmp_dir = os.path.join(OUTDIR, '_desugared')
    if os.path.exists(tmp_dir):
        shutil.rmtree(tmp_dir)
    os.makedirs(tmp_dir, exist_ok=True)

    desugared_files = prepare_desugared_files(file_list, tmp_dir)

    # Phase 2b: Filter files that parse cleanly
    print("\n[Phase 2b] Testing which files parse cleanly...")
    clean_files = filter_parseable_files(desugared_files)

    if not clean_files:
        print("ERROR: No files parse cleanly!")
        sys.exit(1)

    # Phase 3: Transpile
    print(f"\n[Phase 3] Transpiling {len(clean_files)} clean files with core2_new.exe...")
    rc = transpile(clean_files, RAW_CPP, ERROR_LOG)

    raw_size = os.path.getsize(RAW_CPP) if os.path.exists(RAW_CPP) else 0
    if raw_size < 1000:
        print("ERROR: Transpilation produced very little output. Check errors.")
        sys.exit(1)

    # Phase 4: Fix C++
    print("\n[Phase 4] Post-processing C++...")
    run_fix_cpp(RAW_CPP, FIXED_CPP)

    # Phase 5: First compile attempt
    print("\n[Phase 5] Compiling (attempt 1)...")
    rc = compile_cpp(FIXED_CPP, OUTPUT_EXE, COMPILE_LOG)

    if rc == 0:
        print("\n" + "=" * 60)
        print("BUILD SUCCESSFUL!")
        print(f"Binary: {OUTPUT_EXE}")
        print("=" * 60)
        return

    # Phase 6: Stub broken functions and retry
    print("\n[Phase 6] Stubbing broken functions...")
    error_lines = extract_error_lines(COMPILE_LOG)
    if not error_lines:
        print("  No error lines extracted - cannot stub")
        sys.exit(1)

    error_lines_file = os.path.join(OUTDIR, 'cc_v2_error_lines.txt')
    with open(error_lines_file, 'w') as f:
        for line_no in sorted(error_lines):
            f.write(f"{line_no}\n")

    print(f"  Found {len(error_lines)} error lines")
    run_stub_broken(FIXED_CPP, error_lines_file, STUBBED_CPP)

    # Phase 7: Second compile attempt
    print("\n[Phase 7] Compiling (attempt 2, with stubs)...")
    compile_log2 = os.path.join(OUTDIR, 'cc_v2_compile2.log')
    rc = compile_cpp(STUBBED_CPP, OUTPUT_EXE, compile_log2)

    if rc == 0:
        print("\n" + "=" * 60)
        print("BUILD SUCCESSFUL (with stubs)!")
        print(f"Binary: {OUTPUT_EXE}")
        print("=" * 60)
        return

    # Phase 8: Second stub pass
    print("\n[Phase 8] Second stub pass...")
    error_lines2 = extract_error_lines(compile_log2)
    error_lines_file2 = os.path.join(OUTDIR, 'cc_v2_error_lines2.txt')
    with open(error_lines_file2, 'w') as f:
        for line_no in sorted(error_lines2):
            f.write(f"{line_no}\n")

    stubbed2_cpp = os.path.join(OUTDIR, 'cc_v2_stubbed2.cpp')
    run_stub_broken(STUBBED_CPP, error_lines_file2, stubbed2_cpp)

    compile_log3 = os.path.join(OUTDIR, 'cc_v2_compile3.log')
    rc = compile_cpp(stubbed2_cpp, OUTPUT_EXE, compile_log3)

    if rc == 0:
        print("\n" + "=" * 60)
        print("BUILD SUCCESSFUL (with double stubs)!")
        print(f"Binary: {OUTPUT_EXE}")
        print("=" * 60)
    else:
        print("\n" + "=" * 60)
        print("BUILD FAILED after 3 attempts")
        print(f"Check: {compile_log3}")
        print("=" * 60)
        sys.exit(1)


if __name__ == '__main__':
    main()
