#!/usr/bin/env python3
"""check-rt-c-contract-compile.py: R2 C-side compile evidence for rt_ externs, current host only.

For each C translation unit named by --tu (default: src/runtime/runtime_simd_dispatch.c, then
every src/runtime TU that includes runtime_nonnull.h), the extern records that
rt-binding-index.py scans (reused via its build(), not re-implemented) are turned into C
prototypes. The prototypes go into a temporary header that is force-included with -include,
and the TU is compiled with cc -fsyntax-only. The compiler then proves or disproves each
scanned signature against the TU's own definition.

Per (symbol, signature) row, compile is one of:
  PASS      the TU compiles with the prototype in place, and the symbol is defined in the
            TU's preprocessed text on this host.
  FAIL      with the prototype in place the compiler names the symbol in an error, and a run
            with that one prototype alone reproduces the error naming it. reason=prototype-rejected.
  UNTESTED  anything else, with the reason: tu-baseline-failed (the TU does not preprocess or
            compile without the prototypes, e.g. a missing system header), tu-missing,
            not-defined-on-host (defined only behind a preprocessor branch that is off here),
            unmapped-spl-type:T (no single C ABI type for T: generics, tuples, unknown names),
            unattributed-error (an error that cannot be pinned to a symbol, so the
            rest of the batch stays UNTESTED).
Rows are per (symbol, .spl signature, .spl file). Two .spl files that declare one symbol
differently are two rows, each tested against the C definition.

Scope: this host only (cc and preprocessor conditions as they are here). Compile evidence
only: link is never tested here, and parameters are checked only through the C prototype.
Mapped types: i8..i64, u8..u64 to the stdint typedefs, f32/f64 to float/double, bool to bool,
void as a return. Handles cross the seed codegen's i64-everything extern ABI as one tagged
int64_t: text (except the (ptr, len) pairs listed for the symbol in text_extern_abi.spl, which
become const uint8_t* + uint64_t), [T] arrays, T? optionals, Vec* SIMD values, and class/struct/
enum names declared under src/. A scalar alias (type X = i64) takes its target's C type. Tuples,
generic T, and unlisted names stay UNTESTED. A C pointer-typed definition (const char*, SplArray*)
against an int64_t handle is a real mismatch and reports FAIL; the checker never adapts to it.
Run on demand, not wired into CI.

Exit codes: 0 rows produced (FAIL rows do not change the exit), 2 nothing checked,
1 selftest failure. The last stdout line is the summary.
Usage: check-rt-c-contract-compile.py [--root DIR] [--tu PATH]... [--cc CMD] [--selftest]
"""
import importlib.util
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '../..'))
RT_DIR = 'src/runtime'
FIRST_TU = 'src/runtime/runtime_simd_dispatch.c'
SCALAR = {
    'i8': 'int8_t', 'i16': 'int16_t', 'i32': 'int32_t', 'i64': 'int64_t',
    'u8': 'uint8_t', 'u16': 'uint16_t', 'u32': 'uint32_t', 'u64': 'uint64_t',
    'f32': 'float', 'f64': 'double', 'bool': 'bool',
}
NONNULL_INCLUDE = re.compile(r'#\s*include\s*"runtime_nonnull\.h"')
SIG = re.compile(r'^\((.*)\) -> (.+)$')
NOMINAL_DECL = re.compile(r'^[ \t]*(?:pub[ \t]+)?(?:class|struct|enum)[ \t]+([A-Za-z_]\w*)', re.M)
ALIAS_DECL = re.compile(r'^[ \t]*(?:pub[ \t]+)?type[ \t]+([A-Za-z_]\w*)[ \t]*=[ \t]*([A-Za-z_]\w*)[ \t]*$', re.M)
VEC_TYPE = re.compile(r'^Vec\d+[fdiu]\d*$')


TEXT_ABI_SPL = 'src/compiler/50.mir/text_extern_abi.spl'
TEXT_CASE = re.compile(r'case\s+((?:"[^"\n]*"\s*\|?\s*)+):\s*(?:#[^\n]*\n\s*)*return\s+Some\(\[([0-9,\s]*)\]\)')
NAME = re.compile(r'"([^"\n]*)"')


def text_split_table(root):
    """symbol -> param indices passed as (ptr, len). Read from the Simple table that mirrors the
    compiler's text_arg_indices (text_extern_abi.spl), the same source the backends use."""
    path = os.path.join(root, TEXT_ABI_SPL)
    if not os.path.isfile(path):
        return {}
    with open(path, encoding='utf-8', errors='replace') as f:
        body = f.read()
    out = {}
    for m in TEXT_CASE.finditer(body):
        idx = tuple(int(x) for x in m[2].replace(' ', '').split(',') if x)
        for name in NAME.findall(m[1]):
            out[name] = idx
    return out


def load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, rel))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


IX = load('rt_binding_index', 'rt-binding-index.py')
HM = IX.load('check_rt_host_map', 'check-rt-host-map.py')
PM = IX.load('check_rt_pointer_ref_map', 'check-rt-pointer-ref-map.py')


def run(argv):
    try:
        p = subprocess.run(argv, capture_output=True, text=True, timeout=300)
        return p.returncode, p.stdout + p.stderr
    except (OSError, subprocess.TimeoutExpired) as e:
        return 127, str(e)


def first_error(text):
    for line in text.splitlines():
        if 'error' in line:
            return line.strip()[:240]
    lines = text.strip().splitlines()
    return (lines[0] if lines else '<no output>')[:240]


def names_symbol(text, sym):
    return any(("'%s'" % sym) in line for line in text.splitlines() if 'error' in line)


def parse_sig(sig):
    m = SIG.match(sig)
    params = [p.strip() for p in m[1].split(',')] if m[1].strip() else []
    return params, m[2].strip()


def c_type(t, types):
    """C spelling of one .spl type, or None when no single C type is the real ABI.

    Scalars map to their stdint/float spelling. Every other value that the seed codegen passes
    as a tagged RuntimeValue crosses as int64_t: text (default ABI), arrays [T], optionals T?,
    SIMD vectors (Vec4f, Vec16u8, ...), and nominal class/struct/enum refs. Scalar aliases
    (type X = i64) resolve to their target. Tuples, generics and anything undeclared stay None.
    """
    if t in SCALAR:
        return SCALAR[t]
    if t in types.alias:
        return SCALAR[types.alias[t]]
    if t == 'text' or types.is_handle(t):
        return 'int64_t'
    if t.endswith('?') and c_type(t[:-1], types):
        return 'int64_t'  # nullable: a tagged RuntimeValue, nil included
    return None


def unmapped(params, ret, types):
    for t in params:
        if c_type(t, types) is None:
            return t
    if ret != 'void' and c_type(ret, types) is None:
        return ret
    return None


def prototype(sym, params, ret, types, split):
    """One C prototype. A text parameter listed in the text ABI table for sym is a raw
    (const uint8_t* ptr, uint64_t len) pair; every other text is one tagged int64_t."""
    ret_c = 'void' if ret == 'void' else c_type(ret, types)
    ps = []
    for i, p in enumerate(params):
        if p == 'text' and i in split.get(sym, ()):
            ps.extend(['const uint8_t*', 'uint64_t'])
        else:
            ps.append(c_type(p, types))
    return '%s %s(%s);' % (ret_c, sym, ', '.join(ps) if ps else 'void')


class TypeNames:
    """Nominal reference types and scalar aliases declared anywhere under src/*.spl."""

    def __init__(self, root):
        self.alias = {}
        self.nominal = set()
        base = os.path.join(root, 'src')
        for dirpath, _, names in os.walk(base):
            for name in names:
                if not name.endswith('.spl'):
                    continue
                with open(os.path.join(dirpath, name), encoding='utf-8', errors='replace') as f:
                    text = f.read()
                self.nominal.update(m[1] for m in NOMINAL_DECL.finditer(text))
                for m in ALIAS_DECL.finditer(text):
                    if m[2] in SCALAR:
                        self.alias[m[1]] = m[2]
        # A name that is both an alias and a nominal decl is ambiguous: not mapped.
        for name in list(self.alias):
            if name in self.nominal:
                del self.alias[name]
                self.nominal.discard(name)

    def is_handle(self, t):
        if t.startswith('[') and t.endswith(']') and len(t) > 2:
            return True
        if VEC_TYPE.match(t):
            return True
        return t in self.nominal


def cc_argv(cc, rt_dir):
    return shlex.split(cc) + ['-std=gnu11', '-I', rt_dir]


def defined_symbols(text):
    return {m[1] for m in HM.DEF.finditer(PM.ATTR.sub('', text))}


def judge_tu(root, cc, tu_rel, by_sym, types, split):
    """Rows for one TU. Each row: symbol, sig, spl, tu, compile, reason, diag."""
    rt_dir = os.path.join(root, RT_DIR)
    tu_abs = os.path.join(root, tu_rel)
    rows = []

    def row(sym, sig, spl, compile_v, reason, diag=''):
        rows.append({'symbol': sym, 'sig': sig, 'spl': spl, 'tu': tu_rel,
                     'compile': compile_v, 'reason': reason, 'diag': diag})

    defined = raw_defs(tu_abs)
    cands = [s for s in sorted(by_sym) if s in defined]
    if not os.path.isfile(tu_abs):
        base_fail = 'tu-missing'
    else:
        base_fail = None
        rc, pp = run(cc_argv(cc, rt_dir) + ['-E', tu_abs])
        if rc != 0:
            base_fail = 'tu-baseline-failed: ' + first_error(pp)
        else:
            rc, out = run(cc_argv(cc, rt_dir) + ['-fsyntax-only', tu_abs])
            if rc != 0:
                base_fail = 'tu-baseline-failed: ' + first_error(out)
    if base_fail:
        for s in cands:
            for sig, spl in by_sym[s]:
                row(s, sig, spl, 'UNTESTED', base_fail)
        return rows

    active = defined_symbols(pp)
    testable = {}  # (symbol, sig) -> (prototype, [spl paths])
    for s in cands:
        for sig, spl in sorted(by_sym[s]):
            params, ret = parse_sig(sig)
            bad = unmapped(params, ret, types)
            if bad:
                row(s, sig, spl, 'UNTESTED', 'unmapped-spl-type:%s' % bad)
            elif s not in active:
                row(s, sig, spl, 'UNTESTED', 'not-defined-on-host')
            else:
                proto = prototype(s, params, ret, types, split)
                testable.setdefault((s, sig), (proto, []))[1].append(spl)

    # Each symbol's k-th distinct testable signature goes in pass k, so one header never
    # holds two prototypes for one symbol. Conflicting .spl declarations are each tested.
    rank = {}
    for s in sorted({k[0] for k in testable}):
        for k, sig in enumerate(sorted(sig for t, sig in testable if t == s)):
            rank[(s, sig)] = k
    for k in range(max(rank.values(), default=-1) + 1):
        keys = sorted(key for key in testable if rank[key] == k)
        results = judge_protos(cc, rt_dir, tu_abs, {s: testable[(s, sig)][0] for s, sig in keys})
        for s, sig in keys:
            verdict, diag = results[s]
            for spl in sorted(testable[(s, sig)][1]):
                if verdict == 'PASS':
                    row(s, sig, spl, 'PASS', 'compiles-with-prototype')
                elif verdict == 'FAIL':
                    row(s, sig, spl, 'FAIL', 'prototype-rejected', diag)
                else:
                    row(s, sig, spl, 'UNTESTED', diag)
    return rows


def raw_defs(tu_abs):
    if not os.path.isfile(tu_abs):
        return set()
    with open(tu_abs, encoding='utf-8', errors='replace') as f:
        return defined_symbols(PM.NOISE.sub(' ', f.read()))


def compile_with(cc, rt_dir, tu_abs, protos, tmp):
    hdr = os.path.join(tmp, 'rt_c_contract_%d.h' % len(os.listdir(tmp)))
    with open(hdr, 'w') as f:
        f.write('/* generated by check-rt-c-contract-compile.py from .spl extern signatures */\n')
        f.write('#include <stdint.h>\n#include <stddef.h>\n#include <stdbool.h>\n')
        for s in sorted(protos):
            f.write(protos[s] + '\n')
    return run(cc_argv(cc, rt_dir) + ['-fsyntax-only', '-include', hdr, tu_abs])


def judge_protos(cc, rt_dir, tu_abs, protos):
    """symbol -> (PASS|FAIL|UNTESTED, diag). Batch first; every FAIL is confirmed alone."""
    results = {}
    remaining = dict(protos)
    tmp = tempfile.mkdtemp(prefix='rt_c_contract_')
    try:
        while remaining:
            rc, err = compile_with(cc, rt_dir, tu_abs, remaining, tmp)
            if rc == 0:
                for s in remaining:
                    results[s] = ('PASS', '')
                break
            named = [s for s in sorted(remaining) if names_symbol(err, s)]
            if not named:
                for s in remaining:
                    results[s] = ('UNTESTED', 'unattributed-error: ' + first_error(err))
                break
            for s in named:
                rc1, err1 = compile_with(cc, rt_dir, tu_abs, {s: remaining[s]}, tmp)
                if rc1 != 0 and names_symbol(err1, s):
                    results[s] = ('FAIL', first_error(err1))
                else:
                    results[s] = ('UNTESTED', 'unconfirmed-batch-error: ' + first_error(err))
            remaining = {s: p for s, p in remaining.items() if s not in named}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return results


def index_by_symbol(root):
    doc = IX.build(root)
    by = {}
    for r in doc['records']:
        by.setdefault(r['symbol'], set()).add((r['signature'], r['path']))
    return by, len(doc['records'])


def check(root, tus, cc):
    by_sym, nrec = index_by_symbol(root)
    types = TypeNames(root)
    split = text_split_table(root)
    rows = []
    for tu in tus:
        rows.extend(judge_tu(root, cc, tu, by_sym, types, split))
    rows.sort(key=lambda r: (r['tu'], r['symbol'], r['sig']))
    return rows, nrec


def tally(rows):
    t = {'PASS': 0, 'FAIL': 0, 'UNTESTED': 0}
    for r in rows:
        t[r['compile']] += 1
    return t


def default_tus(root):
    rt = os.path.join(root, RT_DIR)
    out = [FIRST_TU]
    for name in sorted(os.listdir(rt)):
        rel = os.path.join(RT_DIR, name)
        if name.endswith('.c') and rel != FIRST_TU:
            with open(os.path.join(rt, name), encoding='utf-8', errors='replace') as f:
                if NONNULL_INCLUDE.search(f.read()):
                    out.append(rel)
    return out


def host_line(cc):
    rc, out = run(shlex.split(cc) + ['--version'])
    first = out.strip().splitlines()[0] if rc == 0 and out.strip() else 'unavailable'
    return 'RT_C_CONTRACT_HOST os=%s arch=%s cc=%s' % (platform.system(), platform.machine(), first)


def selftest():
    def tree(files):
        t = tempfile.mkdtemp(prefix='rt_c_contract_st_')
        for rel, body in files.items():
            p = os.path.join(t, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, 'w') as f:
                f.write(body)
        return t

    spl = ('extern fn rt_good(a: i64) -> i64\n'
           'extern fn rt_flag() -> bool\n'
           'extern fn rt_wrong(a: i64) -> f64\n'
           'extern fn rt_win_only() -> i64\n'
           'extern fn rt_textual(s: text) -> i64\n'
           'extern fn rt_dup(a: i64) -> i64\n'
           'extern fn rt_split(s: text, n: i64) -> i64\n'
           'extern fn rt_split_wrong(s: text, n: i64) -> i64\n'
           'extern fn rt_arr(a: [u8]) -> i64\n'
           'extern fn rt_opt(a: i64) -> i64?\n'
           'extern fn rt_vec(v: Vec4f) -> Vec4f\n'
           'extern fn rt_obj(w: Widget) -> i64\n'
           'extern fn rt_alias(h: Handle) -> i64\n'
           'extern fn rt_tuple(t: (i64, i64)) -> i64\n'
           'extern fn rt_generic(x: T) -> i64\n')
    spl_b = 'extern fn rt_dup(a: i64) -> f64\n'
    types_spl = ('class Widget:\n    id: i64\n'
                 'type Handle = i64\n')
    table_spl = ('fn text_arg_indices(func_name: text) -> [i64]?:\n'
                 '    match func_name:\n'
                 '        case "rt_split" | "rt_split_wrong":\n'
                 '            return Some([0])\n'
                 '        case _:\n'
                 '            return None\n')
    good_c = (
        '#include <stdint.h>\n#include <stdbool.h>\n#include <stddef.h>\n'
        'int64_t rt_good(int64_t a) { return a; }\n'
        'bool rt_flag(void) { return true; }\n'
        'int64_t rt_wrong(int64_t a) { return a; }\n'
        '#ifdef _WIN32\nint64_t rt_win_only(void) { return 1; }\n#endif\n'
        'int64_t rt_textual(int64_t v) { return v; }\n'
        'int64_t rt_dup(int64_t a) { return a; }\n'
        'int64_t rt_split(const uint8_t* p, uint64_t len, int64_t n) { return n + (int64_t)len + p[0]; }\n'
        'int64_t rt_split_wrong(int64_t s, int64_t n) { return s + n; }\n'
        'int64_t rt_arr(int64_t a) { return a; }\n'
        'int64_t rt_opt(int64_t a) { return a; }\n'
        'int64_t rt_vec(int64_t v) { return v; }\n'
        'int64_t rt_obj(int64_t w) { return w; }\n'
        'int64_t rt_alias(int64_t h) { return h; }\n'
        'int64_t rt_tuple(int64_t t) { return t; }\n'
        'int64_t rt_generic(int64_t x) { return x; }\n')
    broken_c = (
        '#include "no_such_rt_header_for_selftest.h"\n'
        'int64_t rt_broken(int64_t a) { return a; }\n')
    broken_spl = 'extern fn rt_broken(a: i64) -> i64\n'

    fails = []

    def want(rows, sym, compile_v, reason_prefix):
        got = [r for r in rows if r['symbol'] == sym]
        if len(got) != 1:
            fails.append('%d rows for %s, wanted 1' % (len(got), sym))
            return
        r = got[0]
        if r['compile'] != compile_v or not r['reason'].startswith(reason_prefix):
            fails.append('%s compile=%s reason=%s, wanted %s %s' % (
                sym, r['compile'], r['reason'], compile_v, reason_prefix))

    root = tree({'src/runtime/good.c': good_c, 'src/lib/a.spl': spl, 'src/lib/b.spl': spl_b,
                 'src/lib/types.spl': types_spl,
                 'src/compiler/50.mir/text_extern_abi.spl': table_spl})
    try:
        rows, _ = check(root, ['src/runtime/good.c'], 'cc')
        want(rows, 'rt_good', 'PASS', 'compiles-with-prototype')
        want(rows, 'rt_flag', 'PASS', 'compiles-with-prototype')
        want(rows, 'rt_wrong', 'FAIL', 'prototype-rejected')
        want(rows, 'rt_win_only', 'UNTESTED', 'not-defined-on-host')
        # text is one tagged int64_t by default; a text-ABI row splits into (ptr, len).
        want(rows, 'rt_textual', 'PASS', 'compiles-with-prototype')
        want(rows, 'rt_split', 'PASS', 'compiles-with-prototype')
        want(rows, 'rt_split_wrong', 'FAIL', 'prototype-rejected')
        # Arrays, optionals, SIMD vectors, declared classes and scalar aliases are int64 handles.
        want(rows, 'rt_arr', 'PASS', 'compiles-with-prototype')
        want(rows, 'rt_opt', 'PASS', 'compiles-with-prototype')
        want(rows, 'rt_vec', 'PASS', 'compiles-with-prototype')
        want(rows, 'rt_obj', 'PASS', 'compiles-with-prototype')
        want(rows, 'rt_alias', 'PASS', 'compiles-with-prototype')
        # Tuples and bare generic parameters have no single C ABI type: never guessed.
        want(rows, 'rt_tuple', 'UNTESTED', 'unmapped-spl-type:')
        want(rows, 'rt_generic', 'UNTESTED', 'unmapped-spl-type:T')
        dup = {(r['sig'], r['spl'].rsplit('/', 1)[-1]): r['compile'] for r in rows if r['symbol'] == 'rt_dup'}
        if dup != {('(i64) -> i64', 'a.spl'): 'PASS', ('(i64) -> f64', 'b.spl'): 'FAIL'}:
            fails.append('rt_dup rows %s, wanted a.spl PASS and b.spl FAIL' % sorted(dup.items()))
        wrong = [r for r in rows if r['symbol'] == 'rt_wrong']
        if wrong and 'rt_wrong' not in wrong[0]['diag']:
            fails.append('rt_wrong FAIL diagnostic does not name the symbol')
        # The compiler being unavailable must never produce PASS.
        rows_nocc, _ = check(root, ['src/runtime/good.c'], 'false')
        if any(r['compile'] == 'PASS' for r in rows_nocc):
            fails.append('PASS reported with a failing compiler')
        if not rows_nocc or any(not r['reason'].startswith('tu-baseline-failed') for r in rows_nocc):
            fails.append('failing compiler did not mark every row tu-baseline-failed')
    finally:
        shutil.rmtree(root, ignore_errors=True)

    root = tree({'src/runtime/broken.c': broken_c, 'src/lib/b.spl': broken_spl})
    try:
        rows, _ = check(root, ['src/runtime/broken.c'], 'cc')
        if not rows:
            fails.append('broken TU produced no rows')
        if any(r['compile'] == 'PASS' for r in rows):
            fails.append('PASS reported for a TU that does not compile')
        if any(not r['reason'].startswith('tu-baseline-failed') for r in rows):
            fails.append('broken TU rows are not tu-baseline-failed')
    finally:
        shutil.rmtree(root, ignore_errors=True)

    if fails:
        for f in fails:
            print('SELFTEST FAIL: ' + f)
        print('ERROR — selftest %d failure(s)' % len(fails))
        return 1
    print('PASS — selftest: PASS, FAIL (wrong prototype, wrong text-ABI split), UNTESTED (ifdef, tuple, '
          'bare generic, broken TU, failing cc) all as expected; text, arrays, optionals, vectors, '
          'declared classes and aliases map to their C ABI')
    return 0


def main():
    a = sys.argv[1:]
    if '--selftest' in a:
        return selftest()
    root = os.path.abspath(a[a.index('--root') + 1]) if '--root' in a else ROOT
    cc = a[a.index('--cc') + 1] if '--cc' in a else 'cc'
    tus = [a[i + 1] for i, x in enumerate(a) if x == '--tu' and i + 1 < len(a)]
    if not tus:
        tus = default_tus(root)
    print(host_line(cc))
    rows, nrec = check(root, tus, cc)
    for r in rows:
        line = 'RT_C_CONTRACT compile=%s symbol=%s sig=%s spl=%s tu=%s reason=%s' % (
            r['compile'], r['symbol'], r['sig'].replace(' ', ''), r['spl'], r['tu'], r['reason'])
        if r['diag']:
            line += ' diag=' + r['diag']
        print(line)
    t = tally(rows)
    print('RT_C_CONTRACT_COMPILE tus=%d spl_records=%d rows=%d compile=PASS:%d/FAIL:%d/UNTESTED:%d link=UNTESTED' % (
        len(tus), nrec, len(rows), t['PASS'], t['FAIL'], t['UNTESTED']))
    if not rows:
        print('ERROR — nothing was checked (0 rows)')
        return 2
    return 0


if __name__ == '__main__':
    sys.exit(main())
