#!/usr/bin/env python3
"""check-rt-pointer-ref-map.py: SRT004 pointer-return map, MAPPING evidence only.

Joins each C `T *rt_x(...)` definition under src/runtime to every `.spl`
`extern fn rt_x` declaration. This complements check-non-optional-nil-return.shs,
which derives nil-capability from the Rust interpreter, not from C bodies.

  narrow   pointer declared as a sub-pointer-width scalar (truncates). Never baselined.
  nil      a C body has a direct `return NULL`/`return 0` but the .spl managed
           return (text, [T], tuple) is non-optional. Shrink-only baseline.
  enforced every `return` in the C body is `SIMPLE_RT_NONNULL(...)` (runtime_nonnull.h)
           and there is no direct null return. The bridge aborts on NULL, so the
           bare-typed edge is counted in `enforced=`, not UNKNOWN. A symbol with
           several definitions is enforced only if every definition is.

Text scan of all hosts' sources: no statement about what compiles or links on any
target. A bare-typed edge whose C body has no direct null return and no full
SIMPLE_RT_NONNULL coverage (no visible body, or any null could come through a
callee) is counted UNKNOWN, never proven non-null.
Not matched: multi-line C signatures and __attribute__ prefixes (none in tree
today). src/compiler_rust/lib is out of scope. Raw i64/u64 handles are
counted, not judged. Do not flip signatures from this report alone: see the
interpreter Option-unwrapping note in the nil-return follow-ups.

Parameter direction (second pass, same C and .spl sources). Each C parameter
list is joined by position to the .spl extern params:
  SRT003   parameter count differs between C and .spl. Report-only: printed and counted,
           never fails the verdict (the tree has pre-existing drift; see the report).
  SRT004   a C pointer parameter declared as a sub-pointer-width scalar in .spl
           (i8..u32, bool, f32, f64, optionals of those). Never baselined.
  SNULL002 .spl `T?` crossing a bare C `T *` parameter (NULL can cross unchecked).
  SNULL003 .spl `&T` or `&mut T` crossing a bare C `T *` parameter.
           SNULL002/SNULL003 are shrink-only in scripts/check/rt_param_ref_map_baseline.txt,
           keyed file:extern:param_index:type. Create it only with --regen-param-baseline.
  `void` alone is no parameter, an unnamed parameter is typed by its type alone,
  and a trailing `...` ends the fixed prefix that is joined. A parameter that cannot
  be parsed (function pointer, array, .spl param without `name: type`) counts as
  unparsed= coverage and is never counted as checked.

Last stdout line is the verdict: PASS (0), FAIL (1), ERROR nothing checked (2).
Usage: check-rt-pointer-ref-map.py [--root DIR] [--regen-baseline] [--regen-param-baseline] [--selftest]
"""
import os, re, sys, tempfile

# Any rt_ definition or prototype, whatever its return type (parameter direction).
SIGDEF = re.compile(r'^(?!static\b|return\b)[A-Za-z_][\w \t*]*?[ \t*](rt_\w+)[ \t]*\(', re.M)
CDEF = re.compile(r'^(?!static\b)(?:[A-Za-z_]\w*[ \t]+)*?[A-Za-z_]\w*(?:[ \t]+const)?[ \t]*\*+[ \t]*(rt_\w+)[ \t]*\(', re.M)
EXT = re.compile(r'^[ \t]*(?:pub[ \t]+)?extern[ \t]+fn[ \t]+(rt_\w+)(?:<[^>]*>)?[ \t]*\(((?:[^()]|\([^()]*\))*)\)[ \t]*(?:->[ \t]*([^\n#]+?))?[ \t]*(?:#.*)?$', re.M)
_NULL = r'(?:\(\s*[\w ]+\*+\s*\)\s*)?(?:NULL|nullptr|0)'
NULLRET = re.compile(r'\breturn\s*\(?\s*' + _NULL + r'\s*\)?\s*;|\breturn\b[^;]*[?:]\s*' + _NULL + r'\s*(?=[:;)])')
RET = re.compile(r'\breturn\b[^;]*;')
ENFORCED = re.compile(r'\breturn\s*(?:\([^()]*\)\s*)?SIMPLE_RT_NONNULL\s*\(')
RANK = {'unknown': 0, 'enforced': 1, 'seen': 2, 'nil': 3}
NOISE = re.compile(r'/\*.*?\*/|//[^\n]*|"(?:\\.|[^"\\\n])*"|\'(?:\\.|[^\'\\\n])*\'', re.S)
NARROW = {'i8', 'i16', 'i32', 'u8', 'u16', 'u32', 'bool', 'f32', 'f64'}
BASELINE = 'scripts/check/rt_pointer_ref_map_baseline.txt'
PARAM_BASELINE = 'scripts/check/rt_param_ref_map_baseline.txt'
QUAL = re.compile(r'\b(?:const|volatile|restrict|__restrict|struct|enum|union)\b')
REF_MUT = re.compile(r'&\s*mut\b\s*(.*)$')
REF = re.compile(r'&\s*(.*)$')


def close_paren(src, pos):
    """Index of the ')' that closes the '(' at pos, or -1."""
    depth = 0
    for i in range(pos, len(src)):
        if src[i] == '(':
            depth += 1
        elif src[i] == ')':
            depth -= 1
            if depth == 0:
                return i
    return -1


def split_top(text):
    """Split on commas outside (), [] and {}. Generic '<' is not tracked; no .spl param uses it."""
    parts, cur, depth = [], '', 0
    for ch in text:
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth -= 1
        if ch == ',' and depth == 0:
            parts.append(cur)
            cur = ''
        else:
            cur += ch
    if cur.strip():
        parts.append(cur)
    return [p.strip() for p in parts]


LEN_NAME = re.compile(r'\b\w*(?:len|length|count|size|cap)\s*$')


def c_params(text, fold=True):
    """C parameter list -> [(kind, base)]; kind is ptr, scalar or unparsed. Stops at '...'.

    Text ABI fold: the runtime passes a .spl `text` as `const uint8_t *ptr, uint64_t len`.
    An integer named *len/*length/*count/*size/*cap directly after a pointer is that
    pointer's length companion. fold=True drops it; join_params tries the unfolded
    list first and uses the folded one only when the unfolded count differs from the
    .spl count, so a .spl that spells the pair as two i64 still matches unfolded."""
    t = ' '.join(text.split())
    if t in ('', 'void'):
        return []
    out = []
    for p in split_top(t):
        if p == '...':
            break
        if fold and out and out[-1][0] == 'ptr' and '*' not in p and '(' not in p \
                and '[' not in p and LEN_NAME.search(p):
            continue
        if '(' in p or '[' in p:
            out.append(('unparsed', p))
        elif '*' in p:
            base = QUAL.sub(' ', p[:p.rindex('*')])
            out.append(('ptr', ' '.join(base.split())))
        else:
            out.append(('scalar', p))
    return out


def spl_type(typ):
    """.spl type -> (kind, base); kind is bare, opt, ref or refmut."""
    m = REF_MUT.match(typ)
    if m:
        return ('refmut', m[1].strip())
    m = REF.match(typ)
    if m:
        return ('ref', m[1].strip())
    if typ.endswith('?'):
        return ('opt', typ[:-1].strip())
    return ('bare', typ)


def spl_params(text):
    """.spl param list -> [(kind, base, type text) | (None, None, None)] per `name: type`."""
    t = ' '.join(text.split())
    out = []
    for p in split_top(t):
        if ':' not in p:
            out.append((None, None, None))
        else:
            typ = p.split(':', 1)[1].strip()
            out.append(spl_type(typ) + (typ,))
    return out


def walk(root, rel, exts):
    for d, dirs, names in os.walk(os.path.join(root, rel)):
        dirs[:] = [x for x in dirs if x != 'test']
        for n in sorted(names):
            if n.endswith(exts):
                yield os.path.join(d, n)


def read(path):
    with open(path, errors='ignore') as f:
        return f.read()


def body_after(src, pos):
    """Return the brace body following a signature, or None for a prototype."""
    depth = paren = 0
    i = pos
    while i < len(src):
        c = src[i]
        if c == '(':
            paren += 1
        elif c == ')':
            paren -= 1
        elif c == ';' and paren == 0:
            return None
        elif c == '{':
            start = i
            while i < len(src):
                depth += (src[i] == '{') - (src[i] == '}')
                i += 1
                if depth == 0:
                    return src[start:i]
            return src[start:]
        i += 1
    return None


def classify(body):
    """nil: a direct null return. enforced: every return is SIMPLE_RT_NONNULL. seen: neither."""
    if NULLRET.search(body):
        return 'nil'
    rets = RET.findall(body)
    if rets and all(ENFORCED.match(r) for r in rets):
        return 'enforced'
    return 'seen'


def scan(root):
    c = {}  # symbol -> 'nil' | 'seen' | 'enforced' | 'unknown' (worst definition wins)
    sigs = {}  # symbol -> [c_params(...) | None] one entry per definition or prototype
    for path in walk(root, 'src/runtime', ('.c', '.h')):
        src = NOISE.sub(' ', read(path))
        for m in SIGDEF.finditer(src):
            close = close_paren(src, m.end() - 1)
            sigs.setdefault(m[1], []).append(
                (c_params(src[m.end():close]), c_params(src[m.end():close], False))
                if close >= 0 else None)
        for m in CDEF.finditer(src):
            body = body_after(src, m.end() - 1)
            state = c.get(m[1], 'unknown')
            if body is not None:
                kind = classify(body)
                if RANK[kind] > RANK[state]:
                    state = kind
            c[m[1]] = state
    narrow, nil = set(), set()
    edges = unknown = raw = enforced = 0
    pedges = 0
    p_ptr, p_unparsed, p_srt003, p_narrow, p_snull = set(), set(), set(), set(), {}
    for top in ('src/compiler', 'src/lib', 'src/app', 'src/os'):
        for path in walk(root, top, ('.spl',)):
            src = read(path)
            rel = os.path.relpath(path, root)
            for m in EXT.finditer(src):
                if m[1] in sigs:
                    pedges += 1
                    join_params(m[1], m[2], rel, sigs[m[1]],
                                (p_ptr, p_unparsed, p_srt003, p_narrow, p_snull))
                if m[1] not in c:
                    continue
                edges += 1
                ty = (m[3] or 'void').strip()
                key = '%s:%s:%s' % (os.path.relpath(path, root), m[1], ty)
                if ty.rstrip('?') in NARROW:
                    narrow.add(key)
                elif ty.rstrip('?') in ('i64', 'u64', 'usize', 'isize', 'void'):
                    raw += 1
                elif ty.endswith('?'):
                    continue
                elif c[m[1]] == 'nil':
                    nil.add(key)
                elif c[m[1]] == 'enforced':
                    enforced += 1
                else:
                    unknown += 1
    pres = {'edges': pedges, 'ptr': len(p_ptr), 'unparsed': len(p_unparsed),
            'srt003': sorted(p_srt003), 'narrow': p_narrow, 'snull': p_snull}
    return len(c), edges, unknown, raw, narrow, nil, enforced, pres


def join_params(sym, params, rel, defs, acc):
    """Join each C definition's parameters to the .spl extern params by position."""
    p_ptr, p_unparsed, p_srt003, p_narrow, p_snull = acc
    spl = spl_params(params)
    for entry in defs:
        if entry is None:
            p_unparsed.add((rel, sym, -1))
            continue
        folded, raw = entry
        sig = raw if len(raw) == len(spl) else folded
        if len(sig) != len(spl):
            p_srt003.add('SRT003 param count mismatch (report-only): %s:%s C=%d spl=%d' % (rel, sym, len(raw), len(spl)))
            continue
        for i, (ck, _cb) in enumerate(sig):
            sk, sb, st = spl[i]
            if ck == 'unparsed' or sk is None:
                p_unparsed.add((rel, sym, i))
                continue
            if ck != 'ptr':
                continue
            p_ptr.add((rel, sym, i))
            key = '%s:%s:%d:%s' % (rel, sym, i, st)
            if sb.rstrip('?') in NARROW:
                p_narrow.add(key)
            elif sk == 'opt':
                p_snull[key] = 'SNULL002'
            elif sk in ('ref', 'refmut'):
                p_snull[key] = 'SNULL003'


def load_baseline(path):
    if not os.path.exists(path):
        return set()
    return {l.strip() for l in read(path).splitlines() if l.strip() and not l.startswith('#')}


def run(root, regen, regen_param=False):
    syms, edges, unknown, raw, narrow, nil, enforced, pres = scan(root)
    if syms == 0 or edges == 0:
        print('ERROR — nothing was checked (0 C pointer symbols or 0 extern edges)')
        return 2
    bpath = os.path.join(root, BASELINE)
    if regen:
        with open(bpath, 'w') as f:
            f.write('# Shrink-only. <file>:<extern>:<type> where C can return NULL and .spl is non-optional.\n')
            f.writelines(k + '\n' for k in sorted(nil))
    base = load_baseline(bpath)
    new, stale = sorted(nil - base), sorted(base - nil)
    for k in sorted(narrow):
        print('SRT004 narrow pointer return: ' + k)
    for k in new:
        print('SRT004 new nil mismatch: ' + k)
    for k in stale:
        print('SRT004 stale baseline row, remove it: ' + k)
    print('coverage symbols=%d edges=%d enforced=%d baselined=%d raw=%d UNKNOWN=%d compile=UNTESTED link=UNTESTED' % (syms, edges, enforced, len(nil & base), raw, unknown))
    ppath = os.path.join(root, PARAM_BASELINE)
    snull = pres['snull']
    if regen_param:
        with open(ppath, 'w') as f:
            f.write('# Shrink-only. <file>:<extern>:<param_index>:<type> where a .spl T? (SNULL002) or &T/&mut T (SNULL003) crosses a bare C T* parameter.\n')
            f.writelines(k + '\n' for k in sorted(snull))
    pbase = load_baseline(ppath)
    pnew = sorted(k for k in snull if k not in pbase)
    pstale = sorted(k for k in pbase if k not in snull)
    for line in pres['srt003']:
        print(line)
    for k in sorted(pres['narrow']):
        print('SRT004 narrow pointer param: ' + k)
    for k in pnew:
        print('%s new param mismatch: %s' % (snull[k], k))
    for k in pstale:
        print('SNULL stale param baseline row, remove it: ' + k)
    print('param coverage: edges=%d ptr_params=%d unparsed=%d SRT003=%d narrow=%d SNULL002=%d SNULL003=%d baselined=%d' % (
        pres['edges'], pres['ptr'], pres['unparsed'], len(pres['srt003']), len(pres['narrow']),
        sum(1 for v in snull.values() if v == 'SNULL002'), sum(1 for v in snull.values() if v == 'SNULL003'),
        len(set(snull) & pbase)))
    # SRT003 is report-only: it is printed and counted above but never fails the verdict.
    bad = len(narrow) + len(new) + len(stale) + len(pres['narrow']) + len(pnew) + len(pstale)
    if bad:
        print('FAIL — %d edge(s) checked, %d finding(s)' % (edges, bad))
        return 1
    print('PASS — %d edge(s) checked, 0 new finding(s), mapping evidence only' % edges)
    return 0


def selftest():
    def tree(c, spl):
        t = tempfile.mkdtemp()
        os.makedirs(t + '/src/runtime')
        os.makedirs(t + '/src/lib')
        os.makedirs(t + '/scripts/check')
        open(t + '/src/runtime/a.c', 'w').write(c)
        open(t + '/src/lib/a.spl', 'w').write(spl)
        return t
    nilc = 'char *rt_x(void) {\n  if (a) return NULL;\n  return b;\n}\n'
    okc = 'char *rt_x(void) {\n  return b;\n}\n'
    cases = [
        (nilc, 'extern fn rt_x() -> text\n', 1),
        (nilc, 'extern fn rt_x() -> text?\n', 0),
        (okc, 'extern fn rt_x() -> text\n', 0),
        (okc, 'extern fn rt_x() -> i32\n', 1),
        ('char *rt_x(void);\n', 'extern fn rt_x() -> text\n', 0),
        ('static char *rt_x(void) { return NULL; }\n', 'extern fn rt_x() -> text\n', 2),
        (nilc, 'fn other() -> text\n', 2),
        (okc, 'extern fn rt_x() -> i32?\n', 1),
        ('char *rt_x(void) {\n  if (c == \'}\') y();\n  return NULL;\n}\n', 'extern fn rt_x() -> text\n', 1),
        ('char *rt_x(void) {\n  return p ? p : NULL;\n}\n', 'extern fn rt_x() -> text\n', 1),
        ('char *rt_x(void) {\n  return bad ? NULL : p;\n}\n', 'extern fn rt_x() -> text\n', 1),
        (nilc, 'extern fn rt_x<T>(v: T) -> [T]\n', 1),
        (nilc, 'extern fn rt_x(cb: fn(i64) -> i64) -> text\n', 1),
    ]
    for i, (c, spl, want) in enumerate(cases):
        got = run(tree(c, spl), False)
        if got != want:
            print('ERROR — selftest case %d wanted %d got %d' % (i, want, got))
            return 2
    # Enforced coverage: exit code AND the enforced/UNKNOWN counts from scan(),
    # because an enforced and an UNKNOWN edge both exit 0.
    enf = 'char *rt_x(void) {\n  return SIMPLE_RT_NONNULL("rt_x", b);\n}\n'
    cov = [
        # (C source, .spl source, exit, enforced, UNKNOWN)
        (enf, 'extern fn rt_x() -> text\n', 0, 1, 0),
        (enf, 'extern fn rt_x() -> text?\n', 0, 0, 0),
        ('char *rt_x(void) {\n  return (char *)SIMPLE_RT_NONNULL("rt_x", b);\n}\n',
         'extern fn rt_x() -> text\n', 0, 1, 0),
        ('char *rt_x(void) {\n  if (a) return NULL;\n  return SIMPLE_RT_NONNULL("rt_x", b);\n}\n',
         'extern fn rt_x() -> text\n', 1, 0, 0),
        ('char *rt_x(void) {\n  return p ? SIMPLE_RT_NONNULL("rt_x", p) : NULL;\n}\n',
         'extern fn rt_x() -> text\n', 1, 0, 0),
        ('char *rt_x(void) {\n  if (a) return SIMPLE_RT_NONNULL("rt_x", p);\n  return b;\n}\n',
         'extern fn rt_x() -> text\n', 0, 0, 1),
        ('char *rt_x(void);\n', 'extern fn rt_x() -> text\n', 0, 0, 1),
        (enf + 'char *rt_x(void) {\n  return b;\n}\n', 'extern fn rt_x() -> text\n', 0, 0, 1),
    ]
    for i, (c, spl, want_code, want_enf, want_unk) in enumerate(cov):
        t = tree(c, spl)
        _s, _e, unknown, _r, _n, _nil, enforced, _p = scan(t)
        got = run(t, False)
        if got != want_code or enforced != want_enf or unknown != want_unk:
            print('ERROR — enforced selftest case %d wanted exit=%d enforced=%d UNKNOWN=%d, got exit=%d enforced=%d UNKNOWN=%d'
                  % (i, want_code, want_enf, want_unk, got, enforced, unknown))
            return 2

    # Parameter direction: (C source, .spl source, exit, srt003, narrow, snull codes, unparsed)
    pcases = [
        ('char *rt_x(char *a, int64_t b);\n', 'extern fn rt_x(a: text) -> text\n', 0, 1, 0, '', 0),
        ('char *rt_x(char *a);\n', 'extern fn rt_x(a: i32) -> text\n', 1, 0, 1, '', 0),
        ('char *rt_x(char *a);\n', 'extern fn rt_x(a: text?) -> text\n', 1, 0, 0, 'SNULL002', 0),
        ('char *rt_x(char *a);\n', 'extern fn rt_x(a: &text) -> text\n', 1, 0, 0, 'SNULL003', 0),
        ('char *rt_x(char *a);\n', 'extern fn rt_x(a: &mut [u8]) -> text\n', 1, 0, 0, 'SNULL003', 0),
        ('char *rt_x(char *a);\n', 'extern fn rt_x(a: text) -> text\n', 0, 0, 0, '', 0),
        ('char *rt_x(char *);\n', 'extern fn rt_x(a: text) -> text\n', 0, 0, 0, '', 0),
        ('char *rt_x(char *a, ...);\n', 'extern fn rt_x(a: text) -> text\n', 0, 0, 0, '', 0),
        ('char *rt_x(void);\n', 'extern fn rt_x() -> text\n', 0, 0, 0, '', 0),
        ('char *rt_x(int64_t n);\n', 'extern fn rt_x(n: i64) -> text\n', 0, 0, 0, '', 0),
        ('char *rt_x(int (*cb)(void *));\n', 'extern fn rt_x(cb: text) -> text\n', 0, 0, 0, '', 1),
        ('char *rt_x(char *a);\n', 'extern fn rt_x(a) -> text\n', 0, 0, 0, '', 1),
        ('char *rt_x(char *a,\n  uint64_t n);\n', 'extern fn rt_x(a: text, n: i64) -> text\n', 0, 0, 0, '', 0),
        # text ABI fold: ptr + *_len is one .spl text slot; a len with no pointer before it is not folded
        ('char *rt_x(const uint8_t *p, uint64_t p_len);\n', 'extern fn rt_x(a: text) -> text\n', 0, 0, 0, '', 0),
        ('char *rt_x(int64_t n, uint64_t len);\n', 'extern fn rt_x(n: i64) -> text\n', 0, 1, 0, '', 0),
        # the .spl spells ptr+len as two i64: the unfolded list matches, so no mismatch
        ('char *rt_x(const uint8_t *p, uint64_t p_len);\n', 'extern fn rt_x(p: i64, n: i64) -> text\n', 0, 0, 0, '', 0),
        ('char *rt_x(const uint8_t *p, uint64_t p_len, uint64_t extra);\n', 'extern fn rt_x(a: text) -> text\n', 0, 1, 0, '', 0),
    ]
    for i, (c, spl, want_code, want_srt, want_narrow, want_snull, want_unp) in enumerate(pcases):
        t = tree(c, spl)
        _s, _e, _u, _r, _n, _nil, _enf, pres = scan(t)
        codes = sorted(set(pres['snull'].values()))
        got = run(t, False)
        if (got != want_code or len(pres['srt003']) != want_srt or len(pres['narrow']) != want_narrow
                or (','.join(codes) != want_snull) or pres['unparsed'] != want_unp):
            print('ERROR — param selftest case %d wanted exit=%d srt003=%d narrow=%d snull=%r unparsed=%d, got exit=%d srt003=%d narrow=%d snull=%r unparsed=%d'
                  % (i, want_code, want_srt, want_narrow, want_snull, want_unp, got, len(pres['srt003']),
                     len(pres['narrow']), ','.join(codes), pres['unparsed']))
            return 2

    # Param baseline: a held SNULL row passes, a stale row fails, --regen-param-baseline writes only SNULL rows
    t = tree('char *rt_x(char *a);\n', 'extern fn rt_x(a: text?) -> text\n')
    if run(t, False, False) != 1:
        print('ERROR — selftest param baseline absent should fail')
        return 2
    if run(t, False, True) != 0 or run(t, False) != 0:
        print('ERROR — selftest param regen did not hold its row')
        return 2
    open(t + '/' + PARAM_BASELINE, 'a').write('src/lib/a.spl:rt_gone:0:text?\n')
    if run(t, False) != 1:
        print('ERROR — selftest stale param row should fail')
        return 2

    t = tree(nilc, 'extern fn rt_x() -> text\n')
    row = 'src/lib/a.spl:rt_x:text\n'
    open(t + '/' + BASELINE, 'w').write(row)
    held = run(t, False)
    open(t + '/' + BASELINE, 'w').write(row + 'src/lib/a.spl:rt_y:text\n')
    if held != 0 or run(t, False) != 1:
        print('ERROR — selftest baseline held/stale')
        return 2
    print('PASS — selftest %d return, %d enforced, %d parameter cases' % (len(cases), len(cov), len(pcases)))
    return 0


def main():
    a = sys.argv[1:]
    if '--selftest' in a:
        return selftest()
    root = a[a.index('--root') + 1] if '--root' in a else os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
    return run(root, '--regen-baseline' in a, '--regen-param-baseline' in a)


if __name__ == '__main__':
    sys.exit(main())
