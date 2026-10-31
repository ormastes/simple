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

Last stdout line is the verdict: PASS (0), FAIL (1), ERROR nothing checked (2).
Usage: check-rt-pointer-ref-map.py [--root DIR] [--regen-baseline] [--selftest]
"""
import os, re, sys, tempfile

CDEF = re.compile(r'^(?!static\b)(?:[A-Za-z_]\w*[ \t]+)*?[A-Za-z_]\w*(?:[ \t]+const)?[ \t]*\*+[ \t]*(rt_\w+)[ \t]*\(', re.M)
EXT = re.compile(r'^[ \t]*(?:pub[ \t]+)?extern[ \t]+fn[ \t]+(rt_\w+)(?:<[^>]*>)?[ \t]*\((?:[^()]|\([^()]*\))*\)[ \t]*(?:->[ \t]*([^\n#]+?))?[ \t]*(?:#.*)?$', re.M)
_NULL = r'(?:\(\s*[\w ]+\*+\s*\)\s*)?(?:NULL|nullptr|0)'
NULLRET = re.compile(r'\breturn\s*\(?\s*' + _NULL + r'\s*\)?\s*;|\breturn\b[^;]*[?:]\s*' + _NULL + r'\s*(?=[:;)])')
RET = re.compile(r'\breturn\b[^;]*;')
ENFORCED = re.compile(r'\breturn\s*(?:\([^()]*\)\s*)?SIMPLE_RT_NONNULL\s*\(')
RANK = {'unknown': 0, 'enforced': 1, 'seen': 2, 'nil': 3}
NOISE = re.compile(r'/\*.*?\*/|//[^\n]*|"(?:\\.|[^"\\\n])*"|\'(?:\\.|[^\'\\\n])*\'', re.S)
NARROW = {'i8', 'i16', 'i32', 'u8', 'u16', 'u32', 'bool', 'f32', 'f64'}
BASELINE = 'scripts/check/rt_pointer_ref_map_baseline.txt'


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
    for path in walk(root, 'src/runtime', ('.c', '.h')):
        src = NOISE.sub(' ', read(path))
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
    for top in ('src/compiler', 'src/lib', 'src/app', 'src/os'):
        for path in walk(root, top, ('.spl',)):
            src = read(path)
            for m in EXT.finditer(src):
                if m[1] not in c:
                    continue
                edges += 1
                ty = (m[2] or 'void').strip()
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
    return len(c), edges, unknown, raw, narrow, nil, enforced


def load_baseline(path):
    if not os.path.exists(path):
        return set()
    return {l.strip() for l in read(path).splitlines() if l.strip() and not l.startswith('#')}


def run(root, regen):
    syms, edges, unknown, raw, narrow, nil, enforced = scan(root)
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
    bad = len(narrow) + len(new) + len(stale)
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
        _s, _e, unknown, _r, _n, _nil, enforced = scan(t)
        got = run(t, False)
        if got != want_code or enforced != want_enf or unknown != want_unk:
            print('ERROR — enforced selftest case %d wanted exit=%d enforced=%d UNKNOWN=%d, got exit=%d enforced=%d UNKNOWN=%d'
                  % (i, want_code, want_enf, want_unk, got, enforced, unknown))
            return 2

    t = tree(nilc, 'extern fn rt_x() -> text\n')
    row = 'src/lib/a.spl:rt_x:text\n'
    open(t + '/' + BASELINE, 'w').write(row)
    held = run(t, False)
    open(t + '/' + BASELINE, 'w').write(row + 'src/lib/a.spl:rt_y:text\n')
    if held != 0 or run(t, False) != 1:
        print('ERROR — selftest baseline held/stale')
        return 2
    print('PASS — selftest %d cases' % len(cases))
    return 0


def main():
    a = sys.argv[1:]
    if '--selftest' in a:
        return selftest()
    root = a[a.index('--root') + 1] if '--root' in a else os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
    return run(root, '--regen-baseline' in a)


if __name__ == '__main__':
    sys.exit(main())
