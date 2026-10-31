#!/usr/bin/env python3
"""check-rt-pointer-ref-map.py: SRT004 pointer-return map, MAPPING evidence only.

Joins each C `T *rt_x(...)` definition under src/runtime to every `.spl`
`extern fn rt_x` declaration. This complements check-non-optional-nil-return.shs,
which derives nil-capability from the Rust interpreter, not from C bodies.

  narrow   pointer declared as a sub-pointer-width scalar (truncates). Never baselined.
  nil      a C body has a direct `return NULL`/`return 0` but the .spl managed
           return (text, [T], tuple) is non-optional. Shrink-only baseline.

Text scan of all hosts' sources: no statement about what compiles or links on any
target. A C function with no visible body, or which returns NULL only through a
callee, is counted as UNKNOWN, never as proven non-null. Raw i64/u64 handles are
counted, not judged. Do not flip signatures from this report alone: see the
interpreter Option-unwrapping note in the nil-return follow-ups.

Last stdout line is the verdict: PASS (0), FAIL (1), ERROR nothing checked (2).
Usage: check-rt-pointer-ref-map.py [--root DIR] [--regen-baseline] [--selftest]
"""
import os, re, sys, tempfile

CDEF = re.compile(r'^(?!static\b)(?:[A-Za-z_]\w*[ \t]+)*?[A-Za-z_]\w*(?:[ \t]+const)?[ \t]*\*+[ \t]*(rt_\w+)[ \t]*\(', re.M)
EXT = re.compile(r'^[ \t]*(?:pub[ \t]+)?extern[ \t]+fn[ \t]+(rt_\w+)[ \t]*\([^)]*\)[ \t]*(?:->[ \t]*([^\n#]+?))?[ \t]*(?:#.*)?$', re.M)
NULLRET = re.compile(r'\breturn\s+(?:NULL|0|nullptr|\(\s*\w+\s*\*\s*\)\s*(?:NULL|0))\s*;')
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


def scan(root):
    c = {}  # symbol -> 'nil' | 'unknown'
    for path in walk(root, 'src/runtime', ('.c', '.h')):
        src = read(path)
        for m in CDEF.finditer(src):
            body = body_after(src, m.end() - 1)
            state = c.get(m[1], 'unknown')
            if body is not None and NULLRET.search(body):
                state = 'nil'
            elif body is not None and state != 'nil':
                state = 'seen'
            c[m[1]] = state
    narrow, nil = set(), set()
    edges = unknown = raw = 0
    for top in ('src/compiler', 'src/lib', 'src/app', 'src/os'):
        for path in walk(root, top, ('.spl',)):
            src = read(path)
            for m in EXT.finditer(src):
                if m[1] not in c:
                    continue
                edges += 1
                ty = (m[2] or 'void').strip()
                key = '%s:%s:%s' % (os.path.relpath(path, root), m[1], ty)
                if ty in NARROW:
                    narrow.add(key)
                elif ty in ('i64', 'u64', 'void'):
                    raw += 1
                elif c[m[1]] == 'unknown':
                    unknown += 1
                elif c[m[1]] == 'nil' and not ty.endswith('?'):
                    nil.add(key)
    return len(c), edges, unknown, raw, narrow, nil


def load_baseline(path):
    if not os.path.exists(path):
        return set()
    return {l.strip() for l in read(path).splitlines() if l.strip() and not l.startswith('#')}


def run(root, regen):
    syms, edges, unknown, raw, narrow, nil = scan(root)
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
    print('coverage symbols=%d edges=%d baselined=%d raw=%d UNKNOWN=%d compile=UNTESTED link=UNTESTED' % (syms, edges, len(nil & base), raw, unknown))
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
    ]
    for i, (c, spl, want) in enumerate(cases):
        got = run(tree(c, spl), False)
        if got != want:
            print('ERROR — selftest case %d wanted %d got %d' % (i, want, got))
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
