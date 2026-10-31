#!/usr/bin/env python3
"""check-rt-host-map.py: SRT001 per-host rt_ provider map, MAPPING evidence only.

For each host config, evaluates #if host macros over src/runtime C sources without
building, then checks every .spl `extern fn rt_x` that some host provides also has
a provider on each other host. Missing rows are a shrink-only baseline.

Limits: no C macro selects SimpleOS, so that host is reported UNKNOWN, never as clean.
macros other than host macros stay UNKNOWN and keep both branches, so a
provider may be over-counted. Source lists are not joined here (see
check-runtime-source-list-parity.shs) beyond host filename suffixes. Symbols with a
Rust export are skipped and counted: cfg on them is not evaluated. Compile and link
are UNTESTED on every host.

Last stdout line is the verdict: PASS (0), FAIL (1), ERROR nothing checked (2).
Usage: check-rt-host-map.py [--root DIR] [--regen-baseline] [--selftest]
"""
import os, re, sys, tempfile

HOSTS = {
    'linux': {'__linux__', '__unix__'},
    'macos': {'__APPLE__', '__MACH__', '__unix__'},
    'windows': {'_WIN32', '_WIN64'},
    'freebsd': {'__FreeBSD__', '__unix__'},
    'simpleos': {'__simpleos__'},
}
KNOWN = set().union(*HOSTS.values()) | {'__NetBSD__', '__OpenBSD__'}
SUFFIX = {'windows': 'windows', 'win32': 'windows', 'linux': 'linux', 'macos': 'macos',
          'darwin': 'macos', 'freebsd': 'freebsd', 'simpleos': 'simpleos'}
DEF = re.compile(r'^(?!static\b)[\w \t*]*?\b(rt_\w+)[ \t]*\([^;{}]*\)\s*\{', re.M)
EXT = re.compile(r'^[ \t]*(?:pub[ \t]+)?extern[ \t]+fn[ \t]+(rt_\w+)', re.M)
RUST = re.compile(r'extern\s+"C"\s+fn\s+(rt_\w+)')
TOK = re.compile(r'\s*(defined\s*\(\s*\w+\s*\)|defined\s+\w+|&&|\|\||!|\(|\)|[^\s()&|!]+)')
BASELINE = 'scripts/check/rt_host_map_baseline.txt'


def NOT(a):
    return None if a is None else not a


def AND(a, b):
    return False if a is False or b is False else (None if a is None or b is None else True)


def OR(a, b):
    return True if a is True or b is True else (None if a is None or b is None else False)


def evaluate(expr, host):
    """Three-valued #if evaluation: True, False or None for unknown."""
    toks = TOK.findall(expr.split('//')[0].split('/*')[0])
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else None

    def prim():
        t = peek()
        pos[0] += 1
        if t == '!':
            return NOT(prim())
        if t == '(':
            v = orx()
            if peek() != ')':
                raise ValueError
            pos[0] += 1
            return v
        if t and t.startswith('defined'):
            m = re.search(r'(\w+)\W*$', t)[1]
            return m in HOSTS[host] if m in KNOWN else None
        raise ValueError

    def andx():
        v = prim()
        while peek() == '&&':
            pos[0] += 1
            v = AND(v, prim())
        return v

    def orx():
        v = andx()
        while peek() == '||':
            pos[0] += 1
            v = OR(v, andx())
        return v

    try:
        v = orx()
        return v if pos[0] == len(toks) else None
    except (ValueError, TypeError):
        return None


def host_view(src, host):
    out = []
    stack = []  # [active, any_branch_taken]
    for line in src.split('\n'):
        m = re.match(r'\s*#\s*(ifdef|ifndef|if|elif|else|endif)\b(.*)', line)
        if m:
            k, rest = m[1], m[2].strip()
            if k in ('ifdef', 'ifndef'):
                n = rest.split()[0] if rest else ''
                v = (n in HOSTS[host]) if n in KNOWN else None
                stack.append([v if k == 'ifdef' else NOT(v), v])
            elif k == 'if':
                v = evaluate(rest, host)
                stack.append([v, v])
            elif stack and k == 'elif':
                v = AND(NOT(stack[-1][1]), evaluate(rest, host))
                stack[-1] = [v, OR(stack[-1][1], v)]
            elif stack and k == 'else':
                stack[-1] = [NOT(stack[-1][1]), True]
            elif stack:
                stack.pop()
            out.append('')
        else:
            out.append('' if any(f[0] is False for f in stack) else line)
    return '\n'.join(out)


def file_host(name):
    for tok in re.split(r'[_.]', os.path.basename(name)):
        if tok in SUFFIX:
            return SUFFIX[tok]
    return None


def files(root, rel, exts):
    for d, dirs, names in os.walk(os.path.join(root, rel)):
        dirs[:] = [x for x in dirs if x not in ('test', 'vendor', 'target')]
        for n in sorted(names):
            if n.endswith(exts):
                yield os.path.join(d, n)


def read(p):
    with open(p, errors='ignore') as f:
        return f.read()


def scan(root):
    prov = {h: set() for h in HOSTS}
    nocomment = re.compile(r'/\*.*?\*/|//[^\n]*', re.S)
    for p in files(root, 'src/runtime', ('.c', '.cpp', '.m', '.mm')):
        only = file_host(p)
        src = nocomment.sub('', read(p))
        for h in HOSTS:
            if only in (None, h):
                prov[h].update(DEF.findall(host_view(src, h)))
    rust = set()
    for rel in ('src/compiler_rust/runtime/src', 'src/runtime'):
        for p in files(root, rel, ('.rs',)):
            rust.update(RUST.findall(read(p)))
    decl = set()
    for top in ('src/compiler', 'src/lib', 'src/app', 'src/os'):
        for p in files(root, top, ('.spl',)):
            decl.update(EXT.findall(read(p)))
    return prov, rust, decl


def run(root, regen):
    prov, rust, decl = scan(root)
    anyhost = set().union(*prov.values())
    hosted = [h for h in HOSTS if h != 'simpleos']
    edges = (decl & set().union(*(prov[h] for h in hosted))) - rust
    if not edges:
        print('ERROR — nothing was checked (0 extern to C provider edges)')
        return 2
    missing = {'%s:%s' % (h, s) for h in hosted for s in edges if s not in prov[h]}
    bp = os.path.join(root, BASELINE)
    if regen:
        with open(bp, 'w') as f:
            f.write('# Shrink-only. <host>:<extern> with a C provider elsewhere but none on this host.\n')
            f.writelines(k + '\n' for k in sorted(missing))
    base = set()
    if os.path.exists(bp):
        base = {l.strip() for l in read(bp).splitlines() if l.strip() and not l.startswith('#')}
    new, stale = sorted(missing - base), sorted(base - missing)
    for k in new:
        print('SRT001 new host gap: ' + k)
    for k in stale:
        print('SRT001 stale baseline row, remove it: ' + k)
    print('RT_AUDIT host=simpleos map=UNKNOWN compile=UNTESTED link=UNTESTED')
    for h in hosted:
        n = sum(1 for k in missing if k.startswith(h + ':'))
        print('RT_AUDIT host=%s map_gaps=%d compile=UNTESTED link=UNTESTED' % (h, n))
    print('coverage edges=%d rust_skipped=%d no_provider=%d' % (len(edges), len(decl & rust), len(decl - anyhost - rust)))
    if new or stale:
        print('FAIL — %d finding(s)' % (len(new) + len(stale)))
        return 1
    print('PASS — %d edge(s) over %d hosts, 0 new gap(s), simpleos UNKNOWN, mapping evidence only' % (len(edges), len(hosted)))
    return 0


def selftest():
    def tree(c, name='a.c'):
        t = tempfile.mkdtemp()
        for d in ('src/runtime', 'src/lib', 'scripts/check'):
            os.makedirs(t + '/' + d)
        open(t + '/src/runtime/' + name, 'w').write(c)
        open(t + '/src/lib/a.spl', 'w').write('extern fn rt_x() -> i64\n')
        return t
    body = 'long rt_x(void) { return 1; }\n'
    for i, (c, name, want) in enumerate([
        (body, 'a.c', 0),
        ('#if defined(__linux__)\n' + body + '#endif\n', 'a.c', 1),
        ('#ifdef _WIN32\n' + body + '#else\n' + body + '#endif\n', 'a.c', 0),
        ('#if defined(FEATURE_X)\n' + body + '#endif\n', 'a.c', 0),
        (body, 'a_windows.c', 1),
        ('static long rt_x(void) { return 1; }\n', 'a.c', 2),
    ]):
        got = run(tree(c, name), False)
        if got != want:
            print('ERROR — selftest case %d wanted %d got %d' % (i, want, got))
            return 2
    print('PASS — selftest 6 cases')
    return 0


def main():
    a = sys.argv[1:]
    if '--selftest' in a:
        return selftest()
    root = a[a.index('--root') + 1] if '--root' in a else os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
    return run(root, '--regen-baseline' in a)


if __name__ == '__main__':
    sys.exit(main())
