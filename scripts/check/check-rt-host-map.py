#!/usr/bin/env python3
"""check-rt-host-map.py: SRT001 per-host rt_ provider map, MAPPING evidence only.

For each host config, evaluates #if host macros over src/runtime C sources without
building, then checks every .spl `extern fn rt_x` that some host provides also has
a provider on each other host. Missing rows are a shrink-only baseline.

Limits: no C macro selects SimpleOS, so that host is reported UNKNOWN, never as clean.
macros other than host macros stay UNKNOWN and keep both branches, so a
provider may be over-counted. Quoted local includes are followed only inside owned src/runtime paths;
computed/system includes and macro expansion are not evaluated. Source lists
are not joined here (see
check-runtime-source-list-parity.shs) beyond host filename suffixes. Symbols with a
Rust export are skipped and counted: cfg on them is not evaluated. Compile and link
are UNTESTED on every host.

Last stdout line is the verdict: PASS (0), FAIL (1), ERROR nothing checked (2).
Usage: check-rt-host-map.py [--root DIR] [--regen-baseline] [--selftest]
"""
import os, re, sys, tempfile

HOSTS = {
    'linux': {'__linux__', '__unix__'},
    'macos': {'__APPLE__', '__MACH__'},
    'windows': {'_WIN32', '_WIN64'},
    'freebsd': {'__FreeBSD__', '__unix__'},
    'simpleos': {'__simpleos__'},
}
KNOWN = set().union(*HOSTS.values()) | {'__NetBSD__', '__OpenBSD__'}
SUFFIX = {'windows': 'windows', 'win32': 'windows', 'win': 'windows', 'linux': 'linux', 'macos': 'macos',
          'darwin': 'macos', 'freebsd': 'freebsd', 'simpleos': 'simpleos'}
DEF = re.compile(r'^(?![\w \t*]*\bstatic\b)[\w \t*]*?\b(rt_\w+)[ \t]*\([^;{}]*\)\s*\{', re.M)
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
        if t and t.isdigit():
            return t != '0'
        if t in KNOWN:
            return t in HOSTS[host]
        return None

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


def host_view(src, host, definite_only=False):
    """Host view of src. definite_only also blanks lines whose guard is unknown (None)."""
    out = []
    stack = []  # [active, any_branch_taken]
    for line in src.replace('\\\n', ' ').split('\n'):
        m = re.match(r'\s*#\s*(ifdef|ifndef|if|elif|else|endif)\b(.*)', line)
        if m:
            k, rest = m[1], m[2].strip()
            if k in ('ifdef', 'ifndef'):
                n = rest.split()[0] if rest else ''
                v = (n in HOSTS[host]) if n in KNOWN else None
                a = v if k == 'ifdef' else NOT(v)
                stack.append([a, a])
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
            if any(f[0] is False for f in stack):
                out.append('')
            elif definite_only and any(f[0] is not True for f in stack):
                out.append('')
            else:
                out.append(line)
    return '\n'.join(out)


def file_host(name):
    if 'startup/baremetal/' in name.replace('\\', '/'):
        return 'simpleos'
    for tok in re.split(r'[-_./\\]', name.split('src/runtime', 1)[-1]):
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


# Preserve quoted include names while removing comments. Strings are blanked
# separately before definition matching, so string contents cannot be exports.
C_STRING = re.compile(r'"(?:\\.|[^"\\\n])*"')
C_COMMENT_STRING = re.compile(r'/\*.*?\*/|//[^\n]*|' + C_STRING.pattern, re.S)
LOCAL_INCLUDE = re.compile(r'^[ \t]*#[ \t]*include[ \t]*"([^"\n]+)"', re.M)
EXTERNAL_RUNTIME_HEADERS = {'miniaudio.h', 'stb_image.h', 'stb_truetype.h'}


def c_provider_views(root):
    """Yield (host, definite_only, definition_path, host_view) for reachable sources.

    Start from existing C-family roots and their filename host restrictions.
    Walk each host/possible-or-definite graph once, after filtering include-site
    conditions, so cycles/diamonds terminate without losing host reachability.
    Only existing owned runtime files reached by quoted local includes count;
    angle/computed includes and arbitrary preprocessor macro state stay outside
    this source-only mapping evidence.
    """
    runtime = os.path.realpath(os.path.join(root, 'src/runtime'))

    def owned(path):
        path = os.path.realpath(path)
        if os.path.commonpath((runtime, path)) != runtime:
            return None
        rel = os.path.relpath(path, runtime)
        if any(part in ('vendor', 'test', 'target') for part in rel.split(os.sep)):
            return None
        if rel in EXTERNAL_RUNTIME_HEADERS or not os.path.isfile(path):
            return None
        return path

    roots = [(p, file_host(p)) for p in files(root, 'src/runtime', ('.c', '.cpp', '.m', '.mm'))
             if owned(p)]
    cache = {}
    for h in HOSTS:
        for definite_only in (False, True):
            pending = [os.path.realpath(p) for p, only in roots if only in (None, h)]
            seen = set()
            while pending:
                path = pending.pop()
                if path in seen:
                    continue
                seen.add(path)
                if path not in cache:
                    cache[path] = C_COMMENT_STRING.sub(
                        lambda m: m[0] if m[0].startswith('"') else ' ' + '\n' * m[0].count('\n'), read(path))
                view = host_view(cache[path], h, definite_only)
                yield h, definite_only, path, view
                for name in LOCAL_INCLUDE.findall(view):
                    # Do not follow absolute paths, symlink escapes or vendor
                    # trees, even when a local include happens to name them.
                    if os.path.isabs(name):
                        continue
                    child = owned(os.path.join(os.path.dirname(path), name))
                    if child:
                        pending.append(child)


def provider_definitions(src):
    """External definitions from comment/string/attribute-stripped C text.

    A candidate's declaration extends back to the preceding ;/{/} boundary,
    not merely its return-type line. Scan those bounded segments once so a
    storage qualifier on an earlier line cannot turn a private helper public.
    Preprocessor directive tokens are not C declaration qualifiers.
    """
    src = re.sub(r'^[ \t]*#[^\n]*', '', src, flags=re.M)
    segments = re.split(r'([;{}])', src)
    for i in range(1, len(segments), 2):
        if segments[i] != '{':
            continue
        declaration = segments[i - 1]
        match = DEF.search(declaration + '{')
        if match and not re.search(r'\bstatic\b', declaration[:match.end(1)]):
            yield match[1]


def scan(root):
    prov, rust, decl, _definite = scan_detail(root)
    return prov, rust, decl


def scan_detail(root):
    """scan() plus, per host, the providers whose guard is definitely true for that host.
    definite[h] is a subset of prov[h]; prov[h] - definite[h] are conditional providers
    (kept only because a non-host macro evaluated unknown). Verdicts use prov only."""
    prov = {h: set() for h in HOSTS}
    definite = {h: set() for h in HOSTS}
    for h, definite_only, _path, view in c_provider_views(root):
        src = re.sub(r'__attribute__\s*\(\((?:[^()]|\([^()]*\))*\)\)', ' ', C_STRING.sub(' ', view))
        target = definite if definite_only else prov
        target[h].update(provider_definitions(src))
    definite = {h: definite[h] & prov[h] for h in HOSTS}
    rust = set()
    for rel in ('src/compiler_rust/runtime/src', 'src/runtime'):
        for p in files(root, rel, ('.rs',)):
            rust.update(RUST.findall(read(p)))
    decl = set()
    for top in ('src/compiler', 'src/lib', 'src/app', 'src/os'):
        for p in files(root, top, ('.spl',)):
            decl.update(EXT.findall(read(p)))
    return prov, rust, decl, definite


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
    print('coverage edges=%d rust_skipped_UNKNOWN=%d no_provider=%d' % (len(edges), len(decl & rust), len(decl - anyhost - rust)))
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
        os.makedirs(os.path.dirname(t + '/src/runtime/' + name), exist_ok=True)
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
        (body, 'windows/a.c', 1),
        ('#if defined(__linux__)\n' + body + '#endif\n', 'io_common.c', 1),
        (body, 'startup/baremetal/a.c', 2),
        ('#ifndef __APPLE__\nint y;\n#else\n' + body + '#endif\n', 'a.c', 1),
        ('#if defined(__linux__) || \\\n defined(__APPLE__)\n' + body + '#endif\n', 'a.c', 1),
        ('#if __linux__\n' + body + '#endif\n', 'a.c', 1),
        ('#if defined(__unix__)\n' + body + '#endif\n', 'a.c', 1),
        ('#if 0\n' + body + '#endif\n', 'a.c', 2),
        ('static long rt_x(void) { return 1; }\n', 'a.c', 2),
    ]):
        got = run(tree(c, name), False)
        if got != want:
            print('ERROR — selftest case %d wanted %d got %d' % (i, want, got))
            return 2
    if include_selftest() != 0:
        return 2
    print('PASS — selftest 14 existing + include traversal cases')
    return 0


def include_selftest():
    # Actual files drive scan_detail; no mocked include graph or mirrored parser.
    with tempfile.TemporaryDirectory(prefix='rt_host_include_') as root:
        bodies = {
            'src/runtime/root_linux.c': '#include "guarded.h"\n',
            'src/runtime/main.c': (
                '#include "shared.h"\n#include "diamond.h"\n'
                '#if defined(__linux__)\n#include "linux_only.h"\n#endif\n'
                '#if defined(FEATURE_X)\n#include "unknown.h"\n#endif\n'
                '#if 0\n#include "disabled.h"\n#endif\n'
                '#include "vendor/foreign.h"\n#include "escape.h"\n'
                '#include "../../outside.h"\n#include <unrelated.h>\n'
                '#include COMPUTED_HEADER\n'
                '/* #include "unrelated.h" */\n'
                'const char *s = "long rt_fake(void) { return 0; }";\n'),
            'src/runtime/shared.h': (
                '#include "nested/leaf.h"\n#include "cycle.h"\n'
                'long rt_shared(void) { return 1; }\n'
                'long rt_prototype(void);\n'
                '    static long rt_static(void) { return 1; }\n'
                'inline static long rt_static_inline(void) { return 1; }\n'
                'static\nint64_t rt_multiline_static(void) { return 1; }\n'
                'inline\nstatic\nlong rt_inline_static(void) { return 1; }\n'
                'static\ninline\nlong rt_static_reordered(void) { return 1; }\n'
                'inline\nlong rt_public_inline(void) { return 1; }\n'),
            'src/runtime/diamond.h': '#include "nested/leaf.h"\n',
            'src/runtime/cycle.h': '#include "shared.h"\n',
            'src/runtime/nested/leaf.h': 'long rt_leaf(void) { return 1; }\n',
            'src/runtime/guarded.h': 'long rt_root_host(void) { return 1; }\n',
            'src/runtime/linux_only.h': 'long rt_include_host(void) { return 1; }\n',
            'src/runtime/unknown.h': 'long rt_unknown(void) { return 1; }\n',
            'src/runtime/disabled.h': 'long rt_disabled(void) { return 1; }\n',
            'src/runtime/unrelated.h': 'long rt_unrelated(void) { return 1; }\n',
            'src/runtime/vendor/foreign.h': 'long rt_vendor(void) { return 1; }\n',
            'outside.h': 'long rt_escape(void) { return 1; }\n',
        }
        for rel, body in bodies.items():
            path = os.path.join(root, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, 'w') as f:
                f.write(body)
        try:
            os.symlink(os.path.join(root, 'outside.h'), os.path.join(root, 'src/runtime/escape.h'))
        except OSError as exc:
            # Windows commonly requires an elevated token or Developer Mode.
            # Report only that known capability gap; other failures are real.
            if os.name == 'nt' and getattr(exc, 'winerror', None) == 1314:
                print('UNTESTED — symlink-escape fixture: Windows symlink privilege unavailable')
            else:
                raise
        else:
            print('PASS — symlink-escape fixture: real symlink outside owned runtime')
        prov, _rust, _decl, definite = scan_detail(root)
        for h in HOSTS:
            want = {'rt_shared', 'rt_leaf', 'rt_unknown', 'rt_public_inline'}
            if h == 'linux':
                want.update(('rt_root_host', 'rt_include_host'))
            if prov[h] != want or definite[h] != want - {'rt_unknown'}:
                print('ERROR — include selftest host %s possible=%s definite=%s' %
                      (h, sorted(prov[h]), sorted(definite[h])))
                return 2
        views = list(c_provider_views(root))
        keys = [(h, mode, path) for h, mode, path, _ in views]
        if len(keys) != len(set(keys)):
            print('ERROR — include selftest visited a cycle/diamond more than once')
            return 2
        leaf = os.path.join(root, 'src/runtime/nested/leaf.h')
        if not any(h == 'linux' and path == leaf and 'rt_leaf' in view
                   for h, _mode, path, view in views):
            print('ERROR — include selftest lost header definition provenance')
            return 2
    print('PASS — include fixtures: definitions/static/prototypes/nested/conditions/cycles/diamonds/owned paths')
    return 0


def main():
    a = sys.argv[1:]
    if '--selftest' in a:
        return selftest()
    root = a[a.index('--root') + 1] if '--root' in a else os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
    return run(root, '--regen-baseline' in a)


if __name__ == '__main__':
    sys.exit(main())
