#!/usr/bin/env python3
"""rt-binding-index.py: R1 metadata index of rt_ externs, MAPPING and POINTER evidence only.

One record per `extern fn rt_x` declaration under src/compiler, src/lib, src/app and src/os.
Each record carries a stable interface id (sha256 of symbol and canonical signature,
first 16 hex), one provider row per host profile, and separate verdict fields:

  map      PASS when a C provider is found on every hosted profile (linux, macos,
           windows, freebsd) and every one of those rows is definite; UNKNOWN when any
           hosted row is conditional (its guard used a non-host macro, so the provider
           was kept on an unknown branch), when no C provider is found, or when the
           symbol has a Rust export; FAIL when some hosted profile has no provider
           (host gap) and no hosted row is conditional.
  pointer  from check-rt-pointer-ref-map.py rules: PASS (enforced or nullable-declared),
           FAIL (nil-mismatch or narrow-pointer), UNKNOWN otherwise. Never PASS on a
           bare-typed edge whose C return is not proven.
  compile  always UNTESTED. link  always UNTESTED.

Provider state per hosted profile: `mapped` when check-rt-host-map.py's scan_detail found
a provider whose guard is definitely true on that host; `conditional` when the provider is
kept only through an unknown (non-host) macro; else `unknown` (a text scan that found
nothing is not a claim of absence). The simpleos profile is always `unknown`: no C macro
selects it.

The two guards are loaded with importlib and their scan() and regex helpers are reused.
Their behavior is unchanged; this script never writes a baseline and never prints their
verdicts. Output is versioned JSON with sorted keys and no timestamps, so two runs over
the same tree are byte-identical.

Metadata only: the exit code reports whether the index was produced, not whether the
externs are correct. The summary line goes to stderr, so stdout is pure JSON when --out is omitted.
Exit 0 written, 2 nothing checked, 1 selftest failure.
Usage: rt-binding-index.py [--root DIR] [--out PATH] [--selftest]
"""
import hashlib
import importlib.util
import json
import os
import sys
import tempfile

SCHEMA = 'rt-binding-index'
VERSION = 1
HERE = os.path.dirname(os.path.abspath(__file__))
TOPS = ('src/compiler', 'src/lib', 'src/app', 'src/os')
HOSTED = ('linux', 'macos', 'windows', 'freebsd')
RAW = ('i64', 'u64', 'usize', 'isize', 'void')
HOST_NOTE = {'simpleos': 'no C macro selects SimpleOS; always unknown, never mapped'}


def load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, rel))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def c_pointer_states(pm, root):
    """symbol -> nil | enforced | seen | unknown. Same loop as check-rt-pointer-ref-map.py scan()."""
    c = {}
    for path in pm.walk(root, 'src/runtime', ('.c', '.h')):
        src = pm.ATTR.sub('', pm.NOISE.sub(' ', pm.read(path)))
        for m in pm.CDEF.finditer(src):
            body = pm.body_after(src, m.end() - 1)
            state = c.get(m[1], 'unknown')
            if body is not None:
                kind = pm.classify(body)
                if pm.RANK[kind] > pm.RANK[state]:
                    state = kind
            c[m[1]] = state
    return c


def canonical_signature(pm, params, ret):
    parts = pm.split_top(' '.join(params.split()))
    types = [p.split(':', 1)[1].strip() if ':' in p else p for p in parts]
    return '(%s) -> %s' % (', '.join(' '.join(t.split()) for t in types), ' '.join((ret or 'void').split()))


def provider_state(h, sym, prov, definite):
    if h not in HOSTED:
        return 'unknown'
    if sym in definite[h]:
        return 'mapped'
    if sym in prov[h]:
        return 'conditional'
    return 'unknown'


def map_verdict(sym, states, rust):
    if sym in rust:
        return 'UNKNOWN', 'rust-export, cfg not evaluated'
    if any(states[h] == 'conditional' for h in HOSTED):
        return 'UNKNOWN', 'conditional-provider-on-hosted-profile'
    got = [h for h in HOSTED if states[h] == 'mapped']
    if not got:
        return 'UNKNOWN', 'no-c-provider-in-scan'
    if len(got) == len(HOSTED):
        return 'PASS', 'mapped-on-all-hosted-profiles'
    return 'FAIL', 'host-gap-on-%d-hosted-profile(s)' % (len(HOSTED) - len(got))


def pointer_verdict(sym, ty, c):
    if sym not in c:
        return 'UNKNOWN', 'no-c-pointer-definition'
    base = ty.rstrip('?')
    if base in ('i8', 'i16', 'i32', 'u8', 'u16', 'u32', 'bool', 'f32', 'f64'):
        return 'FAIL', 'narrow-pointer'
    if base in RAW:
        return 'UNKNOWN', 'raw-handle'
    if ty.endswith('?'):
        if c[sym] == 'nil':
            return 'PASS', 'nullable-declared'
        return 'UNKNOWN', 'nullable-declared-c-unproven'
    if c[sym] == 'nil':
        return 'FAIL', 'nil-mismatch'
    if c[sym] == 'enforced':
        return 'PASS', 'enforced'
    return 'UNKNOWN', 'c-return-unproven'


def build(root):
    pm = load('check_rt_pointer_ref_map', 'check-rt-pointer-ref-map.py')
    hm = load('check_rt_host_map', 'check-rt-host-map.py')
    prov, rust, _decl, definite = hm.scan_detail(root)
    c = c_pointer_states(pm, root)
    records = []
    for top in TOPS:
        for path in hm.files(root, top, ('.spl',)):
            src = hm.read(path)
            rel = os.path.relpath(path, root)
            for m in pm.EXT.finditer(src):
                sym, params, ret = m[1], m[2], (m[3] or 'void').strip()
                sig = canonical_signature(pm, params, ret)
                states = {h: provider_state(h, sym, prov, definite) for h in hm.HOSTS}
                map_v, map_r = map_verdict(sym, states, rust)
                ptr_v, ptr_r = pointer_verdict(sym, ret, c)
                records.append({
                    'id': hashlib.sha256((sym + '\n' + sig).encode()).hexdigest()[:16],
                    'symbol': sym,
                    'path': rel,
                    'signature': sig,
                    'providers': [{'host': h, 'state': states[h]} for h in hm.HOSTS],
                    'verdict': {'map': map_v, 'map_reason': map_r,
                                'pointer': ptr_v, 'pointer_reason': ptr_r,
                                'compile': 'UNTESTED', 'link': 'UNTESTED'},
                })
    records.sort(key=lambda r: (r['path'], r['symbol'], r['signature']))
    tally = {k: {'PASS': 0, 'FAIL': 0, 'UNKNOWN': 0} for k in ('map', 'pointer')}
    for r in records:
        for k in tally:
            tally[k][r['verdict'][k]] += 1
    return {
        'schema': SCHEMA,
        'version': VERSION,
        'map_scope': list(HOSTED),
        'host_notes': HOST_NOTE,
        'summary': {'records': len(records), 'tally': tally,
                    'compile': 'UNTESTED', 'link': 'UNTESTED'},
        'records': records,
    }


def render(doc):
    return json.dumps(doc, sort_keys=True, indent=2) + '\n'


def selftest():
    def tree(runtime_c, spl):
        t = tempfile.mkdtemp()
        for d in ('src/runtime', 'src/lib', 'scripts/check'):
            os.makedirs(os.path.join(t, d))
        open(os.path.join(t, 'src/runtime/a.c'), 'w').write(runtime_c)
        open(os.path.join(t, 'src/lib/a.spl'), 'w').write(spl)
        return t

    runtime_c = (
        'char *rt_ok(void) {\n  return SIMPLE_RT_NONNULL(b);\n}\n'
        'char *rt_nil(void) {\n  if (a) return NULL;\n  return b;\n}\n'
        '#if defined(__linux__)\nlong rt_linux_only(void) { return 1; }\n#endif\n'
        '#ifdef SOME_FEATURE_X\nlong rt_feature_gated(void) { return 1; }\n#endif\n')
    spl = ('extern fn rt_ok() -> text\n'
           'extern fn rt_nil() -> text\n'
           'extern fn rt_linux_only() -> i64\n'
           'extern fn rt_feature_gated() -> i64\n'
           'extern fn rt_missing(x: i64) -> i64\n')
    fails = []
    root = tree(runtime_c, spl)
    first = render(build(root))
    second = render(build(root))
    if first != second:
        fails.append('two runs differ')
    doc = json.loads(first)
    by = {r['symbol']: r for r in doc['records']}
    want = {
        'rt_ok': ('PASS', 'PASS'),
        'rt_nil': ('PASS', 'FAIL'),
        'rt_linux_only': ('FAIL', 'UNKNOWN'),
        'rt_feature_gated': ('UNKNOWN', 'UNKNOWN'),
        'rt_missing': ('UNKNOWN', 'UNKNOWN'),
    }
    for sym, (mv, pv) in want.items():
        r = by.get(sym)
        if r is None:
            fails.append('missing record ' + sym)
            continue
        if r['verdict']['map'] != mv or r['verdict']['pointer'] != pv:
            fails.append('%s map=%s pointer=%s, wanted %s %s' % (
                sym, r['verdict']['map'], r['verdict']['pointer'], mv, pv))
    gated = by.get('rt_feature_gated')
    if gated is not None:
        if gated['verdict']['map_reason'] != 'conditional-provider-on-hosted-profile':
            fails.append('rt_feature_gated map reason is %s, wanted conditional-provider-on-hosted-profile'
                         % gated['verdict']['map_reason'])
        states = {p['host']: p['state'] for p in gated['providers']}
        if states.get('linux') != 'conditional' or states.get('windows') != 'conditional':
            fails.append('rt_feature_gated provider states are not conditional on hosted profiles')
    if by.get('rt_nil', {}).get('verdict', {}).get('pointer_reason') != 'nil-mismatch':
        fails.append('rt_nil pointer reason is not nil-mismatch')
    for r in doc['records']:
        if r['verdict']['compile'] != 'UNTESTED' or r['verdict']['link'] != 'UNTESTED':
            fails.append('compile/link not UNTESTED on ' + r['symbol'])
        for p in r['providers']:
            if p['host'] == 'simpleos' and p['state'] != 'unknown':
                fails.append('simpleos row not unknown on ' + r['symbol'])
    if len(by['rt_ok']['id']) != 16:
        fails.append('interface id is not 16 hex characters')
    changed = {r['symbol']: r for r in json.loads(render(build(
        tree(runtime_c, spl.replace('extern fn rt_ok() -> text', 'extern fn rt_ok() -> i64', 1)))))['records']}
    if changed['rt_ok']['id'] == by['rt_ok']['id']:
        fails.append('interface id did not change with the signature')
    if changed['rt_nil']['id'] != by['rt_nil']['id']:
        fails.append('interface id changed for an unchanged signature')
    if fails:
        for f in fails:
            print('SELFTEST FAIL: ' + f)
        print('ERROR — selftest %d failure(s)' % len(fails))
        return 1
    print('PASS — selftest 5 records, #ifdef conditional provider is UNKNOWN, 2 runs byte-identical, simpleos unknown, compile/link UNTESTED')
    return 0


def main():
    a = sys.argv[1:]
    if '--selftest' in a:
        return selftest()
    root = a[a.index('--root') + 1] if '--root' in a else os.path.abspath(os.path.join(HERE, '../..'))
    doc = build(root)
    if doc['summary']['records'] == 0:
        print('ERROR — nothing was checked (0 extern records)')
        return 2
    text = render(doc)
    if '--out' in a:
        out = a[a.index('--out') + 1]
        d = os.path.dirname(os.path.abspath(out))
        os.makedirs(d, exist_ok=True)
        with open(out, 'w') as f:
            f.write(text)
        dest = out
    else:
        sys.stdout.write(text)
        dest = 'stdout'
    t = doc['summary']['tally']
    print('RT_BINDING_INDEX version=%d records=%d map=PASS:%d/FAIL:%d/UNKNOWN:%d pointer=PASS:%d/FAIL:%d/UNKNOWN:%d compile=UNTESTED link=UNTESTED out=%s' % (
        VERSION, doc['summary']['records'], t['map']['PASS'], t['map']['FAIL'], t['map']['UNKNOWN'],
        t['pointer']['PASS'], t['pointer']['FAIL'], t['pointer']['UNKNOWN'], dest), file=sys.stderr)
    return 0


if __name__ == '__main__':
    sys.exit(main())
