#!/usr/bin/env python3
# Wave 4C driver. Usage: driver4.py <count> — process next N from .w4.txt
import subprocess, sys, os, filecmp
sys.path.insert(0, '/tmp/mod9')
os.chdir('/tmp/mod9')
import importlib.util
spec = importlib.util.spec_from_file_location('t', '/tmp/mod9/.transform.py')
T = importlib.util.module_from_spec(spec); spec.loader.exec_module(T)

BIN = '/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple'
SBIN = '/mnt/data/worktrees/simple-main/bin/simple'
MAINT = '/mnt/data/worktrees/simple-main/src/app/sspec_maintain/main.spl'
DEBT = {'ORA-001', 'ORA-002', 'TRC-002', 'TRC-003'}
TWIN = [('test/01_unit/', 'test/unit/'), ('test/02_integration/', 'test/integration/'),
        ('test/00_formal_verification/', 'test/formal_verification/'), ('test/03_system/', 'test/system/')]

def twin_of(p):
    for a, b in TWIN:
        if p.startswith(a):
            return b + p[len(a):]
    return None

def scan_codes(path):
    try:
        r = subprocess.run([SBIN, MAINT, 'scan', path], capture_output=True, text=True,
                           cwd='/tmp/mod9', timeout=400)
    except Exception:
        return None  # scan failed — cannot classify
    codes = set()
    for l in r.stdout.splitlines():
        if 'SSDOC-' in l:
            for c in ('NAR-001','TRC-001','TRC-002','TRC-003','MNT-001','MNT-002','MNT-005',
                      'MNT-007','MNT-008','BEH-001','BEH-002','EVD-001','EVD-002','ORA-001','ORA-002','ORA-003'):
                if 'SSDOC-' + c in l:
                    codes.add(c)
    return codes

def run_test(path):
    try:
        r = subprocess.run(['timeout', '480', BIN, 'test', '--no-session-daemon', path],
                           capture_output=True, text=True, cwd='/tmp/mod9')
    except Exception as e:
        return 'EXC|%s' % e
    res = ''
    for l in (r.stdout + r.stderr).splitlines():
        if l.startswith('Results:'):
            res = l
        elif l.startswith('SPEC FILE VERDICT:'):
            res += '|' + l
    return 'rc=%d|%s' % (r.returncode, res)

def probe(path):
    r = subprocess.run([SBIN, 'probe_sspec_scores.spl', '/tmp/mod9/' + path],
                       capture_output=True, text=True, cwd='/mnt/data/worktrees/simple-main')
    lines = r.stdout.strip().splitlines()
    if lines:
        cols = lines[-1].split('\t')
        if len(cols) >= 2:
            try:
                return int(cols[1])
            except ValueError:
                return -1
    return -1

N = int(sys.argv[1])
todo = [l.strip() for l in open('.w4.txt') if l.strip()]
kept, fast, debt, skip = [], [], [], []
handled = set()

def rec(fname, s):
    with open(fname, 'a') as f:
        f.write(s + '\n')

for path in todo[:N]:
    if not os.path.exists(path):
        handled.add(path); continue
    codes = scan_codes(path)
    if codes is None:
        rec('.w4skip.txt', '%s\tscan-failed' % path); skip.append(path)
        handled.add(path); continue
    if codes & DEBT:
        rec('.w4skip.txt', '%s\tORA-DEBT %s' % (path, ','.join(sorted(codes & DEBT))))
        debt.append(path); handled.add(path); continue
    s = probe(path)
    if s > 80:
        rec('.w4done.txt', path); fast.append(path)
        handled.add(path); continue
    tw = twin_of(path)
    has_twin = tw and os.path.exists(tw)
    ident = has_twin and filecmp.cmp(path, tw, shallow=False)
    pre = run_test(path)
    rid = T.req_id_for(path, open(path).read())
    T.transform(path, rid)
    if has_twin:
        if ident:
            open(tw, 'w').write(open(path).read())
        else:
            T.transform(tw, rid)
    post = run_test(path)
    score = probe(path)
    ok = (pre == post) or ('rc=124' in pre and 'rc=124' in post) or ('EXC' in pre and 'EXC' in post)
    if (not ok) or score <= 80 or pre in ('', '|') or 'rc=124' in pre or 'EXC' in pre:
        pl = [path] + ([tw] if has_twin else [])
        subprocess.run(['git', 'checkout', '--'] + pl, cwd='/tmp/mod9')
        rec('.w4skip.txt', '%s\tpost-%s-verify(%s)' % (path, score, 'same' if ok else 'DIFF'))
        skip.append(path); print('%s FAIL score=%s' % (path, score)); sys.stdout.flush()
        handled.add(path); continue
    rec('.w4done.txt', path)
    kept.append(path)
    print('%s KEPT score=%d' % (path, score)); sys.stdout.flush()
    handled.add(path)

open('.w4.txt', 'w').write('\n'.join(l for l in todo if l not in handled) + '\n')
print('SUMMARY kept=%d fast=%d debt=%d skip=%d' % (len(kept), len(fast), len(debt), len(skip)))
