#!/usr/bin/env python3
# Driver: process a slice of .targets.txt. Usage: driver.py <start> <end>
import subprocess, sys, os, filecmp
sys.path.insert(0, '/tmp/mod6')
os.chdir('/tmp/mod6')
import importlib.util
spec = importlib.util.spec_from_file_location('t', '/tmp/mod6/.transform.py')
T = importlib.util.module_from_spec(spec); spec.loader.exec_module(T)

TWIN = [('test/01_unit/', 'test/unit/'), ('test/00_formal_verification/', 'test/formal_verification/'),
        ('test/02_integration/', 'test/integration/'), ('test/03_system/', 'test/system/'),
        ('test/unit/', 'test/01_unit/'), ('test/formal_verification/', 'test/00_formal_verification/'),
        ('test/integration/', 'test/02_integration/'), ('test/system/', 'test/03_system/')]

def twin_of(path):
    for a, b in TWIN:
        if path.startswith(a):
            return b + path[len(a):]
    return None

def run_test(path):
    try:
        r = subprocess.run(['timeout', '240', 'bin/simple', 'test', path],
                           capture_output=True, text=True, cwd='/tmp/mod6')
        res = ''
        for l in (r.stdout + r.stderr).splitlines():
            if l.startswith('Results:'):
                res = l
        return 'rc=%d|%s' % (r.returncode, res)
    except Exception as e:
        return 'EXC|%s' % e

def probe(path):
    r = subprocess.run(['bin/simple', 'probe_sspec_scores.spl', '/tmp/mod6/' + path],
                       capture_output=True, text=True, cwd='/mnt/data/worktrees/simple-main')
    for l in r.stdout.splitlines():
        if l.startswith(path + '\t') or l.endswith('\t' + path.split('/')[-1]):
            pass
    line = r.stdout.strip().splitlines()
    if line:
        cols = line[-1].split('\t')
        if len(cols) >= 2:
            try:
                return int(cols[1])
            except ValueError:
                return -1
    return -1

def revert(paths):
    subprocess.run(['git', 'checkout', '--'] + paths, cwd='/tmp/mod6')

start, end = int(sys.argv[1]), int(sys.argv[2])
targets = [l.strip() for l in open('/tmp/mod6/.targets.txt') if l.strip()][start:end]
done = set(l.strip() for l in open('/tmp/mod6/.done.txt')) if os.path.exists('/tmp/mod6/.done.txt') else set()

kept, reverted, failed = [], [], []
for path in targets:
    if path in done or not os.path.exists(path):
        continue
    tw = twin_of(path)
    has_twin = tw and os.path.exists(tw)
    identical_twin = has_twin and filecmp.cmp(path, tw, shallow=False)
    pre = run_test(path)
    if 'rc=124' in pre or 'EXC' in pre:
        print('%s PRETIMEOUT %s' % (path, pre)); sys.stdout.flush()
    rid = T.req_id_for(path, open(path).read())
    T.transform(path, rid)
    if has_twin:
        if identical_twin:
            open(tw, 'w').write(open(path).read())
        else:
            T.transform(tw, rid)
    post = run_test(path)
    score = probe(path)
    ok_counts = (pre == post) or ('rc=124' in pre and 'rc=124' in post)
    if not ok_counts or score <= 80:
        pl = [path] + ([tw] if has_twin else [])
        revert(pl)
        failed.append((path, score, pre, post, ok_counts))
        print('%s REVERT score=%s counts_ok=%s' % (path, score, ok_counts)); sys.stdout.flush()
        continue
    with open('/tmp/mod6/.done.txt', 'a') as f:
        f.write(path + '\n')
    kept.append(path)
    print('%s KEPT score=%d' % (path, score)); sys.stdout.flush()

print('SUMMARY kept=%d failed=%d' % (len(kept), len(failed)))
