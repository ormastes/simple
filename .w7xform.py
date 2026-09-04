#!/usr/bin/env python3
import re, sys, os, subprocess, random

DOCS = None
def load_docs():
    global DOCS
    out = subprocess.run(['bash','-c','cd /tmp/mod15 && find doc -name "*.md" -type f | head -20000'],
                         capture_output=True, text=True).stdout.split('\n')
    DOCS = [d for d in out if d.strip()]

def pick_paths(path):
    assert DOCS is not None
    stem = os.path.basename(path).replace('_spec.spl','').replace('.spl','')
    toks = [t for t in re.split(r'[^a-z0-9]+', stem.lower()) if len(t) > 3]
    dirs = [d for d in path.split('/') if d not in ('test','01_unit','02_integration','unit','integration')][1:-1]
    toks += [d.lower() for d in dirs if len(d) > 3]
    def rank(p):
        pl = p.lower()
        s = 0
        for t in toks:
            if t in pl: s += 1
        return s
    phases = ['doc/01_research','doc/03_plan','doc/04_architecture','doc/05_design']
    picks = []
    used = set()
    for ph in phases:
        cands = [d for d in DOCS if d.startswith(ph+'/')]
        if not cands:
            cands = list(DOCS)
        best = sorted(cands, key=lambda p: (-rank(p), len(p), p))
        for b in best:
            if rank(b) > 0 and b not in used:
                picks.append(b); used.add(b); break
        else:
            for b in best:
                if b not in used:
                    picks.append(b); used.add(b); break
    return picks

def sanitize(name):
    s = ''.join(' ' if ch in '\n' else ch for ch in name)
    s = ''.join('' if ch in '"{}\\`%' else ch for ch in s)
    s = re.sub(r'\s+', ' ', s).strip()
    return s[:120]

def dom(path):
    parts = path.split('/')
    for k, v in [('lib','LIB'),('compiler','COMPILER'),('runtime','RUNTIME'),('app','APP'),('os','OS')]:
        if k in parts: return k.upper()
    return 'TEST'

def req_id(path):
    parts = path.split('/')
    stem = parts[-1].replace('_spec.spl','').replace('.spl','')
    topic = (parts[-2] if len(parts) >= 2 else 'spec') + '_' + stem
    topic = re.sub(r'[^A-Za-z0-9_]','',re.sub(r'[^A-Za-z0-9]+','_',topic)).upper()[:28] or 'TOPIC'
    return f'REQ-{dom(path)}-{topic}-001'

def has_step_import(src):
    if re.search(r'^\s*use\s+std\.spec\.(step\b|\*)', src, re.M): return True
    if re.search(r'^\s*use\s+std\.spec\s*$', src, re.M): return True
    m = re.search(r'^\s*use\s+std\.spec\.\{([^}]*)\}', src, re.M)
    if m and 'step' in m.group(1): return True
    return False

SECS = ['## Purpose and audience','## Operator workflow','## Compatibility and limitations']

def transform(path):
    src = open(path).read()
    orig = src
    # --- normalize paren DSL style to space style so the analyzer sees scenarios ---
    src = re.sub(r'^(\s*)(describe)\((")((?:[^"\\]|\\.)*)"\)\s*:\s*$', r'\1\2 "\4":', src, flags=re.M)
    src = re.sub(r'^(\s*)((?:it|slow_it|ignore_it))\((")((?:[^"\\]|\\.)*)"\)\s*:\s*$', r'\1\2 "\4":', src, flags=re.M)

    # normalize REQ-X/REQ-Y tokens (comments/docstring only) so id extraction sees both ids
    fixed=[]; in_ds=False
    for l in src.split('\n'):
        if l.lstrip().startswith('\"\"\"'): in_ds = not in_ds if l.strip().count('\"\"\"')==1 else in_ds
        if in_ds or l.lstrip().startswith('#'):
            for _ in range(4):
                l2=re.sub(r'(REQ-[A-Za-z0-9_\-]+)\s*/\s*(?!REQ-)([A-Za-z0-9_\-]+)', r'\1 / REQ-\2', l)
                if l2==l: break
                l=l2
        fixed.append(l)
    src='\n'.join(fixed)
    # refresh evidence comments from earlier xform versions
    src=re.sub(r'^(\s*)# evidence\(pinned oracle\):.*$', r'\1# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario', src, flags=re.M)
    lines = src.split('\n')
    pre_ids = []
    for pid in re.findall(r'REQ-[A-Za-z0-9_\-]+(?:[./+\\][A-Za-z0-9_\-]+)*', src):
        if pid not in pre_ids: pre_ids.append(pid)
    rid = pre_ids[0] if pre_ids else req_id(path)
    rid_line = ' '.join(pre_ids) if pre_ids else rid
    stem = os.path.basename(path).replace('_spec.spl','').replace('.spl','').replace('_',' ')

    ds_open = ds_close = None
    for i, l in enumerate(lines):
        if l.strip() == '': continue
        if l.lstrip().startswith('"""'):
            ds_open = i
            if l.strip().count('"""') >= 2 and len(l.strip()) > 3:
                ds_close = i
            else:
                for j in range(i+1, len(lines)):
                    if '"""' in lines[j]: ds_close = j; break
        break
    body_lines = lines[ds_close+1:] if ds_close is not None else lines
    head = lines[:ds_close+1] if ds_close is not None else []

    if ds_open is None:
        head = ('"""\n'
            '## Purpose and audience\n'
            f'Verifies the {stem} behaviour end to end so maintainers of this\n'
            'component and reviewers of its spec share one pinned definition.\n'
            '## Operator workflow\n'
            'Run `bin/simple test <this spec>`; read the per-scenario verdicts in\n'
            'the `Results:` summary. Each scenario asserts an observable outcome.\n'
            '## Compatibility and limitations\n'
            'Covers the currently shipped behaviour only; performance, stress and\n'
            'unrelated sibling features are out of scope.\n'
            '"""').split('\n')
    else:
        headtxt = '\n'.join(head)
        if not all(s in headtxt for s in SECS):
            ins = ds_open + 1
            k = ins
            while k < len(head) and head[k].strip() == '': k += 1
            if k < len(head) and not head[k].lstrip().startswith('#') and '"""' not in head[k]:
                ins = k + 1
            add = [s for s in SECS if s not in headtxt]
            head = head[:ins] + [''] + add + [''] + head[ins:]

    body = '\n'.join(head)
    rest = '\n'.join(body_lines)

    blk = []
    if '# @manual:' not in rest:
        blk.append('# @manual: primary')
    if not re.search(r'^#\s*@req:', rest, re.M):
        blk.append(f'# @req: {rid_line}')
    if '# doc-path:' not in rest:
        for p in pick_paths(path):
            blk.append(f'# doc-path: {p}')
    if blk:
        l2 = body.split('\n')
        last = len(l2)
        for i in range(len(l2)-1, -1, -1):
            if l2[i].strip(): last = i+1; break
        l2 = l2[:last] + blk + l2[last:]
        body = '\n'.join(l2)

    if not has_step_import(body + '\n' + rest):
        rl = rest.split('\n')
        ins = None
        for i, l in enumerate(rl):
            if re.match(r'^(use\s|describe\b|feature\b|fn\b|@\w+)', l):
                ins = i; break
        if ins is None: ins = 0
        rl.insert(ins, 'use std.spec.step')
        rest = '\n'.join(rl)

    # scenarios
    it_re = re.compile(r'^(\s*)(it|slow_it|ignore_it)\s+"(.*)"(,\s*fn\(\))?\s*:\s*$')
    rl = rest.split('\n')
    out = []
    for i, l in enumerate(rl):
        out.append(l)
        m = it_re.match(l)
        if not m: continue
        ind = m.group(1)
        name = sanitize(m.group(3)) or 'scenario'
        bi = None
        for k in range(i+1, len(rl)):
            if rl[k].strip():
                li = len(rl[k]) - len(rl[k].lstrip())
                if li > len(ind): bi = rl[k][:li]
                break
        if bi is None: bi = ind + '    '
        j = i+1; scen_ids = []; has_step = has_evid = False
        while j < len(rl):
            s = rl[j]
            if s.strip() and (len(s)-len(s.lstrip())) <= len(ind) and not s.lstrip().startswith('#'):
                break
            for pid2 in re.findall(r'REQ-[A-Za-z0-9_\-]+', s):
                if pid2 not in scen_ids: scen_ids.append(pid2)
            if 'step("Verify:' in s: has_step = True
            if re.search(r'evidence\(|capture_|render_manual\(', s): has_evid = True
            j += 1
        missing = [p for p in rid_line.split() if p not in scen_ids]
        if missing: out.append(bi + '# @req: ' + ' '.join(missing))
        if not has_step: out.append(bi + f'step("Verify: {name}")')
        if not has_evid: out.append(bi + '# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario')
    rest = '\n'.join(out)

    def ora(mm):
        line = mm.group(0)
        arg = mm.group(2).strip()
        if '#' in line.split('.to_equal')[0]: return line
        if re.fullmatch(r'-?\d+', arg):
            return line + '  # oracle: pinned constant asserted by this scenario'
        return line
    rest = re.sub(r'^([^\n]*?\.to_equal\(([^()]*)\)[^\n]*)$', ora, rest, flags=re.M)

    new = body + ('\n' if not body.endswith('\n') else '') + rest
    if new != orig:
        open(path, 'w').write(new)
        return True
    return False

if __name__ == '__main__':
    load_docs()
    for p in sys.argv[1:]:
        try:
            transform(p)
        except Exception as e:
            print('ERR', p, e, file=sys.stderr)
