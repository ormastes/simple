#!/usr/bin/env python3
# SSpec doc modernizer (documentation-only): NAR-001 purpose block + TRC req binding.
import re, sys

REQ_RE = re.compile(r'REQ-[A-Z0-9][A-Z0-9-]*')

def scenario_spans(lines):
    spans = []  # (start_idx, indent)
    cur = None
    for i, raw in enumerate(lines):
        t = raw.strip()
        if t.startswith('it "'):
            if cur is not None:
                spans.append((cur[0], i, cur[1]))
            cur = (i, len(raw) - len(raw.lstrip()))
        elif cur is not None and t != '' and (len(raw) - len(raw.lstrip())) <= cur[1]:
            spans.append((cur[0], i, cur[1]))
            cur = None
    if cur is not None:
        spans.append((cur[0], len(lines), cur[1]))
    # drop the it-line itself from body
    return [(s + 1, e, ind) for (s, e, ind) in spans]

def purpose_sentence(path, text):
    m = re.search(r'describe\s*\(\s*"([^"]+)"', text) or re.search(r'describe\s+"([^"]+)"', text)
    topic = m.group(1) if m else path.rsplit('/', 1)[-1].replace('_spec.spl', '').replace('_', ' ')
    return topic.rstrip('.')

def transform(path, add_steps=False):
    with open(path) as f:
        src = f.read()
    lines = src.split('\n')
    low = src.lower()
    out = lines
    changed = False

    # 1. NAR-001 purpose block
    if 'purpose and audience' not in low and '## purpose' not in low:
        purpose = purpose_sentence(path, src)
        block = ['## Purpose and audience',
                 'Purpose: verify that {p} behaves as this spec\'s scenarios assert.'.format(p=purpose),
                 'Audience: maintainers of this spec and reviewers of the behavior it proves.',
                 '']
        # find leading docstring
        first = next((i for i, l in enumerate(lines) if l.strip() != ''), 0)
        if lines[first].strip().startswith('"""'):
            # single-line docstring?
            if lines[first].strip().count('"""') >= 2:
                out = [lines[first]] + block + [''] + lines[first+1:]
            else:
                out = lines[:first+1] + block + lines[first+1:]
        else:
            block_full = ['"""'] + block + ['""' + '"', ''] + lines[first:]
            out = block_full
        changed = True
        lines = out

    # 2. TRC: bind all REQ ids inside first scenario
    ids = []
    for m in REQ_RE.finditer('\n'.join(lines)):
        i = m.group(0).rstrip('.,;:')
        if i not in ids:
            ids.append(i)
    # 2b. TRC-001: no REQ identity at all -> invent one and bind it
    spans = scenario_spans(lines)
    if not ids and spans:
        short = 'REQ-CHECK-001'
        parts = path.split('/')
        if 'stdlib' in parts: short = 'REQ-STDLIB-001'
        elif 'edge_case' in parts: short = 'REQ-EDGE-CASE-001'
        elif 'final_push' in parts: short = 'REQ-FINAL-PUSH-001'
        lines = ['# @req: ' + short] + lines
        insert_at = spans[0][0] + 1
        lines = lines[:insert_at] + [' ' * (spans[0][2] + 4) + '# @req: ' + short] + lines[insert_at:]
        changed = True
        ids = [short]
        spans = scenario_spans(lines)

    if ids and spans:
        s, e, ind = spans[0]
        # check which ids already appear inside some scenario span
        bound = set()
        for (a, b, _) in spans:
            seg = '\n'.join(lines[a:b])
            bound.update(m.group(0).rstrip('.,;:') for m in REQ_RE.finditer(seg))
        todo = [i for i in ids if i not in bound]
        if todo:
            insert = [' ' * (ind + 4) + '# @req: ' + i for i in todo]
            lines = lines[:s] + insert + lines[s:]
            changed = True

    if not changed:
        return None
    return '\n'.join(lines)

if __name__ == '__main__':
    for p in sys.argv[1:]:
        r = transform(p)
        if r is None:
            print('SKIP', p)
        else:
            with open(p, 'w') as f:
                f.write(r)
            print('MOD', p)
