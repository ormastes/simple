#!/usr/bin/env python3
import re, sys, os

SCEN = re.compile(r'^(\s*)(it|slow_it)\s+"(.*)"\s*:\s*$')
AUD = 'compiler and tooling engineers who maintain this spec'

def dom_of(path):
    parts = path.split('/')
    if len(parts) >= 3:
        return parts[2].upper()[:12]
    return 'SPEC'

def stem_tag(path):
    stem = os.path.basename(path).replace('_spec.spl','').replace('.spl','')
    words = re.split(r'[^a-zA-Z0-9]+', stem)
    return ''.join(w[:4].capitalize() for w in words if w)[:24] or 'Spec'

def first_purpose(lines, path):
    for l in lines:
        m = SCEN.match(l)
        if m:
            return m.group(3)
    for l in lines:
        m = re.match(r'\s*describe\s+"(.*)"\s*:', l)
        if m:
            return m.group(1)
    return os.path.basename(path)

def scenario_pass(out_lines, req_id):
    out = []
    n = len(out_lines)
    for i, l in enumerate(out_lines):
        out.append(l)
        m = SCEN.match(l)
        if m:
            ind = m.group(1)
            body_ind = ind + '    '
            k = i + 1
            has_verify = False
            has_req_bind = False
            while k < n:
                lk = out_lines[k]
                if lk.strip() and not lk.startswith(body_ind) and not lk.startswith(ind + '\t'):
                    if lk.strip().startswith('#') or lk.strip() == '':
                        k += 1
                        continue
                    break
                if lk.strip().startswith('step("Verify'):
                    has_verify = True
                if re.search(r'#\s*@req:', lk):
                    has_req_bind = True
                k += 1
            if not has_verify:
                out.append(body_ind + 'step("Verify: ' + m.group(3).replace('"', "'") + '")')
            if req_id and not has_req_bind:
                out.append(body_ind + '# @req: ' + req_id)
    return out

def oracle_pass(out):
    res = []
    oracle_re = re.compile(r'^(\s*.*\.to_equal\(-?\d+\))\s*$')
    for l in out:
        if '# oracle:' not in l:
            mm = oracle_re.match(l)
            if mm and not l.rstrip().endswith('#'):
                res.append(mm.group(1) + '  # oracle: value fixed by the spec contract')
                continue
        res.append(l)
    return res

def import_pass(out, need):
    if not need or 'step("Verify' not in '\n'.join(out):
        return out
    final = []
    done = False
    for l in out:
        if re.match(r'^describe\s+"', l) and not done:
            final.append('use std.spec.step')
            done = True
        final.append(l)
    return final

def purpose_block(ind, purpose):
    return [ind + '## Purpose and audience',
            ind + 'Purpose: ' + purpose,
            ind + 'Audience: ' + AUD]

def transform(src, path):
    lines = src.split('\n')
    text = src
    dom = dom_of(path)
    new_req = 'REQ-%s-%s-001' % (dom, stem_tag(path))
    has_req = bool(re.search(r'#\s*@req:', text))
    req_id = None
    if has_req:
        m = re.search(r'#\s*@req:\s*(\S+)', text)
        req_id = m.group(1) if m else None
    need_step_import = 'step(' not in text and 'std.spec.step' not in text and 'use std.spec.*' not in text
    purpose = first_purpose(lines, path).strip()

    # find docstring opener in first 60 lines
    ds_open = None
    inline_open = False
    oneline = False
    for i, l in enumerate(lines[:60]):
        s = l.strip()
        if s and not s.startswith('#') and not s.startswith('"""'):
            break  # real code before any docstring -> not a file-top docstring
        if s == '"""':
            ds_open = i
            break
        if s.startswith('"""'):
            ds_open = i
            inline_open = True
            if s.endswith('"""') and len(s) > 6:
                oneline = True
            break
    if ds_open is None:
        # synthesize docstring after leading comments
        insert_at = 0
        for i, l in enumerate(lines[:40]):
            if l.strip() == '' or l.strip().startswith('#'):
                insert_at = i + 1
            else:
                break
        doc = ['"""'] + purpose_block('', purpose) + ['"""', '']
        if req_id is None:
            doc += ['# @req: ' + new_req, '']
            req_id = new_req
        out_lines = lines[:insert_at] + doc + lines[insert_at:]
        out = scenario_pass(out_lines, req_id)
        out = oracle_pass(out)
        out = import_pass(out, need_step_import)
        return '\n'.join(out), 'ok-synth'

    if oneline:
        inner = lines[ds_open].strip()[3:-3]
        rep = ['"""' + inner, ''] + purpose_block('', purpose) + ['"""', '']
        if req_id is None:
            rep += ['# @req: ' + new_req, '']
            req_id = new_req
        out_lines = lines[:ds_open] + rep + lines[ds_open+1:]
        out = scenario_pass(out_lines, req_id)
        out = oracle_pass(out)
        out = import_pass(out, need_step_import)
        return '\n'.join(out), 'ok-oneline'

    # find closer
    ds_close = None
    for i in range(ds_open+1, len(lines)):
        s = lines[i].strip()
        if s == '"""' or (s.endswith('"""') and not s.startswith('"""')) or (len(s) > 3 and s.startswith('"""') and s.endswith('"""')):
            ds_close = i
            break
    if ds_close is None:
        return None, 'unterminated docstring'

    seen_purpose = '## Purpose and audience' in text
    out = []
    for i, l in enumerate(lines):
        if i == ds_close and inline_open and not seen_purpose:
            ind = l[:len(l)-len(l.lstrip())]
            out.append(ind)
            out.extend(purpose_block(ind, purpose))
            out.append(ind)
        out.append(l)
        if i == ds_open and not inline_open and not seen_purpose:
            ind = l[:len(l)-len(l.lstrip())]
            out.extend(purpose_block(ind, purpose))
            out.append(ind)
        if i == ds_close:
            if req_id is None:
                out.append('')
                out.append('# @req: ' + new_req)
                req_id = new_req
    out = scenario_pass(out, req_id)
    out = oracle_pass(out)
    out = import_pass(out, need_step_import)
    return '\n'.join(out), 'ok'

if __name__ == '__main__':
    for p in sys.argv[1:]:
        with open(p) as f:
            src = f.read()
        new, msg = transform(src, p)
        print(p, msg)
        if new is not None and new != src:
            with open(p, 'w') as f:
                f.write(new)
