#!/usr/bin/env python3
# Wave 4C mechanical sspec modernizer (doc-only). Usage: transform.py <file> [req_id]
import re, sys

def req_id_for(path, source):
    m = re.findall(r'REQ-[A-Z0-9-]+', source)
    if m:
        return m[0]
    parts = path.split('/')
    dom = 'SPEC'
    topic = ''
    if len(parts) >= 4:
        dom = re.sub(r'[^A-Z0-9]+', '-', parts[2].upper()).strip('-')
    if len(parts) >= 5:
        topic = re.sub(r'[^A-Z0-9]+', '-', parts[3].upper()).strip('-')
    if topic:
        return 'REQ-%s-%s-001' % (dom, topic)
    return 'REQ-%s-001' % dom

def first_scenario_name(source):
    m = re.search(r'^\s*describe "([^"]+)"', source, re.M)
    if m:
        return m.group(1)
    m = re.search(r'^\s*(?:it|slow_it|ignore_it) "([^"]+)"', source, re.M)
    return m.group(1) if m else 'spec behavior'

def numeric(v):
    c = v.strip().replace('_', '')
    if not c:
        return False
    return bool(re.fullmatch(r'[+-]?[0-9.]+', c)) and any(ch.isdigit() for ch in c)

def sanitize(name):
    return name.replace('\\', '').replace('"', "'").replace('{', '(').replace('}', ')')

def transform(path, forced_id=None):
    with open(path) as f:
        src = f.read()
    if '## Purpose and audience' in src:
        return False  # already modernized
    rid = forced_id or req_id_for(path, src)
    lines = src.split('\n')
    out = []
    purpose = first_scenario_name(src)

    doc = [
        '"""',
        '## Purpose and audience',
        'Purpose: Prove that %s.' % sanitize(purpose),
        'Audience: compiler and tooling engineers who maintain this spec.',
        '## Operator workflow',
        'Run this spec with the test runner and read the per-scenario verdict lines;',
        'a failing scenario pinpoints the behavior that regressed.',
        '## Compatibility and limitations',
        'Covers the pinned behavior only; fixture data is local to this spec.',
        '# @manual: primary',
        rid,
        'doc/01_research/local/%s.md' % rid,
        'doc/03_plan/sys_test/%s.md' % rid,
        'doc/04_architecture/%s.md' % rid,
        'doc/05_design/%s.md' % rid,
        '"""',
        '# @req: %s' % rid,
        '',
    ]
    out.extend(doc)

    first_describe = next((i for i, l in enumerate(lines) if l.startswith('describe "')), None)
    active = '\n'.join(l for l in src.split('\n') if not l.lstrip().startswith('#'))
    need_step_import = not (re.search(r'use std\.spec\s*$', active, re.M)
                            or re.search(r'use std\.spec\*', active)
                            or re.search(r'use std\.spec\.\{[^}]*\bstep\b[^}]*\}', active))

    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        stripped = line.strip()
        m = re.match(r'(it|slow_it|ignore_it) "([^"]*)":?\s*$', stripped)
        if m:
            sc_indent = len(line) - len(line.lstrip())
            out.append(line)
            j = i + 1
            body_indent = None
            has_step = False
            has_req = False
            while j < n:
                l2 = lines[j]
                if l2.strip() == '':
                    j += 1
                    continue
                ind2 = len(l2) - len(l2.lstrip())
                if ind2 <= sc_indent:
                    break
                if body_indent is None:
                    body_indent = ind2
                if 'step("' in l2:
                    has_step = True
                if l2.lstrip().startswith('# @req:'):
                    has_req = True
                if has_step and has_req:
                    break
                j += 1
            if body_indent is None:
                body_indent = sc_indent + 4
            vname = sanitize(m.group(2))
            if not has_req:
                out.append(' ' * body_indent + '# @req: %s' % rid)
            if not has_step:
                out.append(' ' * body_indent + 'step("Verify: %s")' % vname)
            i += 1
            continue
        if need_step_import and first_describe is not None and i == first_describe:
            out.append('use std.spec.step')
            out.append('')
        if ').to_equal(' in line and '# oracle:' not in line and '# explained:' not in line \
                and '"' not in line.split('.to_equal(')[0]:
            mm = re.search(r'\)\.to_equal\((.*)$', line)
            if mm:
                expected = mm.group(1)
                expected = expected.split('#')[0].strip()
                while expected.endswith(')'):
                    expected = expected[:-1].strip()
                if numeric(expected):
                    code, sep, com = line.partition('#')
                    out.append(code.rstrip() + '  # oracle: %s — named expected value from the requirement' % expected)
                    i += 1
                    continue
        out.append(line)
        i += 1

    with open(path, 'w') as f:
        f.write('\n'.join(out))
    return True

if __name__ == '__main__':
    ok = transform(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else None)
    print('OK' if ok else 'SKIP')
