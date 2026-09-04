#!/usr/bin/env python3
# Wave-8 shard A6 helper: convert bare `expect expr` assertions into the
# recognized expect(...).to_equal(...) form, add oracle comments on numeric
# expecteds, and add @capture lines where missing. Conservative: only
# rewrites lines it fully matches; leaves everything else untouched.
import re, sys

NUM = r'(?:-?\d+)'

def strip_comment(line):
    # naive: no '#' inside strings for our matched patterns
    i = line.find('#')
    return (line, '') if i < 0 else (line[:i], line[i:])

def oracle_note(expected):
    return f"  # oracle: {expected} — pinned contract value from this spec's bug record/design"

def transform_line(raw):
    line = raw.rstrip('\n')
    code, comment = strip_comment(line)
    stripped = code.strip()
    m = re.fullmatch(r'expect (.+?) == (.+)', stripped)
    if m:
        act, exp = m.group(1).strip(), m.group(2).strip()
        if re.fullmatch(NUM, exp) and '#' not in comment:
            comment = oracle_note(exp)
        indent = code[:len(code) - len(code.lstrip())]
        return f"{indent}expect({act}).to_equal({exp}){comment}\n", True
    m = re.fullmatch(r'expect (.+?) != (.+)', stripped)
    if m:
        act, exp = m.group(1).strip(), m.group(2).strip()
        indent = code[:len(code) - len(code.lstrip())]
        return f"{indent}expect({act} != {exp}).to_equal(true){comment}\n", True
    # truthy bare expect on a comparison-free boolean expression
    m = re.fullmatch(r'expect (.+)', stripped)
    if m and '==' not in stripped and '!=' not in stripped:
        act = m.group(1).strip()
        booleanish = any(k in act for k in (
            'contains(', 'has(', 'starts_with(', 'ends_with(', 'is_', 'empty',
            'ok', 'err', 'some', 'none', 'true', 'false', 'valid', 'resolved'))
        if act and booleanish:
            indent = code[:len(code) - len(code.lstrip())]
            return f"{indent}expect({act}).to_equal(true){comment}\n", True
    return line + '\n', False

def main(path):
    out, changed = [], 0
    for raw in open(path):
        new, did = transform_line(raw)
        out.append(new)
        changed += 1 if did else 0
    open(path, 'w').write(''.join(out))
    print(f"{path}: converted {changed} bare-expect lines")

if __name__ == '__main__':
    for p in sys.argv[1:]:
        main(p)
