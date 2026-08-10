#!/usr/bin/env python3
"""Bare-field-reference census scanner. Heuristic, read-only. See
scripts/check/census-bare-field-references.shs for the wrapper.
"""
import re, sys, os, csv

EXCLUDE_PREFIXES = (
    "src/compiler_rust/vendor/",
    "src/runtime/vendor/",
)
EXCLUDE_FILES = (
    "src/runtime/miniaudio.h",
    "src/runtime/stb_image.h",
    "src/runtime/stb_truetype.h",
)

CLASS_RE = re.compile(r'^(\s*)(class|struct)\s+(\w+)')
FIELD_RE = re.compile(r'^\s{4,8}(\w+)\s*:\s*[A-Za-z_][\w\.<>\[\], ]*\s*$')
METHOD_RE = re.compile(r'^(\s+)(me|fn|static fn)\s+(\w+)\s*\(')
KEYWORDS = {
    'if','while','return','and','or','not','true','false','nil','self','me',
    'let','val','var','for','in','match','case','else','elif','break',
    'continue','new','static','fn','class','struct','import','use','text',
    'i32','i64','f32','f64','bool','list','dict','array','type','none','some',
    'ok','err','print','println','panic','assert','with','as','is',
}

def get_body_end(lines, start_idx, indent):
    i = start_idx + 1
    n = len(lines)
    while i < n:
        line = lines[i]
        if line.strip() == "":
            i += 1
            continue
        cur_indent = len(line) - len(line.lstrip(' '))
        if cur_indent <= indent:
            break
        i += 1
    return i

def scan_file(path, rows):
    try:
        with open(path, 'r', errors='ignore') as f:
            text = f.read()
    except Exception:
        return
    lines = text.split('\n')
    n = len(lines)
    i = 0
    while i < n:
        m = CLASS_RE.match(lines[i])
        if not m:
            i += 1
            continue
        class_indent = len(m.group(1))
        class_name = m.group(3)
        class_end = get_body_end(lines, i, class_indent)
        # collect field names within class body, before first method
        fields = set()
        j = i + 1
        while j < class_end:
            line = lines[j]
            stripped = line.strip()
            if METHOD_RE.match(line):
                break
            fm = FIELD_RE.match(line)
            if fm and not stripped.startswith('#'):
                fields.add(fm.group(1))
            j += 1
        if fields:
            # determine convention: scan whole class body for self. vs me.
            body_text = '\n'.join(lines[i:class_end])
            self_count = len(re.findall(r'\bself\.', body_text))
            me_count = len(re.findall(r'\bme\.', body_text))
            convention = 'self.' if self_count >= me_count else 'me.'
            # now scan each method body for bare field refs
            k = i + 1
            while k < class_end:
                mm = METHOD_RE.match(lines[k])
                if mm and mm.group(2) == 'static fn':
                    method_indent = len(mm.group(1))
                    method_end = get_body_end(lines, k, method_indent)
                    k = method_end
                    continue
                if mm:
                    method_indent = len(mm.group(1))
                    method_end = get_body_end(lines, k, method_indent)
                    for li in range(k, method_end):
                        line = lines[li]
                        s = line.strip()
                        if s.startswith('#'):
                            continue
                        if s.startswith('"""') or s.startswith("'''") or (s.startswith('"') and s.endswith('"') and len(s) > 1):
                            continue
                        pos = None
                        if re.match(r'^if\s+\w', s):
                            pos = 'if-cond'
                        elif re.match(r'^while\s+\w', s):
                            pos = 'while-cond'
                        elif re.match(r'^return\s+\w', s) or s == 'return':
                            pos = 'return'
                        elif re.search(r'^\w[\w]*\s*=\s*[^=]', s) or re.search(r'=\s*\w', s):
                            pos = 'assign-rhs'
                        else:
                            pos = 'expr'
                        if '->' in s and s.rstrip().endswith(':') and '(' in s:
                            continue  # function signature line
                        # "self.<fld> = <fld>" constructor-body idiom: RHS bare name is the
                        # incoming parameter, not a field reference. Skip the whole line for
                        # any field matching this exact shape.
                        selfassign = re.match(r'^(self|me)\.(\w+)\s*=\s*(\w+)\s*$', s)
                        if selfassign and selfassign.group(2) == selfassign.group(3):
                            continue
                        for fld in fields:
                            for fmatch in re.finditer(r'(?<![\w.])' + re.escape(fld) + r'(?!\w)', line):
                                start = fmatch.start()
                                # inside a string literal? (odd number of unescaped double-quotes before start)
                                before = line[:start]
                                if before.count('"') % 2 == 1:
                                    continue

                                prefix = line[max(0, start-5):start]
                                if prefix.endswith('self.') or prefix.endswith('me.'):
                                    continue
                                prefix_stripped = line[:start].strip()
                                if prefix_stripped in ('val', 'var', 'for'):
                                    continue
                                # skip "key: fld" named-arg value position (e.g. `source_path: source_path,`)
                                if re.search(r':\s*$', line[:start]):
                                    continue
                                # skip function-signature parameter position "fn name(self, fld: Type)"
                                if re.match(r'^(fn|static fn)\s+\w+\s*\(', s):
                                    continue
                                if fld in KEYWORDS:
                                    continue
                                # skip if immediately followed by ':' with no leading space diff (named arg like fld: value) inside a call - heuristic: check char before is '(' or ',' and after fld is ':'
                                after = line[fmatch.end():fmatch.end()+1]
                                before_ws = line[:start].rstrip()
                                if after == ':' and (before_ws.endswith('(') or before_ws.endswith(',') or before_ws == ''):
                                    # looks like named-arg / field-init, but 'if fld:' block-condition is legit bare-ref, keep those
                                    if pos != 'if-cond' and pos != 'while-cond':
                                        continue
                                rows.append((path, li+1, fld, pos, convention, class_name))
                    k = method_end
                else:
                    k += 1
        i = class_end if class_end > i else i + 1

def main():
    root = sys.argv[1] if len(sys.argv) > 1 else 'src'
    out = sys.argv[2] if len(sys.argv) > 2 else '/tmp/bfr_census.tsv'
    rows = []
    files_scanned = 0
    for dirpath, dirnames, filenames in os.walk(root):
        for fn in filenames:
            if not fn.endswith('.spl'):
                continue
            p = os.path.join(dirpath, fn)
            if any(p.startswith(pref) for pref in EXCLUDE_PREFIXES):
                continue
            if p in EXCLUDE_FILES:
                continue
            files_scanned += 1
            scan_file(p, rows)
    with open(out, 'w', newline='') as f:
        w = csv.writer(f, delimiter='\t')
        w.writerow(['file','line','field_name','syntactic_position','prefix_convention','confidence','class'])
        for (path, line, fld, pos, conv, cls) in rows:
            conf = 'high' if pos in ('if-cond','while-cond','return') else 'medium'
            w.writerow([path, line, fld, pos, conv, conf, cls])
    print(f"files_scanned={files_scanned}")
    print(f"candidate_sites={len(rows)}")
    files_hit = len(set(r[0] for r in rows))
    print(f"files_with_hits={files_hit}")

if __name__ == '__main__':
    main()
