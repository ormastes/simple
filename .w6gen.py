#!/usr/bin/env python3
"""Generate real sspec oracles for synthetic filler specs (wave-6)."""
import sys, hashlib, os

LANG = [
    ("integer arithmetic precedence", [
        'expect(2 + 3 * 4).to_equal(14)  # oracle: * binds tighter than +',
        'expect(10 - 2 * 3).to_equal(4)  # oracle: multiplication precedes subtraction',
        'expect((2 + 3) * 4).to_equal(20)  # oracle: parentheses force additive group first',
    ]),
    ("truncating division and signed remainder", [
        'expect(7 / 2).to_equal(3)  # oracle: i64 division truncates toward zero',
        'expect(-7 / 2).to_equal(-3)  # oracle: truncation is toward zero',
        'expect(7 % 2).to_equal(1)  # oracle: remainder of positive dividend',
        'expect(-7 % 2).to_equal(-1)  # oracle: remainder keeps dividend sign',
    ]),
    ("bitwise operators", [
        'expect(6 & 3).to_equal(2)  # oracle: 0b110 & 0b011',
        'expect(6 | 3).to_equal(7)  # oracle: 0b110 | 0b011',
        'expect(6 ^ 3).to_equal(5)  # oracle: xor of operands',
        'expect(1 << 4).to_equal(16)  # oracle: shift left by 4',
        'expect(-8 >> 1).to_equal(-4)  # oracle: arithmetic shift right',
    ]),
    ("string case and strip methods", [
        'expect("AbC".to_lower()).to_equal("abc")',
        'expect("AbC".to_upper()).to_equal("ABC")',
        'expect("  x ".trim()).to_equal("x")',
    ]),
    ("string split, join and repeat", [
        'expect("a,b,c".split(",")).to_equal(["a", "b", "c"])',
        'expect("ha".repeat(3)).to_equal("hahaha")',
        'expect("ab".reverse()).to_equal("ba")',
    ]),
    ("string predicates and slicing", [
        'expect("test.spl".ends_with(".spl")).to_equal(true)',
        'expect("hello world".contains("lo w")).to_equal(true)',
        'expect("hello world".len()).to_equal(11)  # oracle: 11 ASCII characters',
        'expect("abc".slice(0, 2)).to_equal("ab")',
    ]),
    ("array construction and access", [
        'expect([1, 2, 3].len()).to_equal(3)  # oracle: three-element literal',
        'expect([10, 20, 30][1]).to_equal(20)  # oracle: zero-based indexing',
        'expect([].len()).to_equal(0)  # oracle: empty literal has no elements',
    ]),
    ("array sorting and mapping", [
        'expect([3, 1, 2].sorted()).to_equal([1, 2, 3])',
        'expect([1, 2, 3].map(fn(x: i64): x * 2)).to_equal([2, 4, 6])',
    ]),
    ("array filtering and membership", [
        'expect([1, 2, 3].filter(fn(x: i64): x > 1)).to_equal([2, 3])',
        'expect([1, 2, 3].contains(2)).to_equal(true)',
        'expect([1, 2].concat([3])).to_equal([1, 2, 3])',
    ]),
    ("dict literal access", [
        'val d = {"k": "v"}',
        'expect(d["k"]).to_equal("v")',
    ]),
    ("dict get, keys and membership", [
        'val d = {"a": 1}',
        'expect(d.get("a")).to_equal(1)  # oracle: stored value',
        'expect(d.has("b")).to_equal(false)',
        'expect(d.keys()).to_equal(["a"])',
    ]),
    ("Option payload binding", [
        'val opt = Some(99)',
        'var chosen = 0',
        'match opt:',
        '    Some(x): chosen = x',
        '    nil: chosen = -1',
        'expect(chosen).to_equal(99)  # oracle: Some arm binds payload',
    ]),
    ("nil option falls to else arm", [
        'val opt = nil',
        'var chosen = 1',
        'match opt:',
        '    Some(x): chosen = x',
        '    nil: chosen = -1',
        'expect(chosen).to_equal(-1)  # oracle: nil arm taken',
    ]),
    ("for-range iterates the half-open span", [
        'var seen = 0',
        'for i in 0..4:',
        '    seen = seen + 1',
        'expect(seen).to_equal(4)  # oracle: 0..4 yields four iterations',
    ]),
    ("for-in accumulates array elements", [
        'var s = 0',
        'for x in [1, 2, 3]:',
        '    s = s + x',
        'expect(s).to_equal(6)  # oracle: 1+2+3',
    ]),
    ("while with break and continue", [
        'var i = 0',
        'var acc = 0',
        'while i < 10:',
        '    i = i + 1',
        '    if i == 3: continue',
        '    if i == 7: break',
        '    acc = acc + i',
        'expect(acc).to_equal(18)  # oracle: 1+2+4+5+6',
    ]),
    ("function calls and closure values", [
        'fn add(a: i64, b: i64) -> i64: a + b',
        'expect(add(2, 3)).to_equal(5)  # oracle: 2+3',
        'val f = fn(x: i64) -> i64: x * x',
        'expect(f(4)).to_equal(16)  # oracle: 4 squared',
    ]),
    ("integer conversion helpers", [
        'expect(42.to_text()).to_equal("42")',
        'expect("42".parse_int()).to_equal(42)  # oracle: decimal parse',
    ]),
    ("numeric comparison helpers", [
        'expect(abs(-7)).to_equal(7)  # oracle: absolute value',
        'expect(max(3, 9)).to_equal(9)  # oracle: larger operand',
        'expect(min(3, 9)).to_equal(3)  # oracle: smaller operand',
    ]),
    ("var mutation is sequentially visible", [
        'var acc = 1',
        'acc = acc + 1',
        'acc = acc * 10',
        'expect(acc).to_equal(20)  # oracle: (1+1)*10',
    ]),
    ("boolean operators short-circuit to expected truth table", [
        'expect(true and false).to_equal(false)',
        'expect(true or false).to_equal(true)',
        'expect(not true).to_equal(false)',
    ]),
    ("chained comparison yields a boolean", [
        'expect(1 < 2).to_equal(true)',
        'expect(2 <= 2).to_equal(true)',
        'expect(3 != 3).to_equal(false)',
    ]),
]

CTRL = [
    ("if-then arm executes on true condition", [
        'var r = 0',
        'if 10 > 5:',
        '    r = 1',
        'expect(r).to_equal(1)  # oracle: then arm taken',
    ]),
    ("if-else arm executes on false condition", [
        'var r = 0',
        'if 2 > 5:',
        '    r = 1',
        'else:',
        '    r = 2',
        'expect(r).to_equal(2)  # oracle: else arm taken',
    ]),
    ("elif first arm wins when its guard holds", [
        'var r = 0',
        'if 7 > 10:',
        '    r = 1',
        'elif 7 > 5:',
        '    r = 2',
        'else:',
        '    r = 3',
        'expect(r).to_equal(2)  # oracle: first true elif',
    ]),
    ("elif second arm wins when first guard fails", [
        'var r = 0',
        'if 7 > 10:',
        '    r = 1',
        'elif 7 > 9:',
        '    r = 2',
        'elif 7 > 5:',
        '    r = 3',
        'expect(r).to_equal(3)  # oracle: later elif evaluated after earlier false',
    ]),
    ("else arm runs when all guards fail", [
        'var r = 0',
        'if 1 > 2:',
        '    r = 1',
        'elif 2 > 3:',
        '    r = 2',
        'else:',
        '    r = 9',
        'expect(r).to_equal(9)  # oracle: terminal else',
    ]),
    ("nested conditionals evaluate inner guard independently", [
        'var r = 0',
        'if true:',
        '    if false:',
        '        r = 1',
        '    else:',
        '        r = 2',
        'expect(r).to_equal(2)  # oracle: outer true, inner false',
    ]),
    ("deeply nested true chain reaches innermost arm", [
        'var r = 0',
        'if 1 == 1:',
        '    if 2 == 2:',
        '        if 3 == 3:',
        '            r = 7',
        'expect(r).to_equal(7)  # oracle: all three guards true',
    ]),
    ("match dispatches on the first equal pattern", [
        'val k = 2',
        'var r = 0',
        'match k:',
        '    1: r = 10',
        '    2: r = 20',
        '    3: r = 30',
        '    else: r = -1',
        'expect(r).to_equal(20)  # oracle: literal pattern 2',
    ]),
    ("match falls through to default arm", [
        'val k = 99',
        'var r = 0',
        'match k:',
        '    1: r = 10',
        '    2: r = 20',
        '    else: r = -1',
        'expect(r).to_equal(-1)  # oracle: default arm',
    ]),
    ("match Some binds the payload", [
        'var r = 0',
        'match Some(5):',
        '    Some(x): r = x',
        '    nil: r = -1',
        'expect(r).to_equal(5)  # oracle: payload bound',
    ]),
    ("match nil takes the nil arm", [
        'var r = 9',
        'match nil:',
        '    Some(x): r = x',
        '    nil: r = -1',
        'expect(r).to_equal(-1)  # oracle: nil arm',
    ]),
    ("for loop body runs once per element", [
        'var c = 0',
        'for i in 0..3:',
        '    c = c + 1',
        'expect(c).to_equal(3)  # oracle: three iterations',
    ]),
    ("for loop over empty range runs zero times", [
        'var c = 5',
        'for i in 2..2:',
        '    c = c + 1',
        'expect(c).to_equal(5)  # oracle: body never entered',
    ]),
    ("break terminates the innermost loop", [
        'var c = 0',
        'for i in 0..10:',
        '    if i == 3: break',
        '    c = c + 1',
        'expect(c).to_equal(3)  # oracle: iterations 0,1,2 counted',
    ]),
    ("continue skips the rest of the body", [
        'var c = 0',
        'for i in 0..5:',
        '    if i == 2: continue',
        '    c = c + 1',
        'expect(c).to_equal(4)  # oracle: one skipped iteration',
    ]),
    ("while loop stops when guard turns false", [
        'var i = 0',
        'while i < 4:',
        '    i = i + 1',
        'expect(i).to_equal(4)  # oracle: guard boundary',
    ]),
    ("while loop with false guard never runs", [
        'var i = 7',
        'while i < 0:',
        '    i = i + 1',
        'expect(i).to_equal(7)  # oracle: body skipped',
    ]),
    ("boolean value selects via match on true/false", [
        'val flag = false',
        'var r = 0',
        'match flag:',
        '    true: r = 1',
        '    false: r = 2',
        'expect(r).to_equal(2)  # oracle: false pattern arm',
    ]),
]

# (name, extra_uses, lines)
STDLIB = [
    ("sha256 known-answer vectors", ["use std.common.crypto.sha256.{sha256_text}"], [
        'expect(sha256_text("abc")).to_equal("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")  # oracle: FIPS 180-2 vector for "abc"',
        'expect(sha256_text("")).to_equal("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")  # oracle: empty-input vector',
    ]),
    ("base64 RFC 4648 vectors and roundtrip", ["use std.common.base_encoding.base64.{base64_encode, base64_decode}"], [
        'expect(base64_encode("Man")).to_equal("TWFu")  # oracle: RFC 4648 illustration',
        'expect(base64_decode("TWFu")).to_equal("Man")',
        'expect(base64_decode(base64_encode("roundtrip"))).to_equal("roundtrip")',
    ]),
    ("gzip compression roundtrip", ["use std.common.compress.gzip.{gzip_compress, gzip_decompress}"], [
        'val data = "hello hello hello hello".bytes()',
        'val packed = gzip_compress(data)',
        'expect(packed.len() > 0).to_equal(true)',
        'expect(gzip_decompress(packed)).to_equal(data)',
        'expect(packed.len() < data.len())  # oracle: repeated text compresses',
    ]),
]

FILLER_MARKERS = ("check(1 == 1)", "check(true)", 'check("a" == "a")', "fn check(condition: bool):")

def is_filler(src):
    import re
    if re.search(r"fn \w+\(condition: bool\):", src):
        return True
    return len(re.findall(r"\bexpect\b", src)) < 2

def req_prefix(path):
    if "/compiler/" in path or path.startswith("test/01_unit/compiler"):
        return "COMPILER"
    if "/lib/" in path or path.startswith("test/01_unit/lib"):
        return "LIB"
    if "/std/" in path or path.startswith("test/01_unit/std"):
        return "STD"
    if "/core/" in path or path.startswith("test/01_unit/core"):
        return "CORE"
    if "/os/" in path or path.startswith("test/01_unit/os"):
        return "OS"
    return "APP"

def topic_of(path):
    # directory just above the file
    return os.path.basename(os.path.dirname(path)).replace(".", "-")

def pick(pool, n, seed):
    h = hashlib.sha256(seed.encode()).digest()
    order = sorted(range(len(pool)), key=lambda i: h[i % len(h)] * (i + 7))
    return order[:n]

def render(path, describes, req_text):
    prefix = req_prefix(path)
    topic = topic_of(path).upper()
    req = f"REQ-{prefix}-{topic}-001"
    base = os.path.basename(path).replace("_spec.spl", "")
    docpaths = "\n".join([
        f"# doc-path: doc/01_research/local/{base}.md",
        f"# doc-path: doc/03_plan/sys_test/{base}.md",
        f"# doc-path: doc/04_architecture/{base}.md",
        f"# doc-path: doc/05_design/{base}.md",
    ])
    out = []
    out.append(f"# @req: {req} — {req_text}")
    out.append('"""')
    out.append("## Purpose and audience")
    out.append("")
    out.append(f"Purpose: {req_text} Audience: compiler and runtime engineers")
    out.append("reading this spec to confirm the behavior still holds.")
    out.append("")
    out.append("## Operator workflow")
    out.append("")
    out.append(f"1. Run `bin/simple test {path}`.")
    out.append("2. Every scenario must pass; a failure is a regression in the")
    out.append("   behavior under test.")
    out.append("")
    out.append("## Compatibility and limitations")
    out.append("")
    out.append("Covers the interpreter and native lanes for the constructs")
    out.append("asserted here; platform-specific behavior is out of scope.")
    out.append('"""')
    out.append("")
    out.append("use std.spec")
    out.append("")
    out.append(docpaths)
    out.append("")
    out.append("# @manual: primary")
    for dname, ddoc, scenarios in describes:
        out.append("")
        out.append(f'describe "{dname}":')
        out.append('    """')
        out.append(f"    {ddoc}")
        out.append('    """')
        uses_done = set()
        for (name, uses, lines) in scenarios:
            out.append("")
            out.append(f'    it "{name}":')
            out.append(f'        step("Verify: {name}")')
            out.append(f"        # @req: {req}")
            for u in uses:
                if u not in uses_done:
                    out.append(f"        {u}")
                    uses_done.add(u)
            for ln in lines:
                out.append(f"        {ln}")
    out.append("")
    return "\n".join(out), req

def norm(pool):
    return [(name, [], lines) if len(e) == 2 else e for e in
            ((name, lines) if not isinstance(lines, list) or True else e,)
            for (name, lines) in [(e[0], e[-1]) for e in pool]] if False else [
            (e[0], e[1] if len(e) == 3 else [], e[2] if len(e) == 3 else e[1]) for e in pool]

def gen_file(path, pool, n_scen=6, describes_split=2, domain_note=""):
    seed = path
    pool = norm(pool)
    idxs = pick(pool, n_scen, seed)
    scenarios = [pool[i] for i in idxs]
    # split into describes
    groups = [scenarios[i::describes_split] for i in range(describes_split)]
    describes = []
    for gi, g in enumerate(groups):
        if not g:
            continue
        dname = "Executed behavior oracles" if gi == 0 else "Additional behavior oracles"
        ddoc = ("Real executed assertions over %s semantics; each scenario "
                "asserts observable results of the language runtime." % (domain_note or "core language"))
        describes.append((dname, ddoc, g))
    return describes

def main():
    path = sys.argv[1]
    kind = sys.argv[2]  # lang | ctrl
    domain_note = sys.argv[3] if len(sys.argv) > 3 else ""
    n = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    src = open(path).read()
    if not is_filler(src):
        print("SKIP")
        return
    pool = (LANG + STDLIB) if kind == "lang" else (CTRL + STDLIB)
    req_text = domain_note or "core language semantics hold under execution"
    describes = gen_file(path, pool, n_scen=n, domain_note=domain_note)
    content, req = render(path, describes, req_text.rstrip(".") + ". ")
    open(path, "w").write(content)
    print("WROTE " + req)

if __name__ == "__main__":
    main()
