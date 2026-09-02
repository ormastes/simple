# `todo!()` inside a STRING LITERAL breaks semantic analysis ("value is not callable")

**Status:** OPEN. Found 2026-09-02 while writing
`test/01_unit/app/tools/rt_alias_map_unbacked_same_entry_is_detected_spec.spl`.

## Symptom

A `.spl` string literal whose *content* contains `todo!()` makes every `it` that
evaluates the enclosing function fail with:

```
semantic: value is not callable
```

The error names no symbol and no position, so it reads as a bug in the caller.
It cost roughly an hour of bisection to locate, because the failing tests all
shared an unrelated helper and the obvious suspects (array `.contains`, a
`has` name collision, escaped quotes in the `it` description) were each
eliminated first.

## Minimal reproduction (measured, both halves in ONE file)

```
val RT: text = "rt" + "_"

fn joined(lines: [text]) -> text:
    lines.join("\n") + "\n"

fn native_universe(rust_src: text, c_src: text) -> [text]:
    var out: [text] = []
    for line in rust_src.split("\n"):
        val marker = "extern \"C\" fn " + RT
        if line.contains(marker):
            val tail = line.split(marker)[1]
            out.push(RT + tail.split("(")[0])
    out

fn fixture_rust() -> text:
    joined([
        "pub extern \"C\" fn " + RT + "good() -> i64 { 0 }",
        "pub fn " + RT + "phantom(args: &[Value]) { todo!() }",   # <-- the literal
    ])

describe "probe":
    it "a: inline":
        expect(native_universe("pub extern \"C\" fn " + RT + "g() -> i64 { 0 }\n", "").len()).to_equal(1)
    it "b: via fixture":
        expect(native_universe(fixture_rust(), "").len()).to_equal(1)
```

Measured on `/d/wt-alias/bin/simple.exe` (x86_64-pc-windows-msvc), 2026-09-02:

| variant | result |
|---|---|
| as written above | `a: inline` PASS, `b: via fixture` FAIL — `semantic: value is not callable` |
| identical file, `{ todo!() }` in the literal replaced by `{ .. }` | both PASS |

Nothing else changed between the two runs. The literal is never evaluated as
code by any correct reading of the program: it is `[text]` element data that is
only ever `join`ed and `split`.

## Why this matters beyond the one spec

String content must never reach the macro/semantic layer. Any spec, fixture,
code-generator, or linter that quotes Rust source — an extremely common shape in
this repo, since many guards and specs assert on `src/compiler_rust` text — can
be broken by quoting a Rust macro invocation. The diagnostic gives the author no
way to connect the failure to the literal.

Related shapes to check when fixing (not yet measured): `vec![]`, `println!()`,
`assert!()`, `format!()` inside string literals; and whether the trigger is the
`!(` sequence or the specific identifier `todo`.

## Workaround in use

The spec avoids the literal (`{ .. }` instead of `{ todo!() }`). This is a
workaround, not a fix, and is recorded here rather than silently normalized per
`CLAUDE.md` ("when a short, safe grammar or compact expression form fails ...
record a concrete bug/feature request instead of silently normalizing the
workaround").
