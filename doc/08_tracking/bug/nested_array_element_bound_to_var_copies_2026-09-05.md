# Binding a nested-array element to a `var` copies it; writes through that binding are silently lost

**Date:** 2026-09-05
**Status:** OPEN
**Found by:** caret_workbench lane A6 (Caret TUI workbench), while building a
cell grid for the workbench layout renderer.
**Binary:** `src/compiler_rust/target/bootstrap/simple` (Rust seed, 130402384
bytes, 2026-09-05 20:01), macOS arm64.

## Symptom

Given `var outer: [[text]]`, binding an inner row to a variable produces a COPY.
Mutating through that binding succeeds locally and is then silently discarded —
no error, no warning, no diagnostic.

## Reproduction

`build/nb/fixtures/probe_nested_array.spl`:

```simple
fn main():
    var outer: [[text]] = [["a", "b"], ["c", "d"]]
    outer[0][1] = "MUT"
    print("nested_direct={outer[0][1]}")
    var row = outer[1]
    row[0] = "VIA_VAR"
    print("via_var_row={row[0]} outer={outer[1][0]}")
    var flat: [text] = ["x", "y"]
    flat[1] = "FLAT"
    print("flat={flat[1]}")
```

```
$ src/compiler_rust/target/bootstrap/simple run build/nb/fixtures/probe_nested_array.spl
nested_direct=MUT
via_var_row=VIA_VAR outer=c
flat=FLAT
```

## What is and is not broken

The reporting lane described this as "array indexing returns nested arrays by
value", which is broader than what reproduces. Measured:

| form | result |
|---|---|
| `outer[0][1] = "MUT"` — chained index assign | **works**, mutates in place |
| `flat[1] = "FLAT"` — top-level index assign | **works** |
| `var row = outer[1]` then `row[0] = …` | **BROKEN** — writes the copy, `outer[1][0]` still `"c"` |

So the defect is specifically in **binding an inner array to a variable**, not in
indexed assignment generally. A fix or a later census that assumes the broader
claim will look in the wrong place.

## Why it is dangerous

It fails silently in the direction that looks correct: `row[0]` reads back the
value that was just written, so a local assertion on the binding passes while the
real structure is unchanged. Any code that follows the ordinary "grab a row, fill
it in, move on" idiom loses every write, and only an assertion against the OUTER
structure catches it.

## Workaround in use

`src/app/llm_caret/workbench/tui_view.spl` avoids `[[text]]` entirely and uses a
flat row-major cell array:

```simple
struct Grid:
    width: i64
    height: i64
    cells: [text]     # index as y * width + x
```

Direct top-level indexing and struct-field array indexing both mutate correctly,
so the flat form is safe. This is a workaround, not a fix.

## Unblock condition

`var row = outer[1]; row[0] = "X"` must either mutate `outer[1][0]`, or be a
compile-time error that says the binding is a copy. Silently accepting the write
and discarding it is the part that must not survive.

Related prior art: `.claude/memory/interp_receiver_var_and_nested_push_bugs.md`
records a same-family receiver/nested-push defect, so this is likely one instance
of a class rather than an isolated case — check whether one root cause covers
both before fixing only this shape.
