# Bug: `.to_int()` on `.split()`-derived text + `??` fallback both return garbage (Rust seed interpreter)

- **Date:** 2026-07-17
- **Status:** open (found incidentally while hardening `simple doc-coverage --missing`; worked around in pure Simple, not fixed here)
- **Area:** `src/compiler_rust` interpreter fallback (tree-walking, `bin/simple run` / `src/compiler_rust/target/release/simple run`)

## Symptom

`text.to_int()` called on a string produced by `.split(":")` indexing (e.g.
`parts[1]`) returns `nil` even for a genuinely numeric string like `"42"` --
confirmed via `match ... case nil / case Some(v)`. Separately, `?? 0` applied
to that same `Option<i64>` (whether stored in a `val` first or chained
directly) does **not** produce the literal fallback `0`; it produces an
unrelated, non-deterministic large integer (looks like uninitialized memory /
a reinterpreted pointer), and even prints with the wrong type (`0` shows as a
float `0.00000000000000000` in one variant).

## Minimal repro

```simple
fn main():
    val parts = "hello:42:world".split(":")
    print "parts[1]={parts[1]}"          # prints "42" correctly

    val n = parts[1].to_int() ?? 0
    print "n={n}"                        # BUG: garbage int, not 42 and not 0

    val n2 = parts[1].to_int()
    match n2:
        case nil:
            print "n2 is nil"            # BUG: takes this branch for "42"
        case Some(v):
            print "n2 = {v}"
```

Actual output (Rust seed, `src/compiler_rust/target/release/simple run <file>`):
```
parts[1]=42
n=3102443233537
n2 is nil
```
(The garbage integer differs between runs -- e.g. a second run produced
`5161544509281` for the equivalent `?? 0` expression.)

Expected: `parts[1].to_int()` should be `Some(42)`, and if it were ever
legitimately `nil`, `?? 0` should yield exactly `0` (as `i64`).

## Workaround used

`src/app/stats/doc_coverage_dynamic.spl`'s `print_missing` needed to compare
grep-derived `file:line` matches without going through `.to_int()`/`??` at
all: it keeps line numbers as strings (`parts[1]` from `.split(":")`, no
numeric parsing) and matches them via a plain `text.contains(...)` substring
check against a second grep pass shaped into the same `"path-N-..."` format.
No numeric parsing needed, so the interpreter defect above never triggers.

## Root cause

Not root-caused. Reproduces with a flat (non-nested) function body, so it is
likely distinct from
`doc/08_tracking/bug/interpreter_nested_block_var_redeclare_leaks_scope_2026-07-17.md`
(no nested block/shadowed name involved here). Suspect area:
`to_int()`'s handling of a `text` value that is itself a slice/element
produced by `.split()` (as opposed to a string literal or a value read via
`file_read`), combined with the `??` (nil-coalescing) operator's handling of
an `Option<i64>` in that same situation. Not checked against the pure-Simple
self-hosted interpreter/compiler (`src/compiler/`) or the native/JIT-compiled
path -- only the Rust seed interpreter fallback was probed.

## Second occurrence: `test/unit/lib/common/json_logic_spec.spl` (whole-suite `lib/common` triage, 2026-07-20)

`"parses nested object and array values"` (1 of 12 examples): `val parsed =
json_parse("{\"user\":{\"name\":\"Ada\",\"scores\":[1,2]}}")` then
`json_to_number(json_path_get(parsed, "user.scores.1"))` → `expected nil to
equal 2`. Traced to `src/lib/common/json/path_ops.spl`:
`json_path_get` (line 31) calls `json_path_parse(path)` (line 15, splits the
dotted path string into `[text]` components) and, for array components, does
`val idx = part.to_int()` (line 53) on the split-derived `"1"` component —
the exact same `text.to_int()`-on-`.split()`-result shape as the original
repro above. `part.to_int()` returns `nil` for the genuinely-numeric `"1"`,
so `json_path_get` returns `nil` at line 55 instead of descending into the
array. `run` not yet probed for this call site specifically (only `test`
verified so far); assumed same defect given identical shape to the
already-confirmed repro. Left the spec unmodified — not a stale-test issue,
`json_path_get`'s dotted-array-index feature is correctly implemented, it is
blocked by this interpreter defect.

## Verification

Reproduced at repo tip during the 2026-07-17 fmt/doc-coverage sanity-check
task via:
```
src/compiler_rust/target/release/simple run <repro.spl>
```
Probe scripts used to isolate this (nested-match variant, flat-split variant,
`to_int()`-alone variant) are not checked into the repo; the minimal repro
above is sufficient to reproduce.
