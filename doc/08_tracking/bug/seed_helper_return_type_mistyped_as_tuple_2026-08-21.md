# Seed mis-types a `-> [text]` helper's result, breaking every downstream field access

Date: 2026-08-21
Reporter: agent A5+Y2 (Any hardening)
Status: FIXED 2026-11-11 (lane seedB, verified non-repro at base 79d5af6723f6)

## Symptom

Compiling `src/app/check/any_escape_census.spl` on the deployed seed failed with

```
error: semantic: undefined field: unknown property or method 'kind' on Tuple
```

pointing at no source location. The named field (`kind`) belongs to a struct that
is four call frames away from the real problem.

## Reproduce

The offending shape was a helper declared `-> [text]` whose result was iterated,
each element passed to a second function, and a field read off THAT function's
result:

```simple
fn collect_paths(args: [text]) -> [text]:
    var paths: [text] = []
    var i = 0
    while i < args.len():
        val a = args[i]
        if a == "--list":
            if i + 1 < args.len():
                val listing = rt_file_read_text(args[i + 1]) ?? ""
                for line in listing.split("\n"):
                    val p = line.trim()
                    if p != "":
                        paths = paths.push(p)
                i = i + 1
        elif a.ends_with(".spl"):
            paths = paths.push(a)
        i = i + 1
    paths

fn main() -> i64:
    val paths = collect_paths(get_cli_args())   # inferred Tuple, not [text]
    for p in paths:
        ...                                     # p: Tuple -> everything downstream mistyped
```

Isolation evidence: every individual piece compiled clean on its own (the helper
alone, the consumer alone, the field access alone). Only the composition failed,
and the failure disappeared when the helper's body was inlined into `main` —
identical statements, no signature change. The declared `-> [text]` is therefore
being ignored somewhere in the seed's inference for this shape.

Annotating the call site (`val paths: [text] = collect_paths(...)`) changed the
error rather than fixing it, which is a second symptom of the same mis-inference.

## Current workaround

`src/app/check/any_escape_census.spl` inlines the path collection into `main` and
accumulates counts in module-level `var`s. This is a workaround for a seed defect
and should be reverted to the helper form once this is fixed — it is recorded here
rather than left as an unexplained code shape.

## Why it matters beyond this file

The diagnostic names a type (`Tuple`) that appears nowhere in the source and a
field (`kind`) that belongs to an unrelated struct, with no location. Any
occurrence of this shape costs an operator a long manual bisection; this one took
roughly a dozen compile cycles to localize.

## 2026-11-11 — FIXED at tip (lane seedB, worktree simple-p3-seedB-20261111, base 79d5af6723f6)

The filed composition no longer reproduces on the tracked seed
`bin/simple.exe` (mtime 2026-11-11):

1. The doc's exact failing shape — helper declared `-> [text]` whose result
   is iterated, each element passed to a second function, and a field read
   off that function's struct result — now **compiles rc=0** and
   **runs correctly** (`run` prints the struct field for each element,
   exit 0).
2. The doc's second symptom (`val paths: [text] = collect_paths(...)` at the
   call site "changed the error rather than fixing it") also compiles rc=0.
3. The real `src/app/check/any_escape_census.spl` compiles rc=0 (only
   unrelated style warnings).

The declared `-> [text]` is no longer ignored: the call result types as
`[text]`, the for-loop element types as `text`, and the downstream field
access resolves against the struct, not a fabricated `Tuple`. Absorbed by
the seed HIR inference fixes landed between 2026-08-21 and this base (the
inference surface has since been heavily reworked; no single absorber
commit identified). No re-fix needed. The inline workaround in
`any_escape_census.spl` may be reverted to the helper form at the owning
lane's discretion — that source shape is no longer load-bearing for the
seed.


---

## Lane disposition 2026-11-13 (p3-misc-b bookkeeping)

FIXED 2026-11-11 (lane seedB, verified non-repro at 79d5af6723f6) per in-file addendum. No contrary evidence found in this pass; header status left as the
owning lane recorded it.