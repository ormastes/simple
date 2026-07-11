# BUG: native path — statement-form `if` with print-only arms emits `%lN = alloca void` (invalid IR)

**Status:** OPEN (found 2026-07-11 by #138 Wall-3 agent)

## Symptom

On the normal native path (`env -u SIMPLE_BOOTSTRAP` + forced worker), a
statement-form `if` whose arms contain only `print` statements emits
`%lN = alloca void` in the LLVM module. `llc` rejects `alloca void`; the build
fails.

## Analysis

The if-expression lowering allocates a result slot even when the merged value
type is void (print-only arms produce no value). The slot allocation in
`70.backend` (MIR-to-LLVM) should be skipped when the merge type is void, or
MIR lowering should not synthesize a result local for statement-form `if`
with no value-producing arms.

## Repro shape

```
fn main() -> i64:
    if cond:
        print "a"
    else:
        print "b"
    0
```

(Exact failing probe was produced by the Wall-3 agent while building probe
fixtures; re-derive with the shape above on the normal native path.)
