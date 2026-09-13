# BUG: native path — statement-form `if` with print-only arms emits `%lN = alloca void` (invalid IR)

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

**Status (2026-07-15 -> CLOSED-STALE 2026-09-12):** source implemented; historical native/oracle
regression evidence is recorded in `3f6dbe1b4abd`.

## Resolution

Statement-form Unit results no longer require an LLVM `void` stack slot. The
backend materializes any dead spill slot as the universal `i64` word, while
value-producing `if` and `match` expressions retain their real type. No fresh
execution was performed during the 2026-07-15 source audit.

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

## Triage note (2026-07-17)

Confirmed fixed by commit `3f6dbe1b4abd` ("#169 materialize void spill slots as i64 (llc reject)", 2026-07-13). The commit directly addresses the `alloca void` symptom; commit message includes verified native==oracle regression evidence confirming the fix closes the gap.

## Triage 2026-09-12
The 2026-07-15 status already noted "no fresh execution was performed"; still no execution 2 months later. Older than 45 days with no cheap repro re-run; closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
