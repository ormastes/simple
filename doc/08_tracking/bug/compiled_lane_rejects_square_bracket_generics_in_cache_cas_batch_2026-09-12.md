# Compiled spec lane rejects `[T]` generics in `80.driver/cache/cas_batch_transaction.spl`, collapsing any spec whose import graph reaches it

- Status: OPEN (2026-09-12)
- Area: compiler / parser, compiler / 80.driver cache (L7/L8 — see "Owner" below)
- Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`, sha256 prefix `3d120a6f`

## Symptom

`bin/simple test <DIR>` (the compiled / SMF lane) reports
`test/01_unit/app/tooling/test_db_integrity_spec.spl` as `0 passed, 1 failed` — the whole
file collapses to a single failure — while `bin/simple test <that one file>` (the
interpreter lane) reports `outcome=OK declared>=27 executed=27 passed=27 failed=0`.

The error text surfaced during the directory run names a library file, not the spec:

```
 85 | fn cas_batch_error_v1[T](error: CasBatchTransactionErrorV1) -> Result[T, CasBatchTransactionErrorV1]:
error: Common mistake detected: See error message for details
```

That is `src/compiler/80.driver/cache/cas_batch_transaction.spl:85`. CLAUDE.md's language
rule is explicit: **Generics: `<>` not `[]`**. The declaration uses `[]` in both the
parameter list and the return type.

## Repro (2-file temp directory, ~1 min — not the 20-minute real directory)

```bash
cd /home/yoon/dev/simple-todofix-2
D=$(mktemp -d)
cp test/01_unit/app/tooling/test_db_integrity_spec.spl "$D"/
cp test/01_unit/lib/test_runner/test_db_cold_start_spec.spl "$D"/   # known-good neighbour
bin/simple test "$D"
# FAIL  .../test_db_integrity_spec.spl (0 passed, 1 failed)
# PASS  .../test_db_cold_start_spec.spl (3 passed)
bin/simple test "$D"/test_db_integrity_spec.spl
# SPEC FILE VERDICT: ... outcome=OK declared>=27 executed=27 passed=27 failed=0
```

Pairing with a known-good neighbour is what distinguishes a spec fault from a harness
fault: the neighbour passes in the same directory run.

## Pre-existing, proven by A/B

The same directory was rebuilt with the spec **exactly as it is at `89c5e3f865d`**
(`git show 89c5e3f865d:test/01_unit/app/tooling/test_db_integrity_spec.spl`) and the same
neighbour. It collapses identically — `0 passed, 1 failed`, neighbour `3 passed`. The
collapse therefore predates the todo-fix lane's edits to that spec and is not caused by
them.

## Honest limit of this record

The error above is the text the directory run surfaced, and it names a file that the
test-db import graph reaches. It has **not** been isolated as the single fatal line for
this spec — no per-file compile trace was captured. What the A/B proves is that the
collapse is pre-existing; the `[T]` declaration is the strongest lead, not a proven root
cause. Anyone picking this up should confirm by compiling that module alone.

## Owner

`src/compiler/80.driver/cache/**` is an L7/L8 packet path that the 2026-09-12 fan-out brief
puts off limits to every other lane, so this was not fixed here and must be picked up by
the lane that owns that directory.

## Impact

Any spec whose import graph reaches `cas_batch_transaction.spl` is at risk of collapsing in
the compiled lane while looking green single-file. A single-file GREEN is not evidence that
a spec survives a suite run.
