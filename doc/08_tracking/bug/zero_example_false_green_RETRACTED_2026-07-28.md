# RETRACTION: "`bin/simple test` exits 0 having run zero examples" — measurement artifact

- **Date:** 2026-07-28
- **Status:** retracted / closed
- **Applies to:** claims made by several lanes on 2026-07-27..28, including the
  commit message of the `markers.spl` `is_nil` fix

## The claim

Multiple lanes reported that `bin/simple test <spec>` can exit 0 having
executed zero examples, printing no `"N examples, M failures"` line at all, and
that `test/01_unit/os/kernel/logging/marker_wire_format_spec.spl` was a live
instance providing no coverage.

## It does not reproduce

Run directly, with the exit code taken from `simple` itself and the output
captured to a file:

```
timeout 600 bin/simple test test/01_unit/os/kernel/logging/marker_wire_format_spec.spl > out.txt 2>&1
echo $?     # 1
```

```
3 examples, 1 failure
2 examples, 1 failure
2 examples, 2 failures
Results: 8 total, 4 passed, 4 failed
```

The spec runs **8 examples** and is **genuinely red**, exit **1**. It is not a
silent zero-example green.

## The guard already exists

- `src/lib/nogc_sync_mut/test_runner/test_runner_single.spl:200-211` — three
  fail-closed checks: timeout, no summary line at all, and literal zero
  examples.
- `src/app/test_runner_new/test_runner_single.spl:422-435` — same.
- `test_runner_types.spl:180-203` — `classify_test_run_result` /
  `test_run_outcome_exit_code`; `EmptySelection` is exit 4.

Verified by construction: a describe block containing no `it` exits **1** with
`error: test-runner: no examples executed`. A spec with one passing `it` exits
**0** with `Results: 1 total, 1 passed, 0 failed`.

## What actually produced the false reading

The observing harness, not the runner. The pattern in use was:

```
timeout 900 bin/simple test <spec> 2>&1 | grep -iE "example|passed|failed" | head -20
echo "=== no match means ZERO examples ==="
```

Two independent faults:

1. **`| head` truncates before the summary.** The results sit roughly 5,200
   lines in, after the lint noise. `head -20` never reaches them, so the grep
   appears to match nothing.
2. **`$?` is `head`'s status, not `simple`'s.** A red spec therefore reads as
   exit 0.

Together these turn "8 examples, 4 failures, exit 1" into "zero examples,
exit 0". This is exactly the standing rule
*Measurement traps: harness not system — pipe `$?`*, which we then re-derived
the hard way.

## Sweep result — 68 specs, zero false greens

Run sequentially (parallel runs corrupt the shared test database):

| sweep | population | result |
|---|---|---|
| 1 | 30 random specs | 22 exit 0 (all with real examples), 7 exit 1, 1 exit 255 — **zero false greens** |
| 2 | 38 static candidates with no `it` / `slow_it` | **38/38 exit 1**; 37 print `no examples executed` |

Specs newly exposed by adding a guard: **0** — the guard predates this
investigation. Specs that genuinely register zero examples and are *already*
correctly failing: **38**.

Deliberate red/green calibration:

| case | exit | output |
|---|---|---|
| describe with no `it` | 1 | `0 examples, 0 failures` → `error: test-runner: no examples executed` |
| one passing `it` | 0 | `1 example, 0 failures` |
| directory of both | 4 | `EmptySelection` |

## One latent fail-open, currently unreachable

`test_executor_parsing.spl:366` returns a *passing* 0/0 result when output
contains `Passed: 0` and `Failed: 0`. It is not live — the hardened child
emits `Failed: 1` for zero examples, so that branch is never taken today. It
is a real fail-open waiting for the child's behaviour to change, and should
be made fail-closed on its own merits.

## What IS real

A static scan found **38** spec files under
`test/{01_unit,02_integration,04_smoke}` that contain no `it` / `slow_it`
example at all — pure class definitions with zero coverage
(e.g. `test/01_unit/os/smux_spec.spl`,
`test/01_unit/compiler/common/config_spec.spl`). Those are genuinely
coverage-free, but the runner **fails closed** on them; they are a
spec-authoring gap, not a runner defect.

## Correction to a landed commit

The commit landing the `markers.spl` `spec == nil` fix states that
`marker_wire_format_spec.spl` "exits 0 having run ZERO examples, so it provides
no coverage". **That is wrong.** The spec runs 8 examples. Its 4 failures are a
separate open question — whether they predate the `is_nil` fix or were exposed
by it (`validate()` previously returned `Ok` for every input, so assertions
against it could not fail).

## Second correction to the same commit: `is_nil()` was never silently Ok

That commit also states that `spec.is_nil()` "never fired and `validate()`
returned Ok for every input". **Also wrong.** Restoring the old form and
re-running shows `is_nil()` is a hard runtime error on this engine:

```
semantic: method 'is_nil' not found on type 'enum' (receiver value: Option::None)
```

So the old form did not fail *open*, it failed *loudly* — and the spec was
worse with it: 5 failures instead of 4. The `== nil` fix converted one of
those errors into a real pass and caused zero failures.

The marker spec's 4 failures were therefore **exposed, not introduced**, and
the cause was not nil-checking at all. The spec was wrong on two independent
counts:

1. It asserted `"[boot] entry"` while the registry namespace is
   `MarkerNamespace.Boot -> "[BOOT]"` (uppercase), which is what every real
   emitter writes. `find_spec("[boot] entry")` correctly returned nil.
2. It referenced `NAMESPACE_BOOT`, which has never existed —
   `semantic: variable 'NAMESPACE_BOOT' not found`. `markers.spl` exports
   `NS_BOOT` (a `text`), and `marker_string` takes a `MarkerNamespace` enum,
   so no rename of that constant would have worked either.

Neither is fallout from the parallel session's `namespace` -> `.ns` field
rename, which is complete and consistent across all 22 registry entries.

## Standing method rule, restated

Capture to a file, read the **tail**, and take `$?` from the command under
test — never from the last stage of a pipe. `bin/simple` also prints thousands
of lines of lint noise before results, so any `| head` on its output is a bug.

Separately: `readlink -f bin/simple` currently resolves to a **Rust bootstrap
seed**, which warns it should not be used as the normal tool. All evidence
gathered this session is seed evidence and should be attributed as such.
