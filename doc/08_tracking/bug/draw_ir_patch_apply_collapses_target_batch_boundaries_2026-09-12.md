# `draw_ir_patch_apply` collapses every target batch into one, so batch boundaries and metadata are lost

- Status: OPEN (2026-09-12)
- Area: `src/lib/common/ui/draw_ir_patch.spl`
- Severity: medium — a specced behaviour that was never implemented; the spec
  example asserting it has been failing (and is the only remaining red in its
  file).
- Found by: BUGFIX-0 fan-out lane while re-checking
  `bug_sspec_daemon_optional_lookup_equality_divergence_2026-07-20` (a
  different, now-closed defect in the same spec file).

## Repro

Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust bootstrap seed,
`Simple Language v1.0.0-rc.1`), sha256 prefix `3d120a6f`.

```
SIMPLE_RUST_SEED_WARNING=0 timeout 420 bin/simple test \
  test/01_unit/lib/common/ui/draw_ir_patch_spec.spl --no-session-daemon
```

```
✗ preserves target batch boundaries and metadata across insert/remove/reorder
    semantic: array index out of bounds: index is 1 but length is 1
SPEC FILE VERDICT: test/01_unit/lib/common/ui/draw_ir_patch_spec.spl \
  outcome=ERROR declared>=19 executed=19 passed=18 failed=1 skipped=0 dropped=0
```

## Diagnosis

Not a mystery and not a regression — the function does this on purpose:

`draw_ir_patch_apply` (`src/lib/common/ui/draw_ir_patch.spl:411-437`) builds one
flat command list, wraps it in a single batch taken from
`_draw_ir_patch_base_batch` (`:405-409`, which returns `composition.batches[0]`),
and emits `batches: [patched_batch]`. The module comment above
`draw_ir_patch_commands_equal` (`:438-443`) states the same thing outright:
"Batch containers are deliberately NOT compared (see module doc: apply()
collapses to a single batch)".

The spec example, however, asserts the opposite contract: two batches out,
carrying the **target** ids `left-new` / `right-new` and the target's per-batch
command membership. With `batches.len() == 1` the `expect(...len()).to_equal(2)`
records a failure, execution continues, and the next line indexes
`batches[1]` — which is the "index is 1 but length is 1" abort, a symptom of the
collapse rather than a second defect.

The `commands_equal` assertion two lines earlier passes, because that oracle
flattens both sides and explicitly ignores batch containers. So the round-trip
oracle cannot see this gap; only the batch-boundary example can.

## Fix direction

Batch identity is not carried anywhere in `DrawIrPatchOp`, so this cannot be
fixed inside `apply` alone. Either:

1. give patch operations a batch identity (target `batch_id` + the batch
   metadata needed to rebuild the container) so `apply` can reconstruct the
   target's batch partition, or
2. decide the single-batch collapse is the real contract and delete the spec
   example — but then `draw_ir_patch_apply` is not usable for any consumer that
   needs batch boundaries preserved, which should be recorded as a limitation
   rather than left implied.

Option 1 is the one the spec was written for. Not attempted here: it is a
feature-sized change on `DrawIrPatchOp`'s shape, outside this lane's scope.

## Not to be confused with

`bug_sspec_daemon_optional_lookup_equality_divergence_2026-07-20`, which lived in
the same spec file and is CLOSED as of 2026-09-12 (its ~30-command round-trip
example passes). This one is unrelated and predates it.
