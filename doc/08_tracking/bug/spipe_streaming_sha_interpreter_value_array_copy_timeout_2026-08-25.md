<!-- codex-architecture -->
# SPipe streaming SHA interpreter verification exceeds budget

**Date:** 2026-08-25
**Status:** Open — `FAIL`; `W4-SRCH-31` is not admitted

## Evidence and reproduction

Fresh verification cycle 2 ran the production-importing SHA spec in
interpreter mode and was terminated after approximately 3 minutes 9 seconds
with zero output. The focused-test ceiling is 180 seconds:

```bash
timeout 180s bin/simple test test/01_unit/app/spipe_knowledge_provider/provider_streaming_sha256_spec.spl --mode=interpreter
```

Expected: the complete focused spec reports within 180 seconds. Final product
admission also requires the Wave 0-qualified runtime, fixture, latency, and RSS
budget; 180 seconds is a diagnostic ceiling, not a fabricated product target.
Cycle 1 fixed a quadratic helper, but Cycle 2 proves the product/spec path is
still unbounded for admitted evidence. The 1,048,576-byte case and its required
partitions must not be reduced, skipped, or replaced by a smaller surrogate.

## Likely copy sites

These are inspection-derived hypotheses requiring profile evidence:

- `deterministic_bytes(1048576)` performs one million array `push` mutations;
- partition helpers pass the full `[u8]` payload by value, then every
  `Sha256StreamV1.update` again accepts `[u8]` by value;
- `_sha256_stream_block_i64(self.partial)` and
  `sha256_process_block(self.words, block)` pass arrays by value per block;
- indexed partial/state mutation may cause detach/writeback under the
  interpreter, though these buffers are fixed-size;
- the one-shot `sha256_u8_hex(payload)` oracle may independently dominate, so
  reference and streaming costs must be measured separately.

## Required direction

Keep the SHA owner to eight digest words and one owner-local fixed 64-byte
block. Consume an immutable bounded byte loan/view (`backing + offset + count`)
without transferring/copying the entire payload per partition. Fill and
compress the block in place. Construct the 1 MiB fixture linearly, without
value-semantic single-byte growth. Do not materialize `domain + payload`.

If the interpreter remains outside budget after algorithmic/copy fixes, retain
that runtime regression and run the unchanged oracle with the current,
provenance-bound pure-Simple self-hosted/native Stage 4 executable. Rust seed,
stale binary, helper-only proof, source review, and smaller input are `NOT
EVIDENCE`.

## Acceptance criteria

1. A profile attributes wall time and allocation/copy volume to fixture build,
   reference SHA, streaming update, compression, budget, and checkpoint paths.
2. No scale-sensitive whole-payload copy occurs per partition or block; live
   SHA state is bounded to digest words plus one 64-byte partial block.
3. Fixture construction is linear and all `W4-SRCH-31` lengths, partitions,
   domain builders, failure cases, and 4 KiB stop quantum remain unchanged.
4. The reproduction completes within 180 seconds, or the unchanged spec passes
   on the current provenance-bound admitted Stage 4 executable while the
   interpreter regression remains separately measured and open.
5. The focused spec reports full PASS, including 1 MiB digest/canonical-byte
   parity and no digest after terminal charge/checkpoint failure.
6. Evidence records executable SHA-256, source revision, mode, wall time,
   maximum RSS, fixture identity, and raw result path.
7. Optimizer review finds no remaining scale-sensitive value-array copy; public
   behavior and protocol bytes remain identical.

## Cycle guard

Two distinct verify/fix cycles are consumed. Cycle 2 terminated at about 3:09
without a result. Do not perform a third run in this session; the parent lane
has requested documentation/high review only. A future fresh session may run
one materially changed verification cycle, subject to its own guard.

## Highest-capability review conclusion

`FAIL`. Cycle 2 ended at approximately 3:09 without a result, so the required
1 MiB evidence is absent. No third execution was performed. The copy sites
above are credible optimization targets but remain hypotheses until measured;
they cannot convert the missing runtime result into acceptance.

## Second qualified-ceiling attempt after bounded optimization

After the bounded reusable-schedule optimization, the unchanged
contract-complete **nine-scenario** matrix was launched once under the focused
180-second ceiling. It reached the ceiling exactly and exited `124` without a
test summary. `/usr/bin/time` was terminated with the test process, so this
attempt has no maximum-RSS result and must not reuse the 43,852 KiB bounded
guard-probe measurement.

The execution receipt was:

- resolved executable:
  `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`;
- reported version: `Simple Language v1.0.0-RC`;
- executable SHA-256:
  `3ef64bffc68d0b1c2dd851d1f02976ca98fba6f88fbb406dddf56ba7f3ca27c0`;
- provenance: the wrapper warned that this is a Rust-built bootstrap seed, not
  an admitted pure-Simple Stage 4 executable;
- result: exit `124` at exactly 180 seconds, no summary, RSS unavailable.

This is a second qualified-ceiling failure, distinct from the earlier
approximately 3:09 uncontrolled termination. Static review of the complete
nine-scenario matrix is finished, but no candidate matrix files are accepted
and the full `W4-SRCH-31` gate remains `FAIL`. It proves neither Stage 4
admission nor a passing 1-MiB oracle.

The next remediation is instrumentation that emits bounded stage-level
progress receipts (fixture construction, reference digest, streaming update,
compression, checkpoint/finalization) before another qualified attempt, or
execution of the unchanged matrix with a provenance-qualified pure-Simple
Stage 4 executable. Do not weaken the timeout, shrink the matrix, report ten
scenarios, infer RSS, or rerun this attempt unchanged.

## Cross-links

- `doc/04_architecture/infra/spipe/spipe_knowledge_compiler_cooperative_streaming.md`
- `doc/05_design/infra/spipe/spipe_knowledge_compiler_cooperative_streaming.md`
- `doc/03_plan/agent_tasks/spipe_knowledge_compiler.md`
- `doc/03_plan/sys_test/spipe_knowledge_compiler.md`
- `test/01_unit/app/spipe_knowledge_provider/provider_streaming_sha256_spec.spl`
