# macOS Stage 2 sanity: SCV journal never materializes on fresh checkout; then JIT field-inference error in src/app/check/main.spl

Status: open, 2026-10-03. Host: M4 Mac, aarch64-apple-darwin, 26 GB.
Tree: `origin/main` at `02f6687d846` (post release/1.0 transplant).
Lane: `bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2
--backend=cranelift --jobs=10 --no-mcp` in a fresh worktree
(`/private/tmp/simple-kimi-bootstrap-20261003`), LLVM 23.1.1 Homebrew,
`SIMPLE_BOOTSTRAP_RUST_LLVM=0`, `BOOTSTRAP_STAGE2_TEST_DELEGATE=0`.

## Failure chain (all runs incremental from preserved phase-1 snapshot)

1. Run 1: Stage 2 sanity aborted —
   `SCV-E-ADMISSION: compile-event-journal-missing (first build in this
   checkout: rerun with SIMPLE_SCV_INVENTORY_COLD_INIT=1)` from the frontend
   smoke child. Log: `/private/tmp/simple-kimi-bootstrap-20261003-run2.log`.
2. Run 2 with `SIMPLE_SCV_INVENTORY_COLD_INIT=1` exported into the whole
   run: identical failure — the sanity child never sees the variable
   (phase-verification children explicitly `unset` it by design; the sanity
   driver's env allowlist apparently predates the SCV admission gate).
   Log: `/private/tmp/simple-kimi-bootstrap-20261003-run3.log`.
3. Manual prime attempts with the stage-2 candidate CLI
   (`stage3/aarch64-apple-darwin/stage2-runtime-authority/simple`) and the
   documented `bootstrap-scv-prime.shs` recipe (HOME/TMPDIR/SIMPLE_BINARY/
   `SIMPLE_NO_BOOTSTRAP_DELEGATE=1`/cold-init, `check --help` from source
   root): exit 0 in ~1 s, **no journal written anywhere** (checked source
   root `build/scv`, HOME, TMPDIR). The prime's documented assumption that
   `--help` performs the warm snapshot materialization does not hold for
   this binary/tree.
4. A real compile (`check --syntax-only examples/01_getting_started/
   hello_world.spl`, same env) passes SCV admission (cold) and then fails:
   `Cannot infer field type: struct 'SymbolId' field 'name' (declared
   fields: id) [in src/app/check/main.spl]` — JIT demotes to interpreter,
   run exits 1, journal still not written.

## Impact

Fresh-checkout stage-2 admission is impossible on current main: the sanity
frontend smoke cannot pass on a tree with no SCV journal, the documented
cold-init remedy does not reach the smoke child, the prime cannot create the
journal via `--help`, and the real-compile path hits a genuine stage-2 JIT
field-inference regression in `src/app/check/main.spl`.

## Suggested directions (not attempted — lane rules)

- Sanity driver should invoke the same `bootstrap_scv_prime` used by phase
  verification before its frontend smoke, or forward the cold-init variable.
- `src/app/check/main.spl` `SymbolId.name` access needs an explicit field
  type annotation (same class as the shaper.spl annotation workarounds) or
  a stage-2 HIR inference fix.
- Verify whether `check --help` short-circuits before admission/inventory on
  current main (prime comment says it used to materialize the snapshot).

## Retained evidence

- `/private/tmp/simple-kimi-bootstrap-20261003-run{2,3}.log`
- `/tmp/scv-prime-run{1..4}.log` (manual prime attempts)
- Frontend failure log:
  `build/bootstrap/stage2-trust-root-20261003/stage3/aarch64-apple-darwin/stage2-sanity.env.frontend-failure.log`
- Candidate CLI:
  `build/bootstrap/stage2-trust-root-20261003/stage3/aarch64-apple-darwin/stage2-runtime-authority/simple`
