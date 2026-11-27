# Cross-language source/SMF actual execution mode receipt missing

Status: BLOCKED (P3) — 2026-11-11 (lane intne1, batch p3-intne1-20261111): receipt owner present in source but runtime receipt unproven on the Rust seed host; verbatim grant below.
Status re-verified 2026-08-17 by source inspection (triage shard 00).
execution remains required before the rows are release-admitted.

The performance harness can request `--interpret` or execute an `.smf`, but the
process emits no machine-verifiable receipt from the selected execution engine.
Command-line intent is insufficient: the run wrapper delegates, environment
selection has fallback behavior, and an `.smf` invocation does not prove which
loader ultimately executed it. Therefore source-interpreter and SMF-loader rows
remain executable blocked rows, never admitted timing evidence.

Required owner change: the CLI execution dispatcher and compiler driver must
emit an opt-in, single-line receipt after final dispatch selection, for example
`simple_execution_mode_v1 requested=<mode> actual=<mode> fallback=false`, from
the component that actually enters interpreter/JIT/SMF execution. The receipt
must be absent on pre-dispatch failure, must report every fallback, and must be
covered by positive interpreter/SMF tests plus forced-fallback and malformed
artifact negatives. The harness can then require exactly one matching receipt
per measured process and replace the two blocked rows.

Resume plan:

1. CLI/runtime owner adds the opt-in receipt at the final engine boundary.
2. Run focused positive and false-admission contracts once on an admitted
   Stage 3/4 compiler.
3. Update the harness to parse requested/actual/fallback and retain raw samples,
   p50, p95, RSS, exit status, checksum, compiler/artifact hashes.
4. Re-seal the source manifest, build a fresh admitted Stage 4, and only then
   run the final performance profile.

## 2026-08-12 implementation

The canonical pure-Simple file execution owner now emits, only when
`SIMPLE_EXECUTION_MODE_RECEIPT=1`, exactly one line with this grammar after a
successful final engine execution:

`simple_execution_mode_v1 requested=<mode> actual=<mode> fallback=<true|false>`

The CLI carries its resolved request across an optional driver process hop.
Explicit interpreter intent is propagated through the existing canonical
`SIMPLE_EXECUTION_MODE=interpret` selector. The in-process source path records
an honest fallback when a requested JIT cannot be used; the SMF path emits only
from its successful load/resolve/execute arm, so malformed artifacts remain
receipt-free. Delegating parents emit nothing because only the child knows the
actual engine.

The retained cross-language harness now admits interpreter and SMF rows only
when every measured process emits exactly one byte-exact `fallback=false`
receipt alongside the existing checksum, timing, RSS, executable hash, and
compiler provenance evidence. The focused contract covers interpreter and SMF
positive receipts, forced-fallback rejection, missing-receipt rejection, and
SMF error-arm ownership. A fresh admitted compiler is still necessary for the
runtime positives; source contracts alone do not close that verification step.

## 2026-08-17 verification (CLI lane) — implemented in source, NOT provable on this host

The receipt owner exists in current source:
`src/app/io/_CliCommands/run_commands.spl:69-75` —
`execution_mode_receipt_enabled()` gates on `SIMPLE_EXECUTION_MODE_RECEIPT == "1"`
and `emit_execution_mode_receipt()` emits exactly
`simple_execution_mode_v1 requested={requested} actual={actual} fallback={fallback_text}`
on stderr.

Empirical run: `SIMPLE_EXECUTION_MODE_RECEIPT=1 bin/simple run hello.spl` -> rc=0,
stdout `hi`, and **no receipt line**. This is NOT evidence of a defect: the
deployed `bin/simple` is the Rust bootstrap seed (it prints the
"this Rust-built Simple binary is a bootstrap seed only" banner), so the
pure-Simple `run_commands.spl` receipt path never executes. Proving the receipt
requires a self-hosted `bin/simple`, which this lane could not produce (a
bootstrap was already occupying the host).

Verdict: **STILL-OPEN (unproven)** — source implementation present, runtime
receipt not demonstrated. Do not close until re-run on an admitted Stage 3/4
self-hosted binary.

## 2026-11-11 addendum (lane intne1, batch p3-intne1-20261111) — verdict: BLOCKED (verbatim grant)

Re-probed on release/1.0.0 tip (worktree simple-p3-intne1-20261111, HEAD 79d5af6723f6):

- Receipt owner still present in source: `src/app/io/_CliCommands/run_commands.spl:69-75`
  (`execution_mode_receipt_enabled` gates on `SIMPLE_EXECUTION_MODE_RECEIPT == "1"`;
  `emit_execution_mode_receipt` writes `simple_execution_mode_v1 requested=… actual=…
  fallback=…` to stderr), with the SMF arm at :116 and the interpreter arm at :146.
- The tracked `bin/simple.exe` (build-commit 46fe8f6b6def, refreshed seed) is still a
  Rust-built seed: it prints the bootstrap-seed banner, and `strings` on the binary
  finds no `simple_execution_mode_v1`.
- Empirical probe on this host: `SIMPLE_EXECUTION_MODE_RECEIPT=1 bin/simple.exe run
  /tmp/intne1/hello.spl` -> rc=0, stdout `hi`, **no receipt line**; the seed's `run`
  is JIT-first with engine-demotion, never entering the pure-Simple `cli_run_file`
  path. A parse-error fixture likewise produced no receipt and no pure-Simple error
  arm. Same wall as the 2026-08-17 CLI lane: the pure-Simple receipt path cannot
  execute under the Rust seed.

Verbatim grant to close this row:

    # on a host with a self-hosted pure-Simple Stage 3/4 binary (NOT the Rust seed):
    cd <repo root>
    printf 'fn main():\n    print("hi")\n' > /tmp/hello.spl
    SIMPLE_EXECUTION_MODE_RECEIPT=1 bin/simple run /tmp/hello.spl 2>&1 \
        | grep 'simple_execution_mode_v1 requested=jit actual=interpreter fallback=true'
    SIMPLE_EXECUTION_MODE_RECEIPT=1 SIMPLE_EXECUTION_MODE=interpret bin/simple run /tmp/hello.spl 2>&1 \
        | grep 'simple_execution_mode_v1 requested=interpret actual=interpreter fallback=false'

Expected if the owner holds: each grep matches exactly one line, and the parse-error
fixture emits no receipt. Then flip Status to FIXED with the captured lines as
evidence.
