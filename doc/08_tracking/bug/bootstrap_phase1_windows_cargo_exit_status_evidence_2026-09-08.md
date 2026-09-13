# Phase 1 Windows Cargo completion followed by wrapper exit 125

Status: native launch/status ownership fixed and verified by one strict
continuation; Phase 1 published, Stage 2 refused a reused evidence root.

The continuation observed as exec session 37462 ended at 2026-09-08 14:17:11 UTC.
`build/bootstrap/bootstrap-progress.state` recorded `milestone=exit-125`.
The timestamp-matched compiler-backfill log reported a completed Cargo bootstrap
build in 0.85 seconds. No separate top-level transcript or native process status
receipt was retained. The earlier `astra_toolchain/rustc-metadata-recovery` log
belongs to a different invocation and does not explain this exit.

The retained evidence cannot recover Cargo's exact Windows exit status. A Cargo
completion banner is not proof of successful process shutdown. The wrapper's
post-build fingerprint and generation-publication failures map explicitly to
exit 1; the build boundary previously retained only the MSYS child status, with
no native status or command receipt to distinguish a child failure from status
translation through `env.exe`.

The four Phase 1 Cargo calls now use `bootstrap-logged-process.shs` on Windows.
It forwards the existing clean environment and absolute Cargo command to the
native Windows Job Object collector. The collector consumes the `env -i`
envelope directly and calls `CreateProcessW` with a Unicode environment block,
so an MSYS `env.exe` intermediary no longer owns Cargo's exit status. Other
hosts and non-Cargo logged commands retain their existing routes.

Each build retains its captured stream and a receipt in a unique `.process.*`
directory beside the human-readable log. Receipts bind the helper hash, log hash, clean-environment
digest, native exit status, and portable shell status. Success requires native
exit 0 and an ordinary child exit. A printed completion banner never overrides
a nonzero process status. Capture is limited to 64 MiB of combined output and a
two-hour deadline; artifacts are not counted against the stream limit. These
are bootstrap host helpers, not Simple compiler or product dependencies.

Focused evidence:

- `sh test/01_unit/scripts/bootstrap_windows_cargo_status_test.shs`: PASS on
  actual Windows. Native children print a Cargo completion banner and exit 0,
  125, or 137; the adapter preserves each status without retrying. The clean
  environment excludes a parent-only sentinel and preserves paths containing
  spaces and literal shell-like argument text.
- Retained logs/receipts: `build/native_probe/cargo-status.usxneB/`.
- The source cache remains
  `build/bootstrap/rust-authority-aef139381e9d90ae37bb43c666e51a251888ccd9e2455b1cd498682cbc22e48e/`.

This evidence fixes the missing native boundary and tests its failure behavior.
It does not establish a retrospective root cause for the lost native status,
nor does it admit an older Phase 1 or Stage 2 binary.

The single cache-preserving continuation (exec 62915) finished at
2026-09-08 15:14:43 UTC. Evidence is retained under
`build/native_probe/phase1-native-status/continuation.liiQGI/`; all tracked
execution-input hashes stayed unchanged. All four native Cargo calls returned
`native_exit_status=0`, `raw_status=0`, `reason=child-exit`, and validated
helper/log receipts. The compiler-backfill receipt is
`build/bootstrap/logs/x86_64-pc-windows-gnu/rust-compiler-backfill-build.log.process.KkZwWj/command.env`.

Phase 1 published generation
`aef139381e9d90ae37bb43c666e51a251888ccd9e2455b1cd498682cbc22e48e-427b64aa6d4ba320462ef17f76d1bedc08387237b0b1ce396c163e1ad2922c3c`.
Its immutable `simple.exe` SHA256 is
`0d60690597549a2bff8250686eadfd03a358367d8fcc185ea484b8d36cc7e144`.
The current marker SHA256 is
`136b8a39de39962559034bf64af178c07fde1f1f37114f9df650e62f45ee483b`.
Exact paths and stamp binding are in the continuation's `phase1-handoff.json`.
The real host selected all 12 available CPUs for native and self-hosted work.

The continuation then stopped with exit 1 before Stage 2 compilation:
`stage2-sanity-error: stale-evidence-output-root; use a new output root with a cache clone`.
The conflicting file is
`build/bootstrap/stage3/x86_64-pc-windows-gnu/stage2-sanity.env`, preserved from
the earlier failed candidate. Its SHA256 is
`67c70bdebe5dd47daef00ad7dd41f9820ee852385acd8dbfd458e9f702c1c813`.
No new Stage 2 artifact was admitted. The next scoped continuation needs a
fresh evidence output root and cache clone; existing evidence must remain
intact. No second full continuation was launched in this fix.
