# Bootstrap Phase 4 midflight handoff — 2026-08-16

Status: **WIP / BLOCKED**, preserved at the user's request without a formal verify gate. This is not a Stage 3 or Stage 4 admission claim.

## Frozen state

| Lane | State | Evidence |
|---|---|---|
| Stage 2 v4 | PASS | Candidate SHA-256 `06e0587baa6b5adcde4d144e9dd3fa6f72dfb4e885ac2ccee9032c818627a06d`; wrapper admission `build/native_probe/stage4-owner-20260815/canonical-stage2-admission-v4/admission.env` SHA-256 `407c906135c920a0bc927bf16c9a5b5a9c786fa09eaeaaf2dd2885c5060c8d1b` |
| W1.5 mixed-tail probe | FAIL | `build/native_probe/p4_mixed_tail_probe_s2new_20260816/receipt.env` SHA-256 `454bf9c5f7c45a16340d5d7134937cdece9a6a37214362703c03e1c93215d5cd`; LLVM line 331 uses undefined `%l17` |
| C3 destination bookkeeping | EDIT READY, UNTESTED | `cycle1-edit.env` SHA-256 `d4d722bd538612ae45747a3c23cd91f01176698bbe570d4fefc2ab22e52f3257`; `build_count=0`, `test_count=0` |
| C4 unresolved-method guard | EDIT READY, UNTESTED | Ownership receipt SHA-256 `9fe4db55dd87a09d429820563ead3c8f67d96572aa41f097e693c8cc5feee798`; no post-edit execution receipt |
| Stage 3 | NOT RUN | Blocked behind a new identity-bound Stage 2 and W1.5 PASS |
| Stage 4 tools and tests | NOT RUN | Tool owners never received admission; no compiler/tool/test receipt exists |
| Tooling matrix C1 | ROW-ONLY PASS | `cycle1-static-review.env` SHA-256 `9ff1e0fb37ae074489013910399222ce88daa0f0d927197182cb03de5332ec05` |
| Tooling matrix C2 | BLOCKED | `mcp_stdio_integration` and `lsp_stdio_integration`: `protocol-root-contract-not-accepted`; real Stage 4 admission is false |

The diagnostic protocol's exact-once condition was violated: the probe owner and C3 lane each replayed the same preserved IR once, so `aggregate_replay_count_known=2` and `protocol_exact_once_violation=true` in `c3-replay-20260816-cycle1/receipt.env` (SHA-256 `0e263f28c1a4816bb309a767538cc0cc6ea489f76f6004822d37ad86ffdd92d4`). Do not replay that artifact again.

## Resume order and commands

1. Freeze the committed source, Git, runtime, tool, probe, and matrix identities in a new single-use Stage 2 authorization set. The v4 receipts are historical and must not authorize the changed C3/C4 source.
2. Run one cache-preserving Stage 2 build using the v4 command shape and a new reason/authorization receipt:

   ```sh
   env SIMPLE_NO_STUB_FALLBACK=1 /usr/bin/time -v \
     sh scripts/bootstrap/bootstrap-from-scratch.sh \
     --bootstrap-receipt=<new-stage2-reason.receipt> \
     --output=build/bootstrap --stop-after-stage2
   ```

3. Bind a new W1.5 evidence root to that admitted Stage 2 and run exactly one native build of `test/02_integration/compiler/bootstrap_mixed_tail_ret_probe.spl` with the frozen `resolved-command.txt` shape: LLVM backend, `core-c-bootstrap`, `--threads 1`, `--compile-stack-mib 64`, isolated mini-cache, `SIMPLE_NO_STUB_FALLBACK=1`, then run the artifact only if the build succeeds. Do not reuse or replay the old IR.
4. Only after W1.5 PASS, run exactly one canonical Stage 3 resume:

   ```sh
   sh scripts/bootstrap/bootstrap-from-scratch.sh resume-stage3 build/bootstrap
   ```

5. Require `Stage3AdmissionReceiptV1` with `admission_status=PASS`, exact compiler/runtime/interface/archive hashes, and the frozen source identity. Then build the CLI, MCP, and LSP journals in isolated caches and run:

   ```sh
   sh scripts/bootstrap/bootstrap-from-scratch.sh stage4-tooling-matrix \
     --matrix-id=<frozen-id> \
     --compiler-manifest=<stage3-compiler-manifest> \
     --cli-journal=<cli-journal> \
     --mcp-journal=<mcp-journal> \
     --lsp-journal=<lsp-journal> \
     --scope=full
   ```

6. Resolve the C2 protocol-root contract before treating either stdio row as PASS. Preserve prior green row receipts and use `--resume`; do not rerun green criteria.

## Required new evidence

- New Stage 2 source/runtime/tool/Git snapshots, GO receipts, transcript, sanity, receiver, and admission receipt bound to the committed hashes.
- One new W1.5 terminal receipt showing build/run counts and exact compiler/probe/runtime identities.
- C3/C4 focused source-contract results plus the new W1.5 result; current edits are untested.
- Stage 3 executable, provenance manifest, sanity receipt, and `Stage3AdmissionReceiptV1`.
- CLI/MCP/LSP compile journals and tools-only receipts with `stage4_compiler_files=0`.
- Resumed 49-row matrix summary with no required FAIL/BLOCKED row before any Stage 4 admission claim.

## Receipt-backed auxiliary changes

The Stage 3 receipt-reuse shell syntax and focused contract passed once under `build/native_probe/stage3-receipt-reuse-review-20260816/`; do not rerun them merely for confirmation. Observer-v2 passed only its host-CC fake-runner contract under `build/mini_builds/bootstrap_diagnostic_resume_verification_20260816/observer_v2/status.receipt.env`; it is not real-sweep acceptance. No Stage 3 receipt-reuse documentation file had an attributable receipt, so no such doc is included in this handoff.

## Conflict-integration note

The obsolete `bootstrap_flat_llvm_receiver_signature_corruption_2026-08-16.md`
bug file was intentionally not resurrected while integrating this WIP onto
`origin/main`. Its last cycle falsified receiver-owned signature dictionaries
as the complete root cause and selected mixed-tail block-result payload loss as
the active producer. Current status remains in the W1.5 row above and in
`doc/08_tracking/bug/bootstrap_flat_function_tail_local_payload_loss_2026-08-16.md`;
no receiver-corruption acceptance claim is carried forward.

The current upstream Stage 3 resume wrapper is intentionally retained for
output-root and recovery-artifact ownership except for the mandatory admitted
authority fix: fresh source/Git/tool snapshots now use separate temporary files
and must match the immutable Stage 2 receipts before the lock or build. The WIP
lane's external allowlist helper is absent from this upstream helper bundle, so
external-output support is deferred. Signal-race-safe lock cleanup, per-attempt
archives, and hash/evidence-backed previous/failed candidate retention are also
deferred blocking hardening; this handoff does not claim those recovery
properties until their helper dependencies are ported and independently
reviewed.
