# Stage-2 receiver probe: `bootstrap fn registry promotion failed` on the site-13 gate fixture
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN (2026-09-13)
- Area: 50.mir transient-scope promotion / Stage-2 admission (receiver probe)
- Found by: BOOT-14, `--full-bootstrap … --stop-after-stage2` at `bcb311feff3`
- Blocks: Stage-2 admission (`reason=stage2-struct-receiver-failed`, `probe_exit=1`)

## Symptom (verbatim)

`build/bootstrap-boot14a/stage3/aarch64-unknown-linux-gnu/stage2-receiver.log` (48 lines total):

```
error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
[ERROR] MIR error: MIR lowering transient scope failed for scripts.check.cert.redeploy_gate.fixtures.stage2_module_path_naming: bootstrap fn registry promotion failed for scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl
error: in-process native-build: MIR lowering transient scope failed for scripts.check.cert.redeploy_gate.fixtures.stage2_module_path_naming: bootstrap fn registry promotion failed for scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl
```

Candidate: `aad572408ec06e53c3b064ab3e2a8ffe86e2663e183e0e0a28288eaf177f2e85` (152287536 B), built by
Stage 2 of that run (`Build complete: 886 compiled, 0 cached, 0 failed`). Stage-2 sanity on the same
binary is `status=pass`.

## What is and is not established

- The message comes from `src/compiler/50.mir/_MirLowering/module_lowering.spl:1318` — the
  `bootstrap_fn_registries_promote()` arm of the per-module transient-array scope. One of the twelve
  `_promote_bootstrap_registry(_bootstrap_fn_*)` calls in `50.mir/mir_data.spl:1131-1156` returned
  false; the log does not say which, and the code does not name it.
- **This is NOT site 13.** Site 13 (the cross-module mangling asymmetry) is CLOSED on this candidate:
  `grep -c 'undefined symbol'` in this same receiver log is **0**, against BOOT-12's candidate which
  failed there with `ld.lld: error: undefined symbol:
  compiler.common.module_path_naming.module_logical_name_from_path`. The probe now gets far enough to
  fail in MIR lowering instead of at link.
- The fixture is the one added with the site-13 fix
  (`scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl`, 12 lines, importing
  `module_logical_name_from_path`), so this path had no prior coverage to regress from.
- Two candidate causes are in the same tree and are NOT yet discriminated: `bcb311feff3` (the site-13
  definition-side rename, which changes what names land in the fn registries) and `0e2aebed9d0`
  (the refactor that routed the same twelve promotes through one `_promote_bootstrap_registry`
  wrapper). Naming one without a one-variable run would be a guess.

## Not fixed here

BOOT-14 is the Stage-3/4 diagnostic lane; the receiver probe is part of the Stage-2 admission chain
that BOOT-13 owns. Recorded with the exact command, log path and binary identity so the owner can
discriminate the two candidates cheaply (the fixture compiles standalone in ~80 s on this host).
The first diagnostic step should be to report WHICH of the twelve registries failed to promote —
`module_lowering.spl:1318` currently discards that.

