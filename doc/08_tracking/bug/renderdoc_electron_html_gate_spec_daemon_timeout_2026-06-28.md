# RenderDoc Electron HTML Gate SSpec Daemon Timeout

## Triage + partial fix 2026-11-25 — daemon timeout not reproducible; lost `_read_evidence` helper restored

- **measured** (Windows host, Git Bash, Rust seed v1.0.0-rc.1): the SSpec is
  not loadable via `bin/simple test` here (seed rejects
  `@representation_boundary` in imported stdlib modules — a known seed
  limitation), but `bin/simple run
  test/03_system/check/renderdoc_electron_html_gate_spec.spl` executes all 12
  examples in **~17 s**. The per-example work is fast; the reported daemon
  timeout is a property of the SPipe test daemon profile on the original
  Linux host, which does not exist on this host, so that acceptance remains
  unverifiable here.
- **found + fixed**: 5 of 12 examples failed with `function _read_evidence
  not found` — the helper's definition was lost in the 2026-09 tree
  transplant churn (`88aac2ffe28`) while its four call sites survived.
  Restored verbatim from pre-transplant history (`aff29a24dfe`). After:
  **12 executed, 9 passed, 3 failed** (was 7 passed / 5 failed, all 5
  semantic errors).
- **remaining 3 failures, none caused by this change**:
  1. "writes typed non-pass evidence…" — expects `xvfb-run -a --server-args=`,
     `-screen 0 `, and `chromium-gpu-process-crashed-under-renderdoc` inside
     `scripts/lib/renderdoc-evidence-common.shs`; all three are gone from that
     script after its refactor (xvfb wrappers moved to per-check scripts; the
     crash-classification string now lives in
     `scripts/check/check-renderdoc-electron-html-gate.shs:608`). Spec/gate
     drift — needs an owner decision on what the common-lib contract is.
  2. "rejects symlinked Electron RDOC and ARGB artifacts" — environment-blocked
     on Windows: Git Bash `ln -s` creates copies, not symlinks, so the gate
     correctly reports no symlink. Should pass on Linux.
  3. "keeps nonblank Electron ARGB proof while failing a missing RDOC
     capture" — the fixture's GPU-crash log now classifies as
     `chromium-gpu-process-crashed-under-renderdoc` (gate reason precedence,
     `check-renderdoc-electron-html-gate.shs:607-608`) instead of the
     expected `missing-rdc`. Spec/gate drift — owner decision.

Status: OPEN (daemon-profile question on the original host unresolved;
remaining failures 1 and 3 above need owner decisions).

## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Triage note 2026-09-13 — could not verify: the spec runner is broken on this host
- **measured** (Windows Rust seed v1.0.0-rc.1): `bin/simple test` is non-functional here — a 3-line 1-assertion spec returns in under a second with `WARNING: test daemon unavailable; running directly`, `error: test-runner: code -1 (process_run_bounded killed the child at its budget)` and a false `reason=outer-bound-timeout budget_ms=930000`. Seven real specs produced byte-identical verdicts.
- **inferred**: every runner-behaviour claim in this entry (example counts, PASS/FAIL bookkeeping, daemon timeouts) is therefore unverifiable here; a green or red from this host would be meaningless either way.
- **inferred**: left OPEN, not stale — the referenced spec files all still exist.

Date: 2026-06-28

## Summary

`test/03_system/check/renderdoc_electron_html_gate_spec.spl` times out under the
current SPipe test daemon on this host, even though the direct shell gate
completes quickly. Do not rerun the same SSpec repeatedly in one session; use
direct gate evidence while this daemon issue is open.

## Observed Command

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/renderdoc_electron_html_gate_spec.spl --mode=interpreter --clean --fail-fast
```

Observed result:

```text
ERROR: test daemon timed out: test/03_system/check/renderdoc_electron_html_gate_spec.spl
```

## Current Direct Evidence

The direct aggregate completes and reports:

```text
gui_showcase_4k_200fps_status=pass
gui_showcase_8k_perf_status=pass
electron_renderdoc_gate_launch_metadata_status=missing
electron_renderdoc_gate_launch_metadata_reason=missing-launch-exit-metadata
electron_renderdoc_gate_source_contract_status=stale
electron_renderdoc_gate_source_contract_reason=stale-source-missing-launch-exit-metadata
```

## Required Fix

Split the SSpec or fix the daemon profile so the scenario file can finish
without timing out. Until then, completion claims for the Electron RenderDoc
gate must rely on direct gate evidence plus this bug note, not repeated SSpec
reruns.

