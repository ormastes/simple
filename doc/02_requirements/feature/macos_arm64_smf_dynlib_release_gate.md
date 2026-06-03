# Feature Request: macOS arm64 SMF Dynlib Release Gate

## Summary

Wire the `macos_status` field in the `qemu_gui_smf_artifact_contract` hardening
gate so that it reports `pass` when the arm64 GUI SMF dynlib artifact is
verified on a macOS arm64 runner.

## Motivation

The hardening evidence matrix (`simpleos_hardening_evidence_matrix`) has 9 gates.
Gate 8 (`qemu_gui_smf_artifact_contract`) requires three fields to pass:

| Field | Current | Required |
|-------|---------|----------|
| `status` | pass | pass |
| `qemu_status` | pass | pass |
| `macos_status` | not-run | **pass** |

`status` and `qemu_status` were wired in commit `1a6b1c3` (arm64 cross-build +
QEMU parity). `macos_status` remains `not-run` because the check requires a
macOS arm64 host to load and call the dynlib symbol natively.

## Acceptance Criteria

1. A macOS arm64 runner (CI or local) builds the arm64 GUI SMF dynlib artifact
   using `src/app/gui_perf/smf_wrap_host_dynlib.spl`.
2. The runner executes `src/app/gui_perf/macos_smf_dynlib_evidence.spl` which
   loads the SMF via `dlopen`, resolves `gui_dynlib_hot_probe_tick`, and calls
   it with a representative batch.
3. The evidence script emits `macos_status=pass` in the
   `GUI_SMF_ARTIFACT_CONTRACT` row when the probe succeeds.
4. The hardening matrix check (`scripts/check-simpleos-hardening-evidence-matrix.shs`)
   sees all three fields as `pass` and promotes `qemu_gui_smf_artifact_status`
   to `pass`.
5. Matrix reaches 9/9.

## Existing Infrastructure

- `src/app/gui_perf/macos_smf_dynlib_evidence.spl` — macOS evidence entrypoint
- `src/app/gui_perf/macos_smf_dynlib_evidence_core.spl` — core probe logic
- `src/app/gui_perf/macos_smf_dynlib_release_gate.spl` — release gate check
- `src/app/gui_perf/macos_smf_dynlib_transcript_check.spl` — transcript verifier

## Blocking Environment

- Requires macOS arm64 (Apple Silicon) host
- Not achievable on Linux x86_64
- Cross-compilation of the dynlib is already handled; only native execution is missing
