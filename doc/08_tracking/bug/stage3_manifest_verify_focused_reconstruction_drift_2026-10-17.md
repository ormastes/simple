# Stage3 manifest-verify focused reconstruction drift (blocks the resume final gate)

Date: 2026-10-17
Lane: release_phase3 Windows full bootstrap, `resume-stage3-from-admitted.sh`
final gate (`bootstrap_stage3_verify_manifest` at
scripts/bootstrap/resume-stage3-from-admitted.sh:1292-1294).

## Symptom

Every stage3 resume that reaches the final gate fails the focused
byte-compare between the recorded stage2 transcript and
`bootstrap_stage3_focused_command` (scripts/check/lib/bootstrap-stage3/manifest-verify.shs),
for divergences that predate any current work (verified present on base
commit 1986eb71e4a; the stage3-focused-provenance python harness is red on
the same base for the same reason).

## Verified divergences (real stage2 transcript vs reconstruction)

1. `--source` spellings. The builder (scripts/bootstrap/bootstrap-from-scratch.sh)
   emits: `--source src/compositions/kernel_llvm_cranelift` (RELATIVE,
   k1_composition_source_root strips the repo prefix at line 1741),
   `--source <abs repo>/src/compositions/cuda_<mode>` (line 1681),
   and `--source <abs repo>/src/plugins` (plugin_policy_source_root,
   unconditional, line 1628). The reconstruction emits: k1 as ABSOLUTE
   (`$bootstrap_stage3_root/src/compositions/kernel_llvm_cranelift`,
   manifest-verify.shs:7), cuda as the GENERATED overlay
   (`$manifest_output_root/compositions/cuda-<manifest-sha>-<template-sha>`,
   line 22 — a different directory containing only
   plugins/backend_registry/selected_cuda_backend.spl), and OMITS the
   plugins source entirely.
2. Frontend env rows. `bootstrap_stage3_windows_frontend_environment`
   (command-snapshot.shs:306-330) emits rows including
   `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=<policy>`; `run_transcribed`
   extracts and PREPENDS the budget (command-snapshot.shs:426-441) before
   the transcript is written, so the recorded vector carries the budget
   first. The focused reconstruction has no slot for it.

## Why it matters

The byte-compare is the last admission gate before the
`ADMITTED: stage=complete reason=manifest-verified` verdict. With any of
the above diverging it cannot pass for a bootstrap-from-scratch Windows
lane, so a fully-green stage3 resume is currently impossible even with all
other blockers cleared (context wiring fixed in PR #3568; this drift
remains).

## Constraints on the fix (design notes, not decisions)

- The overlay for cuda exists to content-pin the backend selection
  (find-verified single file, manifest-verify.shs:25-26); the real build
  still compiles from the repo composition dir. Any alignment must keep
  the overlay's pinning property.
- The k1 RELATIVE spelling is deliberate (k1_composition_source_root);
  the reconstruction's absolute form hashes the same file but bytes
  differ.
- The manifest already records DISPLAY values for cache/runtime dirs; the
  least-invasive reconciliation is likely to record the source argv
  (display) in the manifest at admission and have the reconstruction
  verify-and-emit it, rather than re-deriving spellings the builder
  owns.
- Whatever changes must keep the `hash` action of the focused command
  byte-identical to the manifest's `stage2_build_args_sha256` (verified
  in tests/stage3-focused-provenance-test.py, which is itself red on base
  and must be repaired in the same change).

## Evidence

- Real transcript: .simple/storage/bootstrap stage2-command.transcript
  (argv line) on any admitted release_phase3 Windows lane.
- Harness base-state failure: stage3-focused-provenance-test.py fails
  6/6 scenarios on pristine 1986eb71e4a (verified via git archive).

## Focused harness repair, 2026-10-17

Following production reconstruction repair `52b57c0beca`, the harness still
constructed invalid bare optional-environment placeholders. It also retained
the old absolute K1 spelling, omitted explicit CUDA/plugin source fixtures,
and did not initialize the CUDA mode used by the reconstructed command.
The fixture now uses a real compiler-ceiling assignment, explicit empty
optional Stage2 diagnostics/preflight context, relative K1 and absolute
canonical CUDA/plugin sources. Production admission checks are unchanged.

Concurrent harness processes were observed while both used the same fixed
`/tmp/focused-<stage>-<platform>.transcript` names. Each test invocation now
owns a temporary directory, resolved through the same shell used by the
helpers, and removes it on cleanup. This prevents cross-worktree transcript
overwrites; it does not weaken transcript comparison.

Validation on the isolated `work/bootstrap-focused-provenance-repair-20261017`
lane: the six-case run passed Linux Stage2/3, Darwin Stage2/3 and Windows
Stage2; Windows Stage3 failed its transcript comparison while another harness
process was present. After transcript isolation, only that failed case was
rerun using `FOCUSED_PROVENANCE_CASES=x86_64-pc-windows-msvc:stage3` and passed
in 9.574 seconds. All six cases therefore have passing evidence, with the
five unchanged successful cases retained rather than repeated. Each passing
case checks both exact hash-vector equality and production transcript
verification. The initial all-case fixture failure and intermediate source
path mismatch were retained in session output; no compiler build was run.

This repairs test execution, not full bootstrap admission. Actual Phase3 link,
producer behavior, source/lineage admission and broader runtime gates remain
the shared bootstrap owner's responsibility. Bug DB reconciliation remains
pending a qualified tool; this appendix is the dated evidence record.
