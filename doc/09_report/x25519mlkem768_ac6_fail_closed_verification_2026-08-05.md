# X25519MLKEM768 AC-6 `suggest`/`require` fail-closed verification (T-09)

**Date:** 2026-08-05
**Task:** T-09, `doc/03_plan/agent_tasks/x25519mlkem768_remaining_tasks.md`
**AC:** AC-6 — *"`suggest` records honest fallback and `require` fails closed
when the requested capability is absent."*

## Determination: AC-6 PASS

Independently verified by live execution (not by reading and asserting). No
AC-6 violation found. No bug filed.

## Mechanism found

The production suggest/require gate is
`x25519_mlkem768_resolve_backend(config, operation)` in
`src/os/crypto/x25519_mlkem768/execution_policy.spl` (lines 93-108). It is
called directly and unconditionally as the first step of every production
entry point (`x25519_mlkem768_keygen`, `_encapsulate`, `_decapsulate` in
`src/os/crypto/x25519_mlkem768/hybrid.spl`, e.g. `hybrid.spl:116`
`var evidence = match x25519_mlkem768_resolve_backend(config, "keygen"): ...`).

Its policy (per the file's own header comment) is **promotion-gated, not
hardware-detection-gated**: `Automatic`/`ScalarCpu` always resolve to the
hardened scalar oracle; every other backend (`Avx2`, `Neon`, `Rvv`, `Cuda`,
`Vulkan`, `Metal`) is currently "not promoted" regardless of whether the
underlying hardware/driver is physically present. This makes the gate's
suggest/require behavior deterministic and testable independent of which
GPUs happen to be attached to the host running the test.

Separately, `x25519_mlkem768_resolve_{cuda,metal,vulkan}_candidate` and
`x25519_mlkem768_resolve_simd_candidate` in the same file are explicitly
documented "evidence-only; never used by production TLS" helpers with no
selection-mode semantics at all — they are out of scope for AC-6 (which
governs the production suggest/require contract, not the candidate evidence
collectors).

## How it was verified

1. Read `execution_policy.spl` in full (`x25519_mlkem768_resolve_backend`,
   lines 93-108) and confirmed the production entry points call it
   (`hybrid.spl:116`).
2. The pre-existing landed spec
   `test/01_unit/os/crypto/x25519mlkem768_absolute_spec.spl` could not be run
   as a whole — it fails to compile with
   `error: semantic: Cannot resolve module: os.crypto.entropy` (an unrelated,
   pre-existing missing-module gap, not caused by this task and not touched
   by it).
3. To get real, live, per-backend evidence anyway, a temporary standalone
   spec (`test/01_unit/os/crypto/_tmp_ac6_verify_spec.spl`, deleted after the
   run — not landed, not committed) called
   `x25519_mlkem768_resolve_backend` directly for every
   `X25519MlKem768Backend` value under both `Suggest` and `Require`, and
   printed the real `Ok`/`Err` result. Run via
   `bin/simple test test/01_unit/os/crypto/_tmp_ac6_verify_spec.spl`,
   `Results: 1 total, 1 passed, 0 failed`, exit 0.
   `md5sum src/os/crypto/x25519_mlkem768/execution_policy.spl` was
   `bcd5dd9477f1c84cb51e908f02ef5ece` before and after the run (file
   untouched; no contamination from the concurrent sibling refactor of
   `interpreter_extern/mod.rs`, which this task did not read or use).

### Host state at time of test (for interpreting the CUDA/Vulkan rows)

- CUDA: 2 physical GPUs present (`nvidia-smi -L` → `NVIDIA RTX A6000`,
  `NVIDIA TITAN RTX`). Genuinely device-capable on this host.
- Vulkan: `vulkaninfo --summary` reports a working Vulkan 1.3.275 instance.
  Genuinely device-capable on this host.
- Metal: genuinely unavailable — no macOS/Metal hardware on this Linux host.
  This is a real, unforced absent-capability case, not a simulated one.

Because the production gate's suggest/require behavior is governed by
promotion status rather than live hardware probing, CUDA and Vulkan being
genuinely present on this host does not change their verdict below — and
that is itself part of what was being verified (a `require cuda`/
`require vulkan` does **not** silently start using the newly-restored,
genuinely-capable hardware; it still fails closed because CUDA/Vulkan are
not yet promoted backends). No additional artifact-hiding was needed to
exercise the "absent" case for CUDA/Vulkan, because the current promotion
state already makes them behave as absent at this policy layer regardless of
device presence.

## Verdict lines (verbatim from the test run)

```
AC6-VERDICT backend=automatic mode=suggest result=Ok selected=scalar-cpu fallback_used=false fallback_reason=""
AC6-VERDICT backend=automatic mode=require result=Ok selected=scalar-cpu fallback_used=false fallback_reason=""
AC6-VERDICT backend=scalar-cpu mode=suggest result=Ok selected=scalar-cpu fallback_used=false fallback_reason=""
AC6-VERDICT backend=scalar-cpu mode=require result=Ok selected=scalar-cpu fallback_used=false fallback_reason=""
AC6-VERDICT backend=avx2 mode=suggest result=Ok selected=scalar-cpu fallback_used=true fallback_reason="requested specialized backend is not promoted"
AC6-VERDICT backend=avx2 mode=require result=Err reason="requested X25519MLKEM768 backend has no promoted native implementation"
AC6-VERDICT backend=neon mode=suggest result=Ok selected=scalar-cpu fallback_used=true fallback_reason="requested specialized backend is not promoted"
AC6-VERDICT backend=neon mode=require result=Err reason="requested X25519MLKEM768 backend has no promoted native implementation"
AC6-VERDICT backend=rvv mode=suggest result=Ok selected=scalar-cpu fallback_used=true fallback_reason="requested specialized backend is not promoted"
AC6-VERDICT backend=rvv mode=require result=Err reason="requested X25519MLKEM768 backend has no promoted native implementation"
AC6-VERDICT backend=cuda mode=suggest result=Ok selected=scalar-cpu fallback_used=true fallback_reason="requested specialized backend is not promoted"
AC6-VERDICT backend=cuda mode=require result=Err reason="requested X25519MLKEM768 backend has no promoted native implementation"
AC6-VERDICT backend=vulkan mode=suggest result=Ok selected=scalar-cpu fallback_used=true fallback_reason="requested specialized backend is not promoted"
AC6-VERDICT backend=vulkan mode=require result=Err reason="requested X25519MLKEM768 backend has no promoted native implementation"
AC6-VERDICT backend=metal mode=suggest result=Ok selected=scalar-cpu fallback_used=true fallback_reason="requested specialized backend is not promoted"
AC6-VERDICT backend=metal mode=require result=Err reason="requested X25519MLKEM768 backend has no promoted native implementation"
```

## Per-backend AC-6 assessment

| Backend | Host status | `suggest` (absent/unpromoted) | `require` (absent/unpromoted) | AC-6 |
|---|---|---|---|---|
| Avx2 | not promoted (policy) | Ok, honest fallback to scalar-cpu, reason given | Err, fails closed | PASS |
| Neon | not promoted (policy) | Ok, honest fallback to scalar-cpu, reason given | Err, fails closed | PASS |
| Rvv | not promoted (policy) | Ok, honest fallback to scalar-cpu, reason given | Err, fails closed | PASS |
| Cuda | hardware present, not promoted (policy) | Ok, honest fallback to scalar-cpu, reason given | Err, fails closed | PASS |
| Vulkan | hardware present, not promoted (policy) | Ok, honest fallback to scalar-cpu, reason given | Err, fails closed | PASS |
| Metal | hardware absent (real), not promoted (policy) | Ok, honest fallback to scalar-cpu, reason given | Err, fails closed | PASS |
| Automatic | n/a (always resolves) | Ok, no fallback needed | Ok, no fallback needed | n/a (not a capability-absent case) |
| ScalarCpu | always available | Ok, no fallback | Ok, no fallback | n/a (baseline) |

No `require <backend>` call fell back silently in any case tested. Every
`Err` is returned through the standard `Result<X25519MlKem768Evidence, text>`
channel used throughout this module — callers cannot ignore it without
explicitly discarding a `Result`.

## Corroborating pre-existing landed coverage (read, not re-run due to the
unrelated `os.crypto.entropy` compile gap)

- `test/01_unit/os/crypto/x25519mlkem768_absolute_spec.spl:661-699` — same
  `Require`-fails / `Suggest`-falls-back pattern for Avx2 and Cuda through
  `x25519_mlkem768_resolve_backend` directly.
- `test/02_integration/os/crypto/x25519mlkem768_backend_matrix_spec.spl:435-463`
  — `Require` fails closed for Avx2 and Cuda through the production
  `x25519_mlkem768_keygen` entry point (`reason` contains
  "no promoted native implementation").

Neither pre-existing spec had a `Require`/`Suggest` row for **Metal** or
**Vulkan** through `resolve_backend` — this task's live run above fills that
gap for the first time.

## Note on the unrelated compile gap found in passing

`test/01_unit/os/crypto/x25519mlkem768_absolute_spec.spl` currently fails to
compile as a whole file (`error: semantic: Cannot resolve module:
os.crypto.entropy` — no `src/os/crypto/entropy.spl` exists in this worktree).
This is pre-existing and unrelated to AC-6/execution_policy.spl; it was not
touched or fixed as part of this task (out of scope for T-09). Flagging it
here as an observation, not filing a separate bug doc since it wasn't the
focus of this verification pass and may already be tracked under another
task (e.g. entropy-source work).

## Files touched

None landed. A temporary spec
(`test/01_unit/os/crypto/_tmp_ac6_verify_spec.spl`) was created to obtain
live evidence and deleted immediately after capturing output; git status is
clean for both it and `execution_policy.spl` (verified by md5sum before and
after).
