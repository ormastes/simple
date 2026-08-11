# Backend Layer Artifact and Runtime Matrix

> Operator acceptance for the current backend artifact checker surfaces and
> the canonical ten-stage matrix boundary. This manual deliberately reports
> the missing canonical backend hooks as `FAIL`; independent CPU/GPU artifacts
> are supporting evidence, not substitutes for shared publication hooks.

| Field | Value |
|---|---|
| Requirements | `doc/02_requirements/feature/backend_layer_artifact_matrix.md` |
| NFRs | `doc/02_requirements/nfr/backend_layer_artifact_matrix.md` |
| Architecture | `doc/04_architecture/backend_layer_artifact_matrix.md` |
| Design | `doc/05_design/backend_layer_artifact_matrix.md` |
| Test plan | `doc/03_plan/sys_test/backend_layer_artifact_matrix.md` |
| Executable spec | `test/03_system/compiler/backend/backend_layer_artifact_matrix_spec.spl` |
| Evidence root | `build/check/cpu-backend-artifacts/`, `build/gpu-backend-layer/` |

## Purpose and audience

Compiler, backend, and release operators use this scenario to verify that the
real CPU and GPU checker surfaces account for every row they own while the
system-level ledger remains fail-closed. It prevents independent LLVM,
Cranelift, Wasm, CUDA, Vulkan, Metal, HIP, or OpenCL evidence from being
misreported as completion of an absent canonical compiler hook.

## Preconditions

- Run from the repository root on a host with `/bin/sh`.
- Use a pure-Simple compiler through the CPU checker when available. The Rust
  seed is rejected by that checker and cannot provide production evidence.
- Optional GPU tools/devices may be absent. An unavailable row is acceptable
  only when the checker records `SKIP_UNAVAILABLE` with a nonempty reason and
  probe path. Required Linux CPU baseline gaps remain failures.
- Preserve the checker evidence directories for review.

## Operator workflow

1. `select all compiler artifact stages` using
   `prepare_backend_artifact_fixture`.
2. `compile the layered backend fixture` using
   `compile_backend_artifact_fixture` and the real CPU/GPU checker commands.
3. `validate every emitted compiler layer` using
   `check_shared_stage_artifacts` and `check_backend_stage_artifacts`.
4. `execute the deepest available backend layer` using
   `check_runtime_readback_receipt`.
5. `account for the complete backend environment matrix` using
   `check_complete_matrix_ledger`.

The executable scenario uses these exact visible steps:

- `step("select all compiler artifact stages")`
- `step("compile the layered backend fixture")`
- `step("validate every emitted compiler layer")`
- `step("execute the deepest available backend layer")`
- `step("account for the complete backend environment matrix")`

## Expected result

The SSpec itself passes only when both checker matrices are structurally
complete, every optional unavailable GPU runtime row has reason/probe evidence,
and the missing canonical hooks are classified exactly as `FAIL`. At the pinned
origin, the expected system ledger result is:

- shared `source` through `optimized-mir`: `FAIL` because canonical shared
  publication markers are absent;
- `BackendIR`, `Object`, `LinkedBinary`, and `RunReadbackReceipt`: `FAIL`
  because the shared publication hooks are absent;
- CPU/GPU checker rows: 38 of 38 accounted as independent supporting evidence;
- canonical ten-stage registry/environment ledger: `FAIL` because it is absent.

No missing applicable hook may become `PASS`, `SKIP_UNAVAILABLE`, or
`NOT_APPLICABLE`.

## Evidence and provenance

The scenario executes:

```sh
sh scripts/check/check-cpu-backend-artifacts.shs --backend all
sh scripts/check/check-gpu-backend-layer-evidence.shs \
  --targets cuda,vulkan,metal,hip,opencl --runtime
```

CPU evidence retains build logs, backend IR/object/link artifacts, and runtime
stdout/stderr beneath `build/check/cpu-backend-artifacts/`. GPU evidence retains
producer, validator, tool/device probe, and readback files beneath
`build/gpu-backend-layer/`. The checker summaries must contain 18 unique CPU
rows and 20 unique GPU rows with no duplicate cell, missing cell, or `UNKNOWN`
status. Every optional `SKIP_UNAVAILABLE` row must include both a reason and a
probe path. A CPU baseline skip increases the required-failure count.

## Requirement traceability

| Requirement | System evidence | Current result |
|---|---|---|
| REQ-002, REQ-010 | Six shared-stage canonical marker accounting | `FAIL`: hooks absent |
| REQ-003 | Backend IR/object/link checker rows plus canonical-hook gate | Supporting rows complete; canonical gate `FAIL` |
| REQ-004 | Eight CPU/GPU runtime/readback rows plus receipt-hook gate | Supporting rows complete; canonical gate `FAIL` |
| REQ-005 | GPU unavailable reason/probe validation; CPU baseline fail-closed policy | Accounted, no unevidenced skip accepted |
| REQ-008, NFR-002 | 38 checker rows and canonical ledger marker | Checker rows complete; canonical ledger `FAIL` |
| NFR-003 | Required CPU gaps never promoted by this system ledger | Enforced |
| NFR-007 | Retained checker evidence paths and producer policy | Supporting evidence only |

REQ-001, REQ-006, REQ-007, REQ-009, NFR-001, and NFR-004 through NFR-008
remain owned by their focused parser, sink, determinism, scheduler, coverage,
performance, and security gates; this system scenario does not overclaim them.

## Compatibility and limitations

- This is an honest accounting acceptance, not a release `PASS` for Feature
  Option C. The expected canonical ledger is red until production hooks and the
  registry-derived ten-stage ledger exist.
- Cross-generation is not runtime evidence. A device/runtime row passes only
  with the checker readback receipt; unavailable optional hardware must retain
  its probe evidence.
- The current CPU fixture is the checker-owned deterministic branch/arithmetic
  probe. The planned multi-module/generic/buffer fixture remains an open feature
  gap and is not claimed here.
- The scenario does not use static source grep as backend evidence and does not
  import unpushed tracker or artifact-contract types.

## Executable SSpec

The canonical executable source is retained at
`test/03_system/compiler/backend/backend_layer_artifact_matrix_spec.spl` and is
the authority for assertions and helper implementations. Generated/manual
rendering must keep all five operator steps and all six helper names visible.
