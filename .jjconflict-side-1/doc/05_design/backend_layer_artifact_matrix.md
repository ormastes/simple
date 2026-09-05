<!-- codex-design -->
# Detail Design: Backend Layer Artifact and Runtime Matrix

## Existing interfaces retained

- `BackendArtifactStage`
- `BackendDebugDumpConfig`
- `BackendProbeReceipt`
- `BackendLayerResult`
- `BackendStageArtifact`
- `BackendArtifactSink`
- `CompileOptions.debug_dump_stages`
- `CompileOptions.debug_dump_dir`
- `driver_emit_debug_stage`

The first implementation increment must preserve these names and extend around
them rather than duplicating the contract.

## New shared interfaces

The primary implementation pass owns these names before agents fan out:

```text
BackendCapability
BackendArtifactCapabilityRegistry
BackendArtifactAdapter
BackendArtifactCaptureCoordinator
BackendRequestedStageTracker
BackendEnvironmentProfile
BackendEnvironmentProbe
BackendMatrixCellKey
BackendMatrixCellStatus
BackendArtifactMatrixLedger
BackendArtifactMatrixRunner
```

`BackendMatrixCellStatus` adds `NOT_APPLICABLE` at ledger level. Existing
`BackendLayerResult` remains the result of an attempted applicable layer, so
current users are not forced into a broad enum migration.

## Capability record

`BackendCapability` contains canonical name, aliases, family, targets, formats
by stage, applicable stage set, probe name, required profiles, and concurrency
limit. Registry validation rejects blank names, alias collisions, duplicate
canonical rows, unknown stages, missing formats, and disagreement with backend
factory inventory.

An absent adapter for an applicable stage is a configuration `FAIL`. It must not
be converted to `NOT_APPLICABLE` or `SKIP_UNAVAILABLE`.

## Requested-stage tracking

At compile start, `BackendRequestedStageTracker` records every selected stage.
After `BackendArtifactSink.emit` succeeds, the coordinator marks the exact
module/backend/target/stage key. At normal driver completion it calls
`require_complete`. Missing shared stages identify the module; missing backend
stages identify the selected backend. This check makes the current behavior of
silently omitting four stages under `--debug-dump=all` impossible.

If a selected stage is not applicable to the selected backend, ordinary
`native-build` returns a configuration error explaining the capability. Matrix
mode records the same fact as `NOT_APPLICABLE`, because matrix mode must account
for every cell.

## Adapter protocol

An adapter is passed immutable stage input and `BackendArtifactContext`
(module, canonical backend, target, format, producer identity). It returns a
payload-backed or existing-path-backed `BackendStageArtifact`. The coordinator
validates the returned stage/backend/target before publication.

Adapters hook immediately after the canonical producer:

| Stage | Hook point |
|---|---|
| `backend-ir` | after backend translation succeeds, before external tool use |
| `object` | after assembler/compiler emits and validates the object/module |
| `linked-binary` | after linker/package creation and before execution |
| `run-readback-receipt` | after process/emulator/device completion and readback |

No adapter reparses source or reruns prior compiler layers to obtain its input.

## Backend-specific formats

| Backend family | Backend IR | Object/module | Linked/loadable | Runtime proof |
|---|---|---|---|---|
| LLVM/llvm-lib | `.ll` and optional `.bc` | target object | executable/library | exit/output receipt |
| Cranelift/native | `.clif` or assembly | target object | executable/library | exit/output receipt |
| C++20 codegen | `.cpp` | host/cross object | executable/library | exit/output receipt |
| Wasm | `.wat`/`.wasm` | validated wasm module | runnable module/package | runtime export result |
| CUDA/HIP/OpenCL | PTX/source/device binary | loadable device module | host launch image if applicable | device buffer readback |
| Vulkan | SPIR-V text/binary | validated shader module | pipeline package if applicable | fence + buffer/image readback |
| Metal | MSL/air | metallib | command pipeline package | command completion + readback |
| VHDL | `.vhd` | analyzed design | elaborated image | simulator signal/output receipt |
| BYL/SDN/Lua/Lean/interpreter/IRTC/legacy selectors | generated representation | capability-defined/N/A | capability-defined/N/A | tool/interpreter result |
| Bare metal | assembly/IR | target object | ELF/image | emulator/hardware receipt |

The registry, not this table, is executable truth. The table defines intended
coverage and must be updated when registry rows change.

## Probe and outcome algorithm

1. Resolve environment profile and capability.
2. If the cell is structurally unsupported, record reviewed
   `NOT_APPLICABLE`.
3. Probe required OS/tool/device once.
4. If unavailable, record `SKIP_UNAVAILABLE` with the probe receipt unless the
   profile marks it required, in which case record `FAIL`.
5. Validate prerequisite cell digests.
6. Generate/publish the stage artifact or execute/read back.
7. Validate content oracle and record `PASS`; otherwise record `FAIL` with the
   first failing boundary.

## Ledger schema and validation

The ledger header records revision, producer digest, fixture digest, start/end
time, runner version, and environment identities. Each cell records its key,
status, capability/probe evidence, prerequisite digest, artifact path/digest,
duration, and requirement IDs.

Validation recomputes the expected Cartesian product, rejects missing/duplicate
or unknown cells, validates status-specific evidence, and confirms all artifact
paths and digests. Summary counts are derived after validation; callers cannot
supply them.

## Execution modes

- `fail-fast`: stop scheduling new cells after the first required `FAIL`; finish
  already-running publication safely and record cancellation separately.
- `collect-all`: continue cells that do not depend on failed prerequisites;
  record dependent failures explicitly and reach ledger closure.
- `retry-failed`: load a validated prior ledger, invalidate failed/stale cells
  and their dependents, and reuse only matching green prerequisites.

Progress emits one event per state transition with total/completed/running/
failed/skipped/not-applicable/remaining counts plus backend and stage. It never
rescans artifact directories to compute progress.

## Test fixture design

Use a small multi-module pure-Simple program containing integer arithmetic,
branching, a call across modules, a generic specialization, and a deterministic
buffer transform. CPU rows return the same scalar/text oracle. GPU rows perform
the same transform and read back the buffer. VHDL uses an equivalent bounded
signal sequence. Backend-format validators confirm meaningful symbols,
instructions, entry points, target metadata, and parse/verification success.

Shared scenario/manual names are fixed as:

- `step("select all compiler artifact stages")`
- `step("compile the layered backend fixture")`
- `step("validate every emitted compiler layer")`
- `step("execute the deepest available backend layer")`
- `step("account for the complete backend environment matrix")`

Shared setup/checker helpers are:

- `prepare_backend_artifact_fixture`
- `compile_backend_artifact_fixture`
- `check_shared_stage_artifacts`
- `check_backend_stage_artifacts`
- `check_runtime_readback_receipt`
- `check_complete_matrix_ledger`

Until a real oracle exists, helpers must use `fail("backend artifact oracle not
implemented")`; placeholder success is forbidden.

## Coverage design

Branch tests cover parsing, duplicate stages, default/explicit directories,
every validation error, payload/path publication, I/O failure injection,
requested-stage omission, all four matrix statuses, required-profile upgrade of
unavailability to failure, dependency propagation, fail-fast, collect-all,
retry invalidation, ledger completeness, and sanitization. Platform-only
branches need profile-specific evidence or a reviewed unreachable exclusion.

## Current-to-target migration

1. Add capability/ledger types and omission tracking with focused unit tests.
2. Make unsupported requested backend stages fail explicitly.
3. Finish dynamic shared six-stage integration.
4. Add CPU backend adapters and runtime receipts.
5. Add portable, accelerator, hardware, interpreter, and bare-metal adapters.
6. Add environment runners and collect-all/retry behavior.
7. Close branch coverage, matrix, determinism, security, and performance gates.

No phase may claim Option C complete while `--debug-dump=all` can return success
without all requested applicable artifacts or explicit errors.
