<!-- codex-design -->
# Architecture: Backend Layer Artifact and Runtime Matrix

## Decision

Adopt one backend-neutral artifact envelope and sink, capability-declared backend
adapters at canonical compiler boundaries, and an environment-qualified matrix
runner that produces a complete evidence ledger. Artifact capture is an optional
feature transform around existing stages; it must not create a second compiler
pipeline or backend-specific file-writing paths.

## Context and current state

`compiler.common.backend_stage_artifacts` already owns the ten-stage enum,
debug-dump parser, artifact metadata, path sanitization, SHA-256 validation,
atomic publication, probe receipts, and `PASS`/`FAIL`/`SKIP_UNAVAILABLE`
results. `driver_debug_artifacts` emits the six shared stages from the real
driver. CLI options are carried by `CompileOptions`.

The implementation is intentionally incomplete:

- no backend calls the shared sink for `backend-ir`, `object`,
  `linked-binary`, or `run-readback-receipt`;
- no complete backend/environment ledger or explicit non-applicable cell exists;
- the optimized-MIR integration scenario has not completed dynamically;
- most importantly, `--debug-dump=all` currently selects all ten stages but the
  driver silently emits only six. This violates request completeness and is a
  **release-blocking defect**.

## Architectural invariants

1. A requested stage ends as an emitted artifact or an explicit typed failure;
   silent omission is forbidden.
2. Compiler owners produce semantic objects; adapters serialize them;
   `BackendArtifactSink` alone publishes files.
3. A backend declares capabilities once. Matrix shape, CLI validation, and test
   expectations derive from that declaration.
4. `SKIP_UNAVAILABLE` describes an environment, never missing implementation.
5. `NOT_APPLICABLE` describes a reviewed capability boundary, never a failed
   probe.
6. Ordinary builds do not construct artifact payloads or touch the dump root.
7. Rust-seed output may bootstrap the pure-Simple compiler but cannot be the
   evidence producer for this matrix.

## Component model

### Existing shared capsule

`BackendArtifactStage`, `BackendStageArtifact`, `BackendProbeReceipt`, and
`BackendArtifactSink` remain in `compiler.00.common`. This layer cannot import a
backend, driver, CLI, or test module.

### Planned capability registry

`BackendArtifactCapabilityRegistry` returns canonical `BackendCapability`
records:

- canonical name and aliases;
- backend family and target constraints;
- supported stage set and artifact formats;
- tool/device/OS probe identifier;
- whether compile, link, run, device dispatch, or simulation is applicable;
- maximum safe parallelism and required CI profile.

The registry must be compared with the compiler's backend factory/selector
inventory. A backend present in either side only is a matrix failure.

### Planned stage adapters

Each backend family implements `BackendArtifactAdapter` and receives already
produced backend material. It returns an artifact payload/path or a typed error;
it does not invoke `BackendArtifactSink` directly. A driver-owned coordinator
adds producer/target metadata and calls the sink.

Adapter boundaries are:

- LLVM/llvm-lib: textual/bitcode LLVM IR, object path, linker output, process
  receipt;
- Cranelift/native assembly: textual CLIF/assembly where supported, object,
  linked binary, process receipt;
- C++20 and portable source backends: generated source, host/cross compiler object,
  linked output, process receipt;
- Wasm: WAT/wasm module, validated module artifact, runtime receipt;
- CUDA/HIP/OpenCL: PTX/HIP/OpenCL source or binary, loadable module/object,
  launch image where applicable, device readback receipt;
- Vulkan: SPIR-V text/binary, validated shader/module, pipeline-dispatch
  receipt;
- Metal: MSL/metallib artifacts and command-buffer/readback receipt;
- VHDL: VHDL source, analyzed/elaborated image, simulator receipt;
- BYL/SDN/Lua/Lean/interpreter/IRTC and legacy selectors: generated representation plus applicable
  interpreter/tool receipt; object/link cells are explicitly non-applicable;
- bare metal: assembly/object/ELF or platform image; run receipt comes from the
  declared emulator/hardware profile rather than a host process.

### Planned environment probes

`BackendEnvironmentProbe` performs a read-only availability probe before a
cell runs and returns tool identity/version, device identity, target, and
detail. Probe results are memoized for one matrix run. Environment access and
process launch use canonical facades. A tool that was available but rejects
generated output is `FAIL`, not `SKIP_UNAVAILABLE`.

### Planned matrix runner and ledger

`BackendArtifactMatrixRunner` forms all cells from registry x environment x ten
stages and assigns one `BackendMatrixCellStatus`:

- `PASS(artifact/receipt)`
- `FAIL(reason, evidence)`
- `SKIP_UNAVAILABLE(reason, probe)`
- `NOT_APPLICABLE(reason, capability)`

`BackendArtifactMatrixLedger` writes deterministic SDN/JSON containing every
cell and aggregate counts. Missing or duplicate cells fail ledger validation.
Fail-fast and collect-all are policies over the same runner; neither changes
cell semantics.

## Data flow

```text
CLI selection
  -> CompileOptions
  -> requested-stage tracker
  -> shared driver hooks (source ... optimized MIR)
  -> backend adapter hooks (IR -> object -> linked -> run/readback)
  -> BackendStageArtifact
  -> BackendArtifactSink (temporary file -> atomic move -> size/hash verify)
  -> matrix cell evidence
  -> complete ledger + coverage/requirement gates
```

The requested-stage tracker starts with the selected set and marks a stage only
after successful sink publication. At compilation completion, any unmarked
requested stage is an error naming the stage and backend. This closes the
current `--debug-dump=all` silent-omission hole even before a full matrix run.

## MDSOC evaluation

Artifact capture is a cross-cutting feature transform over existing stage
boundaries. The virtual capsule is the artifact contract plus coordinator; each
backend supplies a narrow adapter. The transform is statically disabled when no
stage is requested. Runtime composition is limited to selecting an adapter and
environment probe from the canonical registry. Semantic compiler nodes do not
gain sink, filesystem, or matrix knowledge.

## Serialization and comparison

- Source is exact bytes.
- AST/HIR serializers sort declaration names and use stable field order.
- MIR uses the canonical complete MIR serializer.
- Backend text preserves readable canonical output and normalizes only
  documented volatile fields.
- Binary output is retained byte-exact; semantic normalization, when needed,
  produces a separate comparison digest without replacing the raw digest.
- Receipts contain structured result/readback values and identity metadata, not
  free-form log-only assertions.

## Error handling

Configuration errors return CLI exit 2 before compilation. Shared-stage
serialization/publication errors map to the corresponding driver phase error.
Backend translation, tool, link, load, dispatch, and readback failures become
typed failed cells and preserve diagnostics. Collect-all continues only cells
whose prerequisites remain valid; downstream cells of a failed prerequisite are
recorded as `FAIL` with that dependency, never omitted.

## Performance and resource controls

Stage-enable checks occur before serialization. Producer identity and probes are
memoized per run. Collect-all schedules independent CPU cells up to the profile
limit and device cells up to the declared safe concurrency. Cache keys include
source, options, producer, target, backend tool/device, and prerequisite digest.
Progress is counter-based and append-only; no repeated full-tree scans or
per-poll subprocesses are permitted.

## Security and integrity

The sink root is resolved once, path components are sanitized, and every final
path is checked to remain below the root. Receipts allowlisted fields only.
Atomic publication and post-write size/hash checks remain mandatory. Artifact
inputs are copied, not moved, so compiler-owned output is not destroyed.

## Environment profiles

The ledger distinguishes Linux x86_64, Linux AArch64, macOS AArch64, Windows
x86_64, FreeBSD x86_64, SimpleOS/QEMU AArch64, and SimpleOS/QEMU RISC-V. GPU
profiles additionally identify CUDA/HIP/OpenCL/Vulkan/Metal device and driver.
Cross-generation on Linux may prove code generation, but native execution or a
declared emulator/device is required for the run/readback cell.

## Consequences

The design gives one comparison surface and prevents backend omissions, at the
cost of adapters and probe fixtures for every backend. Adding a backend now
requires a capability row and evidence plan. Platform and device absence stays
visible without turning infrastructure absence into false compiler failures.

## Release gates

- no requested-stage omissions, including `--debug-dump=all`;
- optimized-MIR real integration completion;
- 100% registry/environment/stage accounting;
- all required cells pass and all skips/non-applicable cells validate;
- at least 95% reviewed reachable branch coverage in owned modules;
- deterministic/integrity and disabled-cost NFRs pass.
