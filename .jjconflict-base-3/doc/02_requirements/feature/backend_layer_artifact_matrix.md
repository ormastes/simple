<!-- codex-design -->
# Backend Layer Artifact and Runtime Matrix Requirements

Status: **Selected — Feature Option C (full layered artifact/runtime matrix)**

## Goal

Make every compiler transformation and code-generation backend observable through
one deterministic artifact contract, then prove the generated output at the
deepest layer supported by the current environment. The Rust compiler remains a
bootstrap seed; the production path under test is the pure-Simple compiler.

## Scope

The canonical stage sequence is:

1. `source`
2. `ast`
3. `hir`
4. `monomorphized-hir`
5. `mir`
6. `optimized-mir`
7. `backend-ir`
8. `object`
9. `linked-binary`
10. `run-readback-receipt`

The backend inventory is registry-derived so a newly registered backend cannot
silently escape the matrix. The initial inventory must account for every
`BackendKind`: Cranelift, LLVM, LLVM-lib, native, Wasm, Lean, BYL, interpreter,
CUDA, HIP, OpenCL, Vulkan, VHDL, C++20 codegen, IRTC, Lua, compiler, SDN, and
the legacy JIT selectors. It must also account for Metal/MSL and bare-metal
x86_64, AArch64, RISC-V 32, and RISC-V 64 producer/runtime routes exposed
outside that enum. Aliases such as `llvmlib`, `ptx`, and `spirv` map to one
canonical row rather than creating duplicate rows.

## Functional requirements

### REQ-001 — Canonical debug-dump selection

`simple native-build` must accept `--debug-dump=<stage-list>` and
`--debug-dump-dir=<path>` in split and inline forms. `all` selects every stage.
Empty, unknown, or duplicate stages and a directory without a stage list must
fail before compilation. Dumping is disabled by default.

### REQ-002 — Shared frontend and middle-end artifacts

For every compiled module, an enabled shared stage must publish its real source,
AST, HIR, monomorphized HIR, MIR, or optimized MIR through
`BackendArtifactSink`; a placeholder, summary-only fake, or Rust-seed-only dump
does not satisfy the requirement. Streaming Stage 4 compilation may publish AST
and HIR at the per-module boundary.

### REQ-003 — Backend artifact adapters

Every registered code-generation backend must declare its capabilities and
publish each applicable `backend-ir`, `object`, and `linked-binary` artifact at
the canonical boundary. Textual IR must remain readable; binary artifacts must
remain byte-exact. Backend adapters may translate native backend objects into
the shared contract but may not create private artifact writers.

### REQ-004 — Runtime or device readback

Every backend with an executable or device-dispatch capability must execute a
deterministic probe and publish a `run-readback-receipt`. CPU probes must verify
exit status and value/output. CUDA, HIP, OpenCL, Vulkan, and Metal probes must
verify device selection, dispatch completion, and host-visible readback. VHDL
must verify elaboration/simulation output. Non-executable producer backends must
declare the runtime layer non-applicable with a reason.

### REQ-005 — Environment-qualified outcomes

Every matrix cell must have exactly one outcome: `PASS`, `FAIL`,
`SKIP_UNAVAILABLE`, or `NOT_APPLICABLE`. `SKIP_UNAVAILABLE` requires a recorded
probe showing the missing tool/device/OS capability. `NOT_APPLICABLE` requires a
backend capability declaration and may not hide an unimplemented applicable
hook. Required baseline cells may not be skipped.

### REQ-006 — Artifact identity and integrity

Each artifact must record stage, module, canonical backend, target, format,
producer identity, path, size, and SHA-256. Publication must use a temporary
path and atomic move, then verify size and digest. File components must be
sanitized and deterministic.

### REQ-007 — Deterministic comparison and failure localization

Two equivalent builds using the same producer and target must produce identical
canonical textual artifacts and matching binary digests, except for explicitly
documented nondeterministic object sections. A failure report must identify the
backend, environment, stage, module, tool/device probe, and first mismatching
artifact.

### REQ-008 — Complete matrix ledger

One machine-readable ledger must enumerate the backend registry, environment
profiles, declared capabilities, all ten stages, outcome, evidence paths, and
requirement IDs. Missing rows, cells, receipts, or evidence are release-blocking
failures rather than implicit skips.

### REQ-009 — Incremental and collect-all execution

The verifier must support fail-fast and collect-all modes. Collect-all continues
independent backend/stage cells after a failure and reuses valid prior artifacts;
fail-fast stops at the first required failure. Retries must be addressable by
failed matrix cell without rebuilding unrelated green cells.

### REQ-010 — Diagnostic layer capture

Debug mode must preserve enough intermediate material to distinguish parser,
lowering, optimization, backend translation, toolchain, linker, loader/runtime,
and device failures. The ordinary build path must not print or write these
artifacts unless requested.

## Acceptance criteria

- AC-001: Parser tests cover every accepted and rejected CLI form in REQ-001.
- AC-002: A real pure-Simple build publishes and validates all six shared-stage
  artifacts for a multi-module fixture.
- AC-003: Every registry backend appears once in the ledger with explicit
  capabilities and every stage cell is accounted for.
- AC-004: Each applicable backend reaches its deepest available layer and
  validates artifact contents, not merely file existence.
- AC-005: GPU/device rows use real probe receipts; an unavailable device is an
  evidence-backed skip and a present device with bad code/readback is a failure.
- AC-006: Tampered payload, partial write, copy, move, size, digest, tool, link,
  launch, and readback paths have negative tests.
- AC-007: Collect-all reports all independent injected failures; fail-fast
  reports the first required failure.
- AC-008: Coverage and matrix gates satisfy the selected NFR document.

## Current implementation status (2026-08-03)

- Implemented: the ten-stage enum, parser/config contract, three-state layer
  result, metadata validation, deterministic path construction, atomic verified
  sink, CLI wiring, and real source/AST/HIR/monomorphized-HIR/MIR/optimized-MIR
  driver hooks.
- Dynamically evidenced: parser behavior and five real shared artifacts through
  MIR. The optimized-MIR integration run did not complete before its outer test
  timeout.
- Incomplete: backend capability registry/ledger, explicit `NOT_APPLICABLE`
  accounting, every backend-specific artifact hook, runtime/device receipts,
  environment matrix execution, collect-all cell runner, and coverage gate.

## Out of scope

- Replacing backend algorithms or changing generated-program semantics.
- Treating the Rust seed as production verification evidence.
- Requiring unavailable proprietary hardware in every developer workstation;
  availability must instead be probed and accounted for.
