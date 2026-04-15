# LLVM Backend Completion Plan

**Date:** 2026-04-04  
**Status:** Implemented (2026-04-04)  
**Scope:** Complete the LLVM backend implementation so it moves from “partial but real” to a fully supported, evidence-backed backend family.

## 1. Current Classification

LLVM support is **partial, not experimental**.

Why it is partial:
- two real self-hosted LLVM backends already exist
- the Rust bootstrap LLVM backend also exists
- the remaining work is about parity, portability, toolchain discovery, linking/sysroot behavior, and authoritative compiled proof

Why it is not experimental:
- this is not a placeholder backend
- the repo already has broad source coverage, multiple target definitions, optimization passes, native linking support, and extensive tests
- the incompleteness is about operational completeness across targets and environments, not backend existence

## 2. Completion Target

The feature is complete when the repo can truthfully state:

> LLVM is a fully supported backend family with deterministic backend selection, cross-target build/link workflows, authoritative compiled-mode tests, and a published support matrix for CLI-based, in-process, and Rust-bootstrap execution paths.

This does **not** require every LLVM-adjacent capability, such as GPU codegen, to be equally mature.

It **does** require:
- stable backend selection between `llvm-lib`, `llvm`, and fallback backends
- authoritative compiled-mode proof for supported targets
- explicit host/toolchain detection
- consistent cross-target linking and sysroot handling
- documented version support and unsupported cases

## 3. Current Gaps

### 3.1 Backend parity is incomplete

Current issue:
- `Llvm`, `LlvmLib`, and Rust/inkwell backends all exist, but not all capabilities are guaranteed to behave the same way across targets and flows

Completion requirement:
- define which path is authoritative for each supported environment
- ensure a minimum parity set across the supported targets

### 3.2 Host/toolchain detection is not cleanly portable

Current issue:
- the CLI-based lane still contains Unix-centric tool discovery assumptions
- Windows host detection is not fully normalized

Completion requirement:
- make tool discovery portable across Linux, macOS, and Windows where supported
- publish deterministic diagnostics when a toolchain is missing

### 3.3 Cross-target link behavior still depends on external environment knowledge

Current issue:
- cross-compilation often requires linker/sysroot setup that is real but not normalized by the backend itself

Completion requirement:
- define and implement one supported path for:
  - native targets
  - cross Linux targets
  - bare-metal targets
  - WASM targets

### 3.4 Test evidence still over-relies on interpreter-mode loading

Current issue:
- many LLVM tests verify structure or load behavior instead of fully authoritative compiled execution

Completion requirement:
- establish compiled-mode authoritative proof for the supported backend matrix

### 3.5 Version support is too narrow and manually encoded

Current issue:
- version handling is hardcoded around LLVM 16-18
- there is no strong compatibility contract for newer versions

Completion requirement:
- define supported LLVM version policy
- centralize compatibility checks
- provide explicit diagnostics for unsupported versions

### 3.6 Target support claims are stronger than the proof matrix

Current issue:
- target definitions exist for many architectures, but the strength of proof differs by target

Completion requirement:
- every target must be classified with real proof status, not only code presence

## 4. Final Backend Model

### 4.1 `LlvmLib` as the preferred hosted path

Use the in-process `libLLVM` backend as the primary hosted LLVM path where `libLLVM` is available.

Why:
- fewer subprocess/tool dependencies than the CLI path
- stronger integration surface
- better candidate for deterministic hosted builds

Completion requirements:
- stable IR generation
- stable optimization execution
- stable object emission
- native linking for the documented supported targets

### 4.2 `Llvm` CLI path as the portable fallback

Use the CLI-based `llc` / `opt` path where `libLLVM` is unavailable but LLVM tools exist.

Completion requirements:
- consistent toolchain discovery
- clean diagnostics for missing `llc`, `opt`, `clang`, `wasm-ld`, `nm`
- documented version and platform behavior

### 4.3 Rust/inkwell path as bootstrap and advanced lane

Use the Rust backend as:
- bootstrap path
- advanced LLVM integration path
- optional GPU-oriented future expansion lane

Completion requirements:
- keep it aligned with the supported LLVM version policy
- define whether it is equal-status production support or a bootstrap-specialized path

## 5. Required Support Matrix

Every target/backend combination must be classified as one of:
- `stable`
- `supported with external sysroot/toolchain requirements`
- `partial`
- `unsupported`

Required first-class target rows:
- x86_64 native
- i686 native
- AArch64 cross
- ARMv7 cross
- RISC-V 32 bare-metal
- RISC-V 64 cross or bare-metal
- WASM32
- WASM64

Required backend columns:
- `llvm-lib`
- `llvm`
- `rust-llvm`

## 6. Implementation Phases

### Phase 1. Define the supported backend policy

Goal:
- remove ambiguity about which LLVM path is preferred and what counts as supported

Tasks:
- document backend selection precedence and rationale
- declare the supported host/target matrix
- define which backend is authoritative for hosted native builds, cross builds, bare-metal, and WASM

Exit criteria:
- one explicit backend policy exists in docs and code comments

### Phase 2. Centralize LLVM capability detection

Goal:
- make backend selection and failure diagnostics deterministic

Tasks:
- unify detection for:
  - `libLLVM`
  - `llc`
  - `opt`
  - `clang`
  - `nm`
  - `wasm-ld`
  - target-specific linker helpers
- fix Windows/macOS/Linux detection paths
- emit one normalized capability report

Suggested output:
- available backend kinds
- detected LLVM version
- supported targets for the current host/toolchain
- missing prerequisites

Exit criteria:
- backend selection no longer depends on scattered shell assumptions
- Windows no longer relies on Unix-only `command -v` logic

### Phase 3. Normalize version compatibility

Goal:
- convert version support from scattered checks into one compatibility layer

Tasks:
- centralize supported version parsing and policy
- support a documented LLVM range
- add explicit warning/error messages for:
  - too old
  - too new
  - mismatched CLI vs shared library versions

Exit criteria:
- a single version-compatibility module governs backend availability

### Phase 4. Close native parity for `llvm-lib` and `llvm`

Goal:
- make the hosted native path robust and interchangeable within the supported subset

Tasks:
- define a parity checklist:
  - function lowering
  - globals
  - control flow
  - calls
  - structs/enums
  - optimization levels
  - object emission
  - native linking
- add backend-comparison tests for the parity subset

Exit criteria:
- x86_64 hosted builds produce matching functional results via `llvm-lib` and `llvm`

### Phase 5. Normalize cross-target linking and sysroot handling

Goal:
- remove undocumented environment dependence from cross-target workflows

Tasks:
- add explicit target toolchain descriptors for:
  - linker
  - sysroot
  - crt objects
  - default flags
- define resolution order:
  - explicit CLI args
  - env vars
  - config
  - built-in defaults
- make errors actionable when sysroots or linkers are missing

Exit criteria:
- AArch64, ARMv7, RISC-V, and WASM targets fail clearly when prerequisites are absent
- supported setups are reproducible from docs

### Phase 6. Make authoritative compiled tests the default proof

Goal:
- stop treating file-load success as sufficient backend proof

Tasks:
- add compiled-mode E2E proof per supported target class
- ensure tests verify real binary/object execution where applicable
- separate:
  - structural IR tests
  - backend translation tests
  - optimization tests
  - compiled execution tests

Required proof classes:
- hosted native execution
- bare-metal object or ELF generation
- WASM artifact generation
- cross-target link success where the host toolchain exists

Exit criteria:
- each README-supported target has at least one compiled authoritative proof

### Phase 7. Publish the target/backend support matrix

Goal:
- make LLVM support claims auditable

Tasks:
- generate or maintain one machine-readable matrix
- classify every backend-target pair
- include:
  - proof status
  - required external tools
  - known limits

Exit criteria:
- README wording can point to one source-of-truth support matrix

### Phase 8. Decide the GPU lane explicitly

Goal:
- remove ambiguity around GPU support

Options:
1. keep GPU as Rust-backend-only advanced support
2. expand self-hosted LLVM backends toward GPU targets
3. explicitly mark GPU codegen out of scope for the general LLVM completion milestone

Recommended:
- keep GPU out of the core LLVM completion milestone
- classify it separately as advanced or experimental support

Exit criteria:
- LLVM “complete” does not imply GPU parity unless that work is actually done

## 7. Test Plan

### 7.1 Hosted native authoritative proof

Required:
- x86_64 compiled execution through `llvm-lib`
- x86_64 compiled execution through `llvm`
- parity comparison spec for both backends

### 7.2 Cross-target proof

Required target groups:
- AArch64
- ARMv7
- RISC-V 32
- RISC-V 64

Minimum proof:
- object or final artifact generation
- link success when prerequisites exist
- clear skip/fail behavior otherwise

### 7.3 WASM proof

Required:
- WASM32 artifact generation
- optional runtime smoke where a supported runner exists
- explicit `wasm-ld` capability checks

### 7.4 Bare-metal proof

Required:
- LLVM backend integrates cleanly with the bare-metal build path
- at least one authoritative RISC-V bare-metal artifact proof
- at least one authoritative ARM bare-metal artifact proof

### 7.5 Negative and diagnostic proof

Required:
- unsupported LLVM version
- missing `libLLVM`
- missing CLI tools
- missing sysroot
- mismatched host/target linker

## 8. Documentation Plan

Update:
- README
- backend guide docs
- bootstrap/build docs
- support matrix report

Required public wording after completion:
- separate `llvm-lib`, `llvm`, and Rust/inkwell paths
- specify the supported LLVM version range
- specify target support class per target, not just a flat target list

## 9. NFR Targets

### Reliability

- backend auto-selection must be deterministic
- missing-tool diagnostics must be explicit and actionable
- backend-target support claims must map to real compiled tests

### Performance

- `llvm-lib` should remain the preferred low-overhead hosted path when available
- backend capability detection should be fast and cached where practical

### Maintainability

- target/toolchain definitions should be centralized
- version compatibility logic should exist in one place
- README claims should derive from a support matrix, not ad hoc prose

## 10. Recommended Public State After Completion

After Phases 1 through 7 are complete:

- `llvm-lib`: stable hosted primary path
- `llvm`: stable CLI fallback path
- Rust/inkwell: supported bootstrap/advanced path
- target support documented per target with explicit proof class

At that point the repo can move from:
- `partial but real`

to:
- `fully supported LLVM backend family with explicit backend/target matrix`

without overclaiming GPU or unverified cross-target lanes.

## 11. Immediate Next Steps

1. Write the backend policy and supported backend-target matrix.
2. Centralize LLVM capability and version detection.
3. Fix host portability in CLI tool discovery.
4. Add compiled authoritative proof for x86_64 `llvm-lib` and `llvm`.
5. Normalize cross-target linker/sysroot handling and diagnostics.
