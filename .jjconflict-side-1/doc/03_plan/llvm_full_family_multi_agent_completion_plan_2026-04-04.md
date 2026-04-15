# LLVM Full-Family Multi-Agent Completion Plan

**Date:** 2026-04-04  
**Status:** Implemented — Outcome B (honest contraction)  
**Execution model:** parallel agents with bounded ownership  
**Program owner:** main agent  
**Goal:** move LLVM from a promoted subset to a fully closed backend family across all declared public rows

## 1. Why A New Plan Is Needed

The current LLVM work is real and substantial, but it is not yet a full-family completion:

- [llvm_backend_completion_plan_2026-04-04.md](doc/03_plan/llvm_backend_completion_plan_2026-04-04.md) completed the **promoted subset**
- [llvm_support_matrix.spl](src/compiler/70.backend/backend/llvm_support_matrix.spl) still contains non-final states:
  - `partial`
  - `supported (external toolchain)`
  - `unsupported`
- `rust-llvm` is still bootstrap-only and excluded from the public matrix

This plan is different:

- it is **not** about documenting the current stable subset
- it is about closing or explicitly removing every remaining public-family gap

## 2. Completion Target

This program is complete only when the repo can truthfully say:

> LLVM is a fully supported backend family across its declared backend and target rows, with deterministic backend selection, normalized cross-target toolchain behavior, compiled-mode proof for every supported row, and no ambiguous middle-state public claims.

For this plan, that means:

- every current target row is resolved to either:
  - `stable`
  - `unsupported`
- no public row remains:
  - `partial`
  - `supported (external toolchain)`
- `rust-llvm` is either:
  - promoted to a real public backend column with proof
  - or formally removed from any “family completeness” claim

## 3. Current Matrix And Required Closure

### Current matrix snapshot

From [llvm_support_matrix.spl](src/compiler/70.backend/backend/llvm_support_matrix.spl):

| Target | llvm-lib | llvm | Current problem |
|--------|----------|------|-----------------|
| `x86_64` | stable | stable | already closed |
| `i686` | partial | partial | multilib/link closure missing |
| `aarch64` | supported external | stable | libLLVM cross row still incomplete |
| `armv7` | supported external | supported external | cross/sysroot row incomplete |
| `riscv64` | supported external | stable | libLLVM cross row still incomplete |
| `riscv32` | partial | partial | hosted/cross/runtime closure missing |
| `wasm32` | unsupported | stable | llvm-lib row missing |
| `wasm64` | unsupported | stable | llvm-lib row missing |

Out-of-band row:
- `rust-llvm` — bootstrap-only, not yet a real public backend column

### Closure requirement per row

This program must resolve each remaining row:

- `i686`: multilib compile-link-run or explicit unsupported demotion
- `aarch64` llvm-lib: object/link parity or explicit unsupported demotion
- `armv7` llvm + llvm-lib: supported setup with reproducible sysroot/link proof or explicit unsupported demotion
- `riscv64` llvm-lib: object/link parity or explicit unsupported demotion
- `riscv32`: real closure for the intended support story, or explicit unsupported demotion
- `wasm32` llvm-lib: real implementation or explicit unsupported demotion from the family-complete claim
- `wasm64` llvm-lib: same as above
- `rust-llvm`: real backend or explicit exclusion from the backend family claim

## 4. Non-Negotiable Rules

- No README or audit promotion before the full matrix is resolved.
- No public target row may stay in an ambiguous state.
- “Supported if you already know the right sysroot” is not acceptable as a final public family status.
- A row can remain supported only if the repo provides:
  - deterministic discovery
  - actionable diagnostics
  - authoritative proof
- If a row cannot be completed within the family, it must be moved to `unsupported` in the same implementation program.

## 5. Agent Team Layout

### Agent A: Matrix Governance and Status Contract

**Owns**
- [llvm_support_matrix.spl](src/compiler/70.backend/backend/llvm_support_matrix.spl)
- status enums and matrix formatting
- public status rules

**Tasks**
- define the final two-state public rule:
  - `stable`
  - `unsupported`
- remove public use of:
  - `partial`
  - `supported (external toolchain)`
- add internal-only metadata if needed for migration, but do not expose it as public final status
- add an explicit migration section in the matrix module if rows are being demoted

**Acceptance**
- the matrix format supports the final completion policy
- every backend-target row can be rendered unambiguously

### Agent B: Hosted x86/x86_64 and Multilib Closure

**Owns**
- hosted native row proofs
- `i686` closure
- native linker/multilib handling

**Tasks**
- keep `x86_64` parity green
- fully close `i686`:
  - compile
  - object emission
  - link
  - run
- normalize multilib detection:
  - gcc/clang path
  - CRT objects
  - 32-bit libc
- if reliable multilib closure cannot be made portable enough, demote `i686` to `unsupported`

**Acceptance**
- `i686` is either `stable` with proof or `unsupported` with explicit diagnostics

### Agent C: AArch64 and ARMv7 Cross Closure

**Owns**
- `aarch64` and `armv7` target rows
- sysroot and linker resolution
- cross-host diagnostics

**Tasks**
- close `aarch64` for `llvm-lib` so it matches the already-stable CLI row
- close `armv7` for both backends:
  - linker resolution
  - sysroot resolution
  - CRT/start objects
  - executable or artifact proof
- define a reproducible supported setup:
  - env vars
  - built-in defaults
  - install hints
- if `armv7` cannot become reproducible enough, demote it cleanly

**Acceptance**
- `aarch64` and `armv7` rows are no longer ambiguous

### Agent D: RISC-V Family Closure

**Owns**
- `riscv64`
- `riscv32`
- hosted vs baremetal interpretation

**Tasks**
- close `riscv64` for `llvm-lib`
- decide whether `riscv32` is:
  - full hosted support
  - stable baremetal-only support
  - unsupported for the public LLVM family
- if `riscv32` remains supported, provide:
  - deterministic toolchain resolution
  - clear ABI/ld flags
  - real artifact and execution proof
- eliminate the current “partial but maybe usable” state

**Acceptance**
- both RISC-V rows end in `stable` or `unsupported`

### Agent E: WASM Family Closure

**Owns**
- `wasm32`
- `wasm64`
- `llvm-lib` WASM implementation decision

**Tasks**
- determine whether `llvm-lib` can really emit WASM in this repo architecture
- if yes:
  - implement and prove it for `wasm32` and `wasm64`
- if no:
  - explicitly mark `llvm-lib` WASM rows `unsupported`
  - adjust the family-complete wording so only supported rows are counted
- strengthen CLI proof beyond artifact existence where feasible

**Acceptance**
- WASM rows are decisively closed, not aspirational

### Agent F: rust-llvm Decision and Integration

**Owns**
- Rust LLVM backend path
- public-vs-bootstrap classification
- parity expectations with `llvm` / `llvm-lib`

**Tasks**
- decide one of two allowed outcomes:
  1. promote `rust-llvm` to a public backend column
  2. keep it bootstrap-only and remove it from “full family” completion scope
- if promoted:
  - define supported targets
  - add proof matrix
  - add capability/version diagnostics
- if not promoted:
  - update docs/reports so no family-complete statement quietly depends on it

**Acceptance**
- `rust-llvm` is no longer a hidden ambiguity in the family story

### Agent G: Capability, Version, and Toolchain Normalization

**Owns**
- [llvm_capability.spl](src/compiler/70.backend/backend/llvm_capability.spl)
- [llvm_version.spl](src/compiler/70.backend/backend/llvm_version.spl)
- [llvm_cross_target.spl](src/compiler/70.backend/backend/llvm_cross_target.spl)

**Tasks**
- centralize final toolchain resolution for all target rows
- unify host detection across Linux/macOS/Windows
- ensure diagnostics distinguish:
  - tool missing
  - version unsupported
  - sysroot missing
  - linker missing
  - CRT/multilib missing
- support final matrix generation from actual capability rules

**Acceptance**
- capability and version logic can justify every matrix cell

### Agent H: Proof Pack and CI Closure

**Owns**
- compiled proof specs
- parity specs
- link/run matrix
- negative cases

**Tasks**
- add or extend authoritative proof per target/backend row
- separate proof classes:
  - capability proof
  - compile proof
  - link proof
  - run proof
  - negative diagnostics
- add CI-friendly subset and host-aware subset
- ensure no row is promoted on artifact existence alone when execution proof is expected

**Acceptance**
- every stable row has the right proof depth
- every unsupported row has a deterministic failure spec

### Main Agent: Integration and Public Promotion

**Owns**
- README
- audit doc
- completion report
- final matrix coherence

**Tasks**
- integrate row decisions from all agents
- update public docs only after proof closes
- produce one final report explaining:
  - rows promoted
  - rows demoted
  - why

**Acceptance**
- public docs and support matrix say exactly the same thing

## 6. Detailed Work Breakdown By Row

### `i686`

Required work:
- multilib capability detection
- 32-bit CRT resolution
- 32-bit libc detection
- `llvm` and `llvm-lib` object/link proof
- execution proof on host or QEMU user if host execution is impractical

Allowed end states:
- `stable`
- `unsupported`

### `aarch64`

Required work:
- close `llvm-lib` row to match CLI row
- prove object/link path with reproducible cross toolchain
- add runtime or artifact-execution proof

Allowed end states:
- `stable`
- `unsupported`

### `armv7`

Required work:
- resolve hard-float ABI assumptions
- normalize linker/sysroot/CRT resolution
- add compile/link proof
- add execution proof if practical, otherwise document artifact proof standard

Allowed end states:
- `stable`
- `unsupported`

### `riscv64`

Required work:
- close `llvm-lib` row
- finalize ABI flags and linker expectations
- add artifact and execution proof

Allowed end states:
- `stable`
- `unsupported`

### `riscv32`

Required work:
- decide public support story first
- if supported:
  - hosted or baremetal-only contract
  - linker policy
  - ABI flags
  - proof path
- if not supportable:
  - demote to `unsupported`

Allowed end states:
- `stable`
- `unsupported`

### `wasm32` and `wasm64`

Required work:
- decide whether `llvm-lib` WASM is real or not
- if real, implement and prove it
- if not, explicitly keep unsupported and document that the family-complete claim excludes those rows for `llvm-lib`

Allowed end states:
- `stable`
- `unsupported`

## 7. Required Proof Matrix

Every final `stable` row must have:

- one capability check
- one compile proof
- one link/artifact proof
- one execution proof where meaningful
- one negative-case proof

### Minimum target/backend proof expectations

#### Hosted native

- `x86_64`:
  - `llvm-lib`
  - `llvm`
  - execution proof

- `i686`:
  - `llvm-lib`
  - `llvm`
  - execution or equivalent authoritative runtime proof

#### Cross native

- `aarch64`:
  - `llvm-lib`
  - `llvm`

- `armv7`:
  - `llvm-lib`
  - `llvm`

- `riscv64`:
  - `llvm-lib`
  - `llvm`

- `riscv32`:
  - whichever support story survives

#### WASM

- `wasm32`
- `wasm64`
- both backends if supported

#### rust-llvm

- if promoted, proof per supported target row

## 8. Diagnostics That Must Exist

For every unsupported or failed row, the system must distinguish:

- backend unavailable
- LLVM version unsupported
- backend/CLI/shared-library mismatch
- linker missing
- sysroot missing
- CRT/multilib missing
- target not supported by the selected backend

No final row should fail with a vague generic “LLVM failed” message.

## 9. Execution Phases

### Phase 1: Freeze final matrix policy

Goal:
- commit to final-state matrix rules

Exit criteria:
- `partial` and `supported external` are migration-only, not final public states

### Phase 2: Capability and version closure

Goal:
- make toolchain discovery explain every remaining row

Exit criteria:
- every target/backend row has deterministic prerequisite logic

### Phase 3: Per-row implementation closure

Run in parallel:
- Agent B: `i686`
- Agent C: `aarch64` / `armv7`
- Agent D: `riscv64` / `riscv32`
- Agent E: `wasm32` / `wasm64`
- Agent F: `rust-llvm`

Exit criteria:
- each row ends in `stable` or proposed `unsupported`

### Phase 4: Proof pack integration

Goal:
- ensure every stable row is actually proven

Exit criteria:
- no promoted row depends only on code presence

### Phase 5: Public doc update

Goal:
- sync README, audit, and report to the final matrix

Exit criteria:
- public wording has no hidden qualified rows left

## 10. Definition Of Done

LLVM full-family completion is done when:

- every row in the public LLVM family matrix is `stable` or `unsupported`
- `rust-llvm` is either promoted with proof or formally excluded from the family claim
- every `stable` row has authoritative proof
- every `unsupported` row has deterministic diagnostics
- README and audit no longer need qualifier language for hidden middle states

## 11. Recommended Final Public Outcomes

Two acceptable final outcomes exist:

### Outcome A: true full-family closure

- all intended rows become `stable`
- `rust-llvm` becomes a real public backend or is intentionally not part of the family claim

### Outcome B: honest contraction

- some rows are demoted to `unsupported`
- the remaining matrix is fully stable
- public docs describe only the stable closed family

Outcome B is acceptable. What is not acceptable is keeping ambiguous middle-state rows and still calling the family complete.
