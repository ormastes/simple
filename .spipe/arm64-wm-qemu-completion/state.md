# Feature: ARM64 WM QEMU completion

## Raw Request

`$sp_dev impl arm64 wm qemu completion....md`

## Task Type

bug

## Refined Goal

Produce an admitted pure-Simple bootstrap compiler and use it to build and
verify the strict ARM64 SimpleOS WM image in QEMU with same-run serial, QMP
input, and framebuffer evidence.

## Acceptance Criteria

- AC-1: Indexed `LoadGlobal` extracts both payload IDs as raw scalars and the
  focused regression excludes aggregate `SymbolId.id` projection.
- AC-2: A fresh Phase 2 candidate passes Cranelift sanity, native smoke, and
  canonical non-entry module-global functional admission without fallback.
- AC-3: Phase 3 built from the admitted Phase 2 candidate passes functional and
  native admission and contains no Rust-seed provenance.
- AC-4: The strict ARM64 readiness and attested build wrappers pass using a
  receipt bound to the exact admitted compiler hash.
- AC-5: One QEMU run retains correlated serial, QMP keyboard/pointer input,
  before/after RAMFB captures, and passing evidence metadata/report.
- AC-6: Focused SPipe, compiler/core/MCP smoke, stub, direct-runtime-access,
  documentation freshness, and repository-layout gates pass once.
- AC-7: The authoritative completion plan records exact commands, hashes,
  artifacts, owners, reviewers, and any still-unavailable capability row.

## Scope Exclusions

None. Phase 2 is an unblocker only; it is not release evidence. Diagnostic QMP
or an emitted but unadmitted binary does not satisfy the QEMU evidence goal.

## Cooperative Review

- Sidecars: compiler artifact-admission review and Phase 2/3 recovery lane.
- Merge owner: root Codex agent.
- Final reviewer: ARM64 integration owner at normal/highest capability.
- Shared interfaces: `translate_load_global_ids`, compiler receipt schema, and
  QEMU evidence metadata contract.
- Manual steps: `Admit the pure-Simple compiler`; `Build the strict ARM64 WM
  image`; `Drive QMP input and capture RAMFB`; `Audit correlated evidence`.
- Setup/checkers: canonical bootstrap admission, ARM64 attested-build, QMP
  input-evidence, and final verification wrappers named in the plan.
- Fail-fast policy: unsupported paths remain explicit failures; no stub,
  fabricated artifact, fallback compiler, or skipped evidence row.
- Generated-manual review owner: final ARM64 integration reviewer.

## Phase

dev-done

## Log

- dev: Refined the active recovery goal into seven testable acceptance criteria
  (type: bug).
- implement: Packed `LoadGlobal` symbol and Ret local IDs now normalize through
  focused PASS 4/4 evidence (`adefa51eda`).
- verify: Final Phase 2 candidate passed Stage 2 sanity/native smoke but failed
  functional admission because LLVM module output was truncated to 104 bytes;
  Phase 3 and ARM64/QEMU remain active.
- implement: Per-instance LLVM accumulation fixed the 104-byte truncation, but
  compiled Stage 2 still drops function/global opening emissions.
- verify: Final bounded candidate `32092b8ac8...` passed sanity/native smoke and
  failed canonical admission at bare `bb0:`; Phase 3 and ARM64/QEMU remain
  active.
