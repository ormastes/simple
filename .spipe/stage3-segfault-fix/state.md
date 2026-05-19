# SStack State: stage3-segfault-fix

## User Request
> fix Stage 3 SEGFAULT (LIM-010) — bootstrap deploy Stage 3 exits with code 139 (SEGFAULT). Stages 2/4/5 pass. Investigate and fix the crash.

## Task Type
bug

## Refined Goal
> Fix the bootstrap Stage 3 SEGFAULT (exit code 139) caused by duplicate LLVM CLI option registration when static LLVM objects in libsimple_native_all.a register options at load time, conflicting with the Stage 2 compiler's own LLVM instance. The fix should allow Stage 3 to complete successfully (exit 0) so the bootstrap pipeline no longer treats it as non-fatal/optional.

## Acceptance Criteria
- [ ] AC-1: Root cause confirmed — identify the exact LLVM constructor conflict path in Stage 3 native-build
- [ ] AC-2: LLVM constructor stripping works reliably — strip_llvm_constructors() removes .init_array/.ctors from all relevant .cpp.o files before linking
- [ ] AC-3: Stage 3 exits 0 — bootstrap-from-scratch.sh Stage 3 completes without SEGFAULT
- [ ] AC-4: Stage 3 output binary is functional — the Stage 3 compiler can compile a test program
- [ ] AC-5: No regression — Stages 2, 4, 5 still pass after the fix
- [ ] AC-6: Stage 3 non-fatal workaround removed — exit code 2 fallback no longer needed

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-19
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** bug
**Feature slug:** stage3-segfault-fix

**Analysis:**
- Root cause: Static LLVM objects in `libsimple_native_all.a` register CLI options via C++ constructors at load time. When Stage 2 compiler (which has its own LLVM) invokes native-build, the resulting Stage 3 binary has duplicate LLVM option registrations → "Option 'debug-counter' registered more than once!" → SIGSEGV (exit 139).
- Current mitigations: Cranelift fallback, constructor stripping via `strip_llvm_constructors()`, `LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1`, and Stage 3 treated as non-fatal (exit 2).
- Goal: Make constructor stripping reliable enough that Stage 3 passes, then remove the non-fatal workaround.

**Key files:**
- `scripts/bootstrap/bootstrap-from-scratch.sh` — bootstrap pipeline, Stage 3 definition
- `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs` — `strip_llvm_constructors()` logic
- `src/compiler_rust/compiler/src/codegen/llvm/backend_core.rs` — LLVM backend core
- `doc/09_report/bootstrap_crash_report_2026_04_01.md` — diagnostic report

**Parallel agent plan:**
- Agent A (Research): Deep-dive into strip_llvm_constructors() implementation, verify it covers all .cpp.o files, check if .init_array AND .ctors sections are both handled
- Agent B (Research): Examine bootstrap-from-scratch.sh Stage 3 flow, identify where exit 2 fallback is, check what environment variables are set
- Agent C (after A+B): Implement fix based on findings

### 2-research
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
