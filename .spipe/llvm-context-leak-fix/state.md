# SStack State: llvm-context-leak-fix

## User Request
> fix LLVM Context memory leak — Box::leak in backend_core.rs:67 prevents memory accumulation during long compilation. Fix the leaked LLVM Context to be properly dropped.

## Task Type
bug

## Refined Goal
> Fix the LLVM Context memory leak where Box::leak(Box::new(Context::create())) creates 'static references that are never freed, causing ~30-40 MB per file compiled. Use ManuallyDrop + custom Drop impl to ensure Module/Builder are dropped before Context, eliminating the self-referential lifetime issue without new dependencies.

## Acceptance Criteria
- [ ] AC-1: LlvmBackend in backend_core.rs owns Context (no Box::leak), has Drop impl that drops Module/Builder before Context
- [ ] AC-2: LlvmJit in llvm_jit.rs owns Context (no Box::leak), has Drop impl
- [ ] AC-3: GPU backend in gpu.rs owns Context (no Box::leak), has Drop impl
- [ ] AC-4: cargo check passes with no new errors
- [ ] AC-5: cargo test in codegen passes (no regression)
- [ ] AC-6: No remaining Box::leak of Context::create in codegen directory

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
**Feature slug:** llvm-context-leak-fix

**Analysis:**
- 3 Box::leak sites: backend_core.rs:140, llvm_jit.rs:62, gpu.rs:216/714
- Root cause: inkwell Context owns all IR; Module<'ctx>/Builder<'ctx> borrow from it. Self-referential struct can't own Context and borrow from it simultaneously.
- Current impact: ~30-40 MB leaked per file, ~118 GB peak during bootstrap with 3573 files
- Fix: ManuallyDrop wrapper for Module/Builder, Box<Context> for owned Context, custom Drop impl ensuring drop order

**Key files:**
- `src/compiler_rust/compiler/src/codegen/llvm/backend_core.rs` — LlvmBackend struct + constructor
- `src/compiler_rust/compiler/src/codegen/llvm_jit.rs` — LlvmJit struct + constructor
- `src/compiler_rust/compiler/src/codegen/llvm/gpu.rs` — GPU backend struct + constructor

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
