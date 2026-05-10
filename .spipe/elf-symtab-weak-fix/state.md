# SStack State: elf-symtab-weak-fix

## User Request
> impl next with agent teams and minimize duplication. 2 │ LLVM/Rust Self-Host in SimpleOS │ P0 │ Blocked (ELF SYMTAB bug)

## Task Type
bug

## Refined Goal
> Fix the ELF SYMTAB bug where the Cranelift codegen backend emits weak boot-alias symbols with LOCAL binding instead of WEAK binding, violating the ELF `sh_info` invariant and causing `ld.lld` to reject the output — unblocking LLVM/Rust/Simple self-host in SimpleOS.

## Acceptance Criteria
- [ ] AC-1: MIR functions annotated as weak (boot-aliases) are emitted with `STB_WEAK` binding in the ELF `.symtab` section
- [ ] AC-2: `sh_info` in the `.symtab` section header correctly points past all LOCAL symbols (WEAK symbols appear in the global partition)
- [ ] AC-3: `ld.lld` accepts the emitted object files without "WEAK symbol in LOCAL partition" errors
- [ ] AC-4: `cargo test` in `src/compiler_rust/compiler/` passes (no regression)
- [ ] AC-5: `bin/simple test` passes (full test suite, no regression)
- [ ] AC-6: SimpleOS kernel ELF builds and loads in QEMU (native-build exits 0)
- [ ] AC-7: `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` succeeds (self-hosted binary not broken)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-10
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
**Feature slug:** elf-symtab-weak-fix

**Analysis:**
- Root cause per roadmap: `src/compiler_rust/compiler/src/codegen/cranelift.rs` (really `common_backend.rs:526-551`) — `declare_functions` only uses `Local`, `Import`, and `Preemptible` linkage. No path handles weak-annotated functions.
- The pure-Simple ELF writer (`src/compiler/70.backend/linker/elf_writer.spl` line 394) correctly sorts `STB_LOCAL` before `STB_GLOBAL/STB_WEAK`, so it handles weak properly. The bug is in the Rust seed compiler's Cranelift codegen.
- `cranelift_module::Linkage` enum does NOT have a Weak variant. The `object` crate's `write::Symbol` struct has a `weak: bool` field. The fix needs to either:
  (a) Use `Preemptible` (which cranelift-object may map to weak), or
  (b) Post-process the object bytes to set weak binding on relevant symbols

**Key files:**
- `src/compiler_rust/compiler/src/codegen/common_backend.rs` — declare_functions linkage logic
- `src/compiler_rust/compiler/src/mir/mod.rs` or similar — MIR function annotations
- `src/compiler_rust/compiler/src/codegen/cranelift.rs` — compile_module, reemit_clean_macho (Mach-O analog exists for the weak field)
- Pure-Simple ELF writer: `src/compiler/70.backend/linker/elf_writer.spl` (reference for correct behavior)

**Parallel agent plan (3 teams):**
- Agent A (Research): Find how weak annotations flow through AST→MIR, what cranelift-object does with Preemptible linkage for ELF, identify exact fix location
- Agent B (Research): Find SimpleOS boot-alias symbols and verify which specific functions need weak binding
- Agent C (after A+B): Implement the fix in common_backend.rs + verify

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
