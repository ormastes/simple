# backend Layer Expert

## Role

Own layer-specific process knowledge for the native codegen backend
(`src/compiler/70.backend/backend/_MirToLlvm/`). This layer transforms MIR
into LLVM IR, manages FFI marshalling (Simple ↔ C), handles aggregate
intrinsics (struct/array/enum construction), and coordinates with the linker.
Default backend is LLVM llc; Cranelift JIT is opt-in.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)
- [impl skill](../../../../.claude/skills/impl/IMPL.md)

## Layer Links

- Core codegen: [src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl](../../../../src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl)
  (expression lowering, type marshalling).
- Aggregate intrinsics: [src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl](../../../../src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl)
  (struct/array/enum lowering, dispatch).
- Native linker: [src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl](../../../../src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl)
  (link order, external symbol resolution).
- LLVM bridge: `src/compiler_rust/compiler/src/backend/llvm/` (seed LLVM codegen,
  not production after stage3).
- Unit specs: `test/01_unit/compiler/70.backend/` (e.g. `core_codegen_spec.spl`).

## Known Issues (2026-07-10)

### rt_process_run Cranelift SFFI Marshalling Bug

**Symptom:** `rt_process_run()` (shell-out execution) is unsafe under Cranelift
JIT due to stale deployed binary + seed TAG_HEAP mask mismatch in calls.rs.
Shell-outs may segfault or lose handle marshalling.

**Workaround:** Prefer direct `rt_*` primitives:
- `rt_dir_create_all(path)` instead of shell `mkdir -p`.
- `rt_file_read_text(path)` / `rt_file_write_text(path, text)` instead of shell
  `cat` / `echo`.
- `rt_file_copy(src, dst)` instead of shell `cp`.

**Permanent fix:** redeploy the bootstrap pipeline with corrected SFFI
marshalling in the deployed binary (not seed-dependent).

**File refs:**
- Seed source: `src/compiler_rust/compiler/src/backend/llvm/calls.rs` (TAG_HEAP
  mask — context-only; no production change here after stage3).
- Simple wrappers: [src/runtime/](../../../../src/runtime/) (rt_* primitives).

## Gotchas

1. **Cranelift JIT is opt-in and has known regressions:** do not force
   `SIMPLE_BOOTSTRAP_REAL_LLVM` without smoke-matrix gate sign-off. FFI
   marshalling bugs are hard to triage. Use LLVM llc for bootstrap.
2. **nil argument type-checking:** all nil call arguments must pass
   `valid_llvm_type()` before lowering to Cranelift. See
   [src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl](../../../../src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl)
   (line ~1200 area, guard sites).
3. **Aggregate intrinsics dispatch:** struct/array/enum lowering is routed
   through method-call dispatch (method_calls_literals.spl) — if ambiguous
   method resolution happens, backend will stub a body, forcing interpreter
   fallback. See
   [doc/00_llm_process/feature_expert/codegen_ambiguous_method/skill.md](../../feature_expert/codegen_ambiguous_method/skill.md).

## Update Rule

After backend regressions, FFI fixes, or linker changes, refresh this skill
with new issue links and concrete marshalling patterns.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`
