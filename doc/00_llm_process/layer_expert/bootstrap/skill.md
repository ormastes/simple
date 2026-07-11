# bootstrap Layer Expert

## Role

Own layer-specific process knowledge for the 3-stage bootstrap pipeline:
`src/compiler/80.driver/driver_bootstrap.spl` orchestrates seed (Rust) → stage2
(Simple on Rust) → stage3 (self-hosted Simple binary). This layer also owns
the JIT Cranelift backend stability track (stage2 uses LLVM llc by default; JIT
is opt-in via `SIMPLE_BOOTSTRAP_REAL_LLVM` env var). Tracks redeploy gate
(`scripts/bootstrap/redeploy_gate.sh`), smoke-matrix verification, and all
bootstrap-blocking regressions.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)
- [impl skill](../../../../.claude/skills/impl/IMPL.md)

## Layer Links

- Driver: [src/compiler/80.driver/driver_bootstrap.spl](../../../../src/compiler/80.driver/driver_bootstrap.spl)
- Gate: [scripts/bootstrap/redeploy_gate.sh](../../../../scripts/bootstrap/redeploy_gate.sh)
  (smoke-matrix fixture verification before any forward push).
- Bootstrap stages plan:
  [doc/03_plan/compiler/bootstrap/redeploy_stage4_plan_2026-07-09.md](../../../../doc/03_plan/compiler/bootstrap/redeploy_stage4_plan_2026-07-09.md).
- Rust seed: `src/compiler_rust/compiler/src/pipeline/` (stage2 compiler only;
  after stage3 hand-off, seed not executed by default).
- Unit specs: `test/01_unit/compiler/80.driver/` (e.g. `driver_bootstrap_spec.spl`).

## Redeploy #79 Status (2026-07-10)

**Wall:** short-circuit `and`/`or` undef dominance (#135, not yet fixed).

**Fixed (landed):**
- **RuntimeDict never grew — THE stage-4 in-process wall (2026-07-11):** compiled-code
  dicts were fixed-capacity (slots inline, `rt_dict_set` → `false` on full, bool
  ignored by compiled code) so the 9th insert into any `{}` silently dropped —
  `SymbolTable.scopes` lost scope 9+ → nil-receiver trap = deployed binary's instant
  `native-build` crash, `check` exit-3, and the reason test/check still delegate.
  Fix: [src/compiler_rust/runtime/src/value/dict.rs](../../../../src/compiler_rust/runtime/src/value/dict.rs)
  (separate slot alloc + ×2 growth at 3/4 load). Reaches `bin/simple` only after
  seed/runtime rebuild + stage-4 redeploy. Companion fix: Cranelift adapter mapped
  `Host` → x86-64 (Linux ELF objects on arm64 macs);
  [cranelift_codegen_adapter.spl](../../../../src/compiler/70.backend/backend/cranelift_codegen_adapter.spl)
  now resolves via `host_arch()`. Debug chain:
  [stage4_compiled_dict_no_growth_2026-07-11.md](../../../../doc/08_tracking/bug/stage4_compiled_dict_no_growth_2026-07-11.md).
- **#131 dup-SSA phi allocation** (var_reassign_ssa.spl): alloca slot reuse
  across distinct SSA values caused phi duplication under Cranelift. Fix:
  [src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl](../../../../src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl)
  (verify alloca freshness per SSA root).
- **#133 nil-arg-types guarded** (core_codegen.spl): LLVM type-check now guards
  all nil call arguments with `valid_llvm_type()` before marshalling to Cranelift.
  [src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl](../../../../src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl).

**Prior fixes (redeploy #79 init):**
- **#128 HIR block tail-drop** (HirBlock.has): expressions weren't recognizing
  tail-drops in single-expr blocks.
- **#130 arg-wipe in seed stage2**: bootstrap_main arg handling.

## Gotchas

1. **JIT path is opt-in:** seed stage2 defaults to LLVM llc (via
   `SIMPLE_BOOTSTRAP=1` without `SIMPLE_BOOTSTRAP_REAL_LLVM`). Cranelift gate
   tests are manual. Do not force JIT as default without smoke-matrix sign-off.
2. **Redeploy gate enforces smoke matrix:** any forward push must pass
   `scripts/bootstrap/redeploy_gate.sh` (compiler lint/fmt/check + bootstrap
   stage2/stage3 round-trip + test subset). Gate failures are hard stops.
3. **stage2 binary is ephemeral:** only used during bootstrap. After stage3
   succeeds, discard it — no production reliance on stage2 artifacts.

## Update Rule

After any bootstrap, JIT stability, or redeploy-gate change, refresh this skill
with new wall status, fixed issue links, and concrete gotchas.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`
