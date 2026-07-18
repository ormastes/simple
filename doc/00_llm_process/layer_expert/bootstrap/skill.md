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

**2026-07-11 evening follow-up (redeploy #79 root-cause & perf hardening):**
- **check hang wall:** check worker spawned as the `bin/simple` SYMLINK → argv0-based
  seed-sibling lookup in `_cli_driver_binary()` fails → no delegation → in-process frontend
  grind on full check app + compiler imports → parser gap #2 at mailbox.spl:525 → 300s kill.
  Fix: `resolve_worker_binary()` in
  [src/app/cli/check_entry.spl](../../../../src/app/cli/check_entry.spl) (spawn real
  `bin/release/<triple>/simple`; 300s+ → 2.9s). Debug: [stage4_compiled_dict_no_growth_2026-07-11.md](../../../../doc/08_tracking/bug/stage4_compiled_dict_no_growth_2026-07-11.md) § evening follow-up.
- **print-loss wall ROOT-CAUSED:** seed's bootstrap-MIR/LLVM lane lowers `[text].join(sep)`
  to a SILENT NULL constant (no runtime call emitted, no error) — CLI print builtin joins its
  args, so all in-process prints die; `rt_print_str` (core_string.spl) silently no-ops on the
  degenerate (0x1,0) pair → exit-0 loss. Literals/concat fine; interpolation `"{n}"` prints
  literal braces in the same lane ([bootstrap_mir_interpolation_literal_braces_2026-07-11.md](../../../../doc/08_tracking/bug/bootstrap_mir_interpolation_literal_braces_2026-07-11.md)). Fix pattern = commit `b48d79b8c6`
  (route method through rt_* runtime call).
- **self-hosted parser gaps:** dedent-continuation CLOSED (lexer rule G27,
  [self_hosted_parser_dedent_continuation_2026-07-11.md](../../../../doc/08_tracking/bug/self_hosted_parser_dedent_continuation_2026-07-11.md));
  block-lambda-as-call-arg OPEN ([mailbox.spl:525](../../../../src/app/interpreter/async_runtime/mailbox.spl#L525)).
- **parser hot-path getenv hoist:** per-token `rt_env_get` calls in `par_line_set`/`par_col_set`
  cached to lazy process-lifetime flag (`par_env_save_enabled()`); 5 sites in
  [src/compiler/10.frontend/core/parser.spl](../../../../src/compiler/10.frontend/core/parser.spl).

**Prior fixes (redeploy #79 init):**
- **#128 HIR block tail-drop** (HirBlock.has): expressions weren't recognizing
  tail-drops in single-expr blocks.
- **#130 arg-wipe in seed stage2**: bootstrap_main arg handling.

## Redeploy #79 Operator Notes (2026-07-11)

**Parse-Error Gate False-Positives:** The phase-2 parse-error gate
(`par_had_error` check) is structurally correct but false-positives on
speculative/fragment re-lex errors. Bootstrap gate may spuriously fail during
stage2 diagnosis. Workaround: diff the actual Hir output to confirm semantic
correctness; known bug, fix in flight.

**Driver Import Pattern:** `use lazy` dynload for the compiler driver was
never implemented. `bootstrap_main.spl` now imports `compiler.driver.driver`
directly. Any driver initialization changes must verify this direct import
path still resolves.

**Native-Build Closure Discovery Limitation:** The recursive closure tracer
follows plain `use` imports but does NOT traverse `export use` shims. Only
direct imports trigger cascading collection. If re-exporting driver or
lowering modules, closure must be assembled manually or closure-tracer
extended to handle shims.

**Runtime Library Path:** `SIMPLE_RUNTIME_PATH` env var MUST be set to the
seed target directory for hosted native-build linking. The `--runtime-path`
CLI flag alone does not set the env var. Host-side wrappers must explicitly
pass both: `SIMPLE_RUNTIME_PATH="path/to/seed/target" bin/simple native-build`.
Hosted link will backfill `rt_*` externs from `libsimple_native_all.a` only if
the env var points to the correct seed target.

## Gotchas

1. **JIT path is opt-in:** seed stage2 defaults to LLVM llc (via
   `SIMPLE_BOOTSTRAP=1` without `SIMPLE_BOOTSTRAP_REAL_LLVM`). Cranelift gate
   tests are manual. Do not force JIT as default without smoke-matrix sign-off.
2. **Redeploy gate enforces smoke matrix:** any forward push must pass
   `scripts/bootstrap/redeploy_gate.sh` (compiler lint/fmt/check + bootstrap
   stage2/stage3 round-trip + test subset). Gate failures are hard stops.
3. **stage2 binary is ephemeral:** only used during bootstrap. After stage3
   succeeds, discard it — no production reliance on stage2 artifacts.

## Session update 2026-07-18

**Release-mode interpreter stack-overflow guard now default-ON:** interpreter 
detects stack exhaust and returns an error instead of crashing, improving 
robustness in production builds.

**fs_helpers file_exists self-shadow recursion fixed:** file_exists no longer 
calls itself recursively, resolving stack issues in filesystem operations.

**NEW OPEN BUG — implicit-self field assignment (doc/08_tracking/bug/interp_implicit_self_field_assignment_silent_noop_2026-07-17.md):** 
in `me` methods, field assignments without explicit `self.` prefix silently 
no-op, while the lint recommends the implicit form. This is a semantic error 
that needs investigation.

**Canonical redeploy path:** `scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift` 
(LLVM feature absent in cargo seed; Cranelift is the canonical JIT target for self-hosted stage3).
See `doc/03_plan/compiler/bootstrap/redeploy_stage4_plan_2026-07-09.md` for blocker tracking.

**f-string interpolation contract (fix 2026-07-17):** unescaped `"` inside `{...}` 
toggles nested string literal; unmatched `{` containment via newline guard for non-triple f-strings 
(parser/src/lexer/strings.rs, regression ca58e1f reverted).

## Update Rule

After any bootstrap, JIT stability, or redeploy-gate change, refresh this skill
with new wall status, fixed issue links, and concrete gotchas.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`
