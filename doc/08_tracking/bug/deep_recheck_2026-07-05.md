# Deep-Recheck Bug Inventory — 2026-07-05

Source: 9-subsystem deep-recheck workflow (sonnet audit + opus adversarial verify).
`real=` is the opus verifier's verdict. All are **current-source** bugs unless marked
`already-fixed-stale-binary`. **Verification caveat:** confirming a pure-Simple source
fix needs a fresh compiler build — via the wall-afflicted seed (broken output) or the
slow pure-Simple bootstrap — so **the stage4 wall gates trustworthy verification of most
of these**. Fix the wall, then the wide/risky items get fixed+verified in a batch.

Priority key: **P0** = short + pinned + high-confidence (do now); **P1** = difficult +
high-impact (opus); **P2** = wide/risky (fix+verify after wall); **DOC** = feature/long/dead-code (plan).

## Interpreter (flat-AST, `bin/simple run` path) — `src/compiler/10.frontend/core/interpreter/`
- **P0** [real] Result/Option payload read wrong field index: `unwrap()`/`match Ok(v)` return `__tag` (idx 0) not `__payload` (idx 1) → `Ok(42).unwrap()`=5. `eval_methods.spl:112` (construct site `eval_access.spl:482-504` uses `[__tag,__payload]`). Silent-wrong-value.
- **P1** [real] f64 silently → 0.0 when a nested call's return flows into a **typed** fast-local slot (typed param / array-literal elem). `eval_calls.spl:280` + `resolve.spl:105-133` + `env.spl:212-232` (pooled-frame LOAD_FAST). Wide, unpinned.
- **P1** [real] Trait **default** method calling `self.other_method()` → **SIGSEGV**. `eval_methods.spl` trait default dispatch. Wide, unpinned.
- **DOC** [real] `Array.map`/`reduce` unimplemented (UFCS fails); `print(array)` shows raw pointer. `eval_methods.spl:230`. Feature.
- (stale-binary) `?` non-propagation — already fixed at source (b7fe9071/da6c4d0d), stale in deployed binary.

## Type system — `src/compiler/30.types` + `35.semantics` + driver
- **P1** [real] **Phase-3 type checking is a NO-OP** — the entire 30.types checker/inference engine is never invoked. `driver.spl:613`. Highest-impact. **CONFIRMED + WARN-ONLY WIRED (2026-07-05):** `type_check_impl` is a documented no-op; the native path of `lower_and_check_impl` never builds `HmInferContext`; `infer_module` (`type_infer/inference_control.spl:594`) has zero callers. Landed opt-in warn-only wiring (`run_typecheck_warn_pass` gated by `SIMPLE_TYPECHECK_WARN=1`, log-only). Fatal enablement deferred — see `doc/03_plan/compiler/type_system/typecheck_burndown.md`.
- **P1** [real] Generic trait-bound (`where T: Trait`) never checked; unsatisfied bounds compile. `resolve.spl:712`. **CONFIRMED (2026-07-05):** `resolve_methods_with_solver` is a `return (module, [])` stub. Burndown P4 in the plan doc (integrate the post-inference `TraitSolver`).
- **P2** [real=?] Visibility/privacy enforcement has zero effect (checker never wired). `driver.spl:456`. **CONFIRMED real (2026-07-05):** `check_module_visibility` (`visibility_integration.spl:11`) is a complete checker with **zero callers**. Now invoked warn-only inside `run_typecheck_warn_pass` (same `SIMPLE_TYPECHECK_WARN=1` gate).

## Compiler frontend / HIR lowering — `10.frontend` + `20.hir`
- **P1** [real] HIR-lowering diagnostics collected but never surfaced → unsupported constructs silently compile. `driver.spl:509`.
- **P1** [real] Generic type args discarded during struct-literal HIR lowering → corrupts generic fields. `expressions.spl:405`.
- **P2** [real] `DictComprehension` has no HIR lowering case. `expressions.spl:397`.
- **DOC** [real] GPU shared-memory / `gpu_launch` have no HIR representation. `convert_nodes.spl`. Feature.

## Backends (multi-arch) — `src/compiler/70.backend/backend/native/regalloc.spl`
- **P2** [real] Regalloc hardcoded x86_64 → silently miscompiles ARM64/RISC-V32/64. `:336`.
- **P2** [real] Never patches AArch64/RISC-V stack-frame-size immediate. `:386`.
- **P2** [real] Injects raw x86_64-encoded spill/reload/callee-save into AArch64/RISC-V. `:462`.
- (real=False) ARM SMP secondary-core bring-up absent — verifier disputed; recheck.

## AOP — `src/compiler/10.frontend/core/aop.spl` + driver
- **P1** [real] Compiled-path advice ordering violates documented priority for after_*/around. `aop.spl:370`.
- **P1** [real] `AdviceCallInfo` drops matched advice form → after_success/around silently mis-run. `aop.spl:60`.
- **P1** [real] Compiled-path `@attribute` and `effect:` pointcuts permanently dead (driver passes empty). `driver_pipeline.spl:244`.
- **P2** [real] E1506 circular around-advice detector uses exact string equality (misses glob/module/attr). `aop_conflict_detect.spl:52`.
- **DOC** [real] E1504 ambiguous-order warning stops after first tied pair. `aop.spl:471`.

## Loader — `src/compiler/70.backend/linker` + `99.loader`
- **P0** [real] SMF header/symbol bit-flags use logical `and` not bitwise `&` → every flag collapses. `smf_reader.spl:408`.
- **P1** [real] `apply_smf_relocations` bounds-check ignores relocation write width → OOB write. `object_mapper.spl:249`.
- **P2** [real=?] `SmfReaderFfi` discards Rust SFFI returns, returns hardcoded zero/empty stubs. `smf_reader.spl:49`.
- **P2** [real=?] `compiler.loader.runtime` public facade completely unreachable. `runtime/__init__.spl:106`.
- **DOC** [real=?] `SmfCacheManager` refcount uses `fn` not `me` on self param. `smf_cache_manager.spl:36`.

## Tooling (lint / fmt / duplication) — cert Phase-2 relevant
- **P1** [real] `bin/simple lint/fmt/fix` completely non-functional — global function-name collision. `sffi/cli.spl:137`.
- **P1** [real] Formatter silently corrupts string-literal/comment content + mangles generic `<...>`. `formatter/main.spl:481`.
- **P2** [real] Duplicate-detection tokenizer has no backslash-escape handling. `duplicate_check/tokenizer.spl:126`.
- **P2** [real] dup config `apply_analysis_mode()` catch-all forces semantic mode. `duplicate_check/config.spl:61`.

## Test runner — cert Phase-4 (test-evidence integrity)
- **P0** [real] **Default synthetic PASS** when a spec has no parseable summary → **false-GREEN by default**. `test_executor_parsing.spl:271`.
- **P1** [real] Parallel/async path never sets per-test env → silently disables DI-lock/mode-detect. `test_runner_async.spl:117`.
- **P2** [real] `--tag` filtering can't match any real spec (extract_tags too narrow). `test_manifest_scanner.spl:174`.
- **P2** [real=?] Duplicate `TestDatabase` type (struct vs class) — #41 collision class. `test_db_compat.spl:23`.

## RTL / sspec docs
- **P0** [real] doc-coverage counts private `fn` as public, excludes every `pub fn`. `doc_coverage_dynamic.spl:51`.
- **P0** [real] spipe-docgen hardcodes `Updated: 2026-06-01` in every generated sspec doc. `generator.spl:184`.
- **P2** [real] `src/app/doc_coverage/` dead code, crashes on undef. `terminal_renderer.spl:37`.
- **DOC** [real=False] ~3000-line duplicate VHDL transpiler (80.driver) is dead code. `driver_compile_vhdl_codegen.spl:48`.

## Batch plan
1. **Now (P0, pinned, opus-reviewed sonnet lane):** payload-index, SMF `and`→`&`, false-GREEN default, doc-coverage private-as-public, spipe hardcoded-date.
2. **Now (P1, opus):** type-checker-is-a-noop + generic trait-bound.
3. **After wall (P1/P2 batch):** interpreter f64/SIGSEGV, AOP compiled-path (4), lint/fmt non-functional, regalloc multi-arch, HIR diagnostics/generic-args, loader relocation/facade.
4. **DOC/features:** Array.map/reduce, DictComprehension lowering, GPU HIR, dead-code removals.
