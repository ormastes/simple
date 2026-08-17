# Deep-Recheck Bug Inventory — 2026-07-05

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

Source: 9-subsystem deep-recheck workflow (sonnet audit + opus adversarial verify).
`real=` is the opus verifier's verdict. All are **current-source** bugs unless marked
`already-fixed-stale-binary`. **Verification caveat:** confirming a pure-Simple source
fix needs a fresh compiler build — via the wall-afflicted seed (broken output) or the
slow pure-Simple bootstrap — so **the stage4 wall gates trustworthy verification of most
of these**. Fix the wall, then the wide/risky items get fixed+verified in a batch.

Priority key: **P0** = short + pinned + high-confidence (do now); **P1** = difficult +
high-impact (opus); **P2** = wide/risky (fix+verify after wall); **DOC** = feature/long/dead-code (plan).

## Interpreter (flat-AST, `bin/simple run` path) — `src/compiler/10.frontend/core/interpreter/`
- **P0** [~~real~~ **REFUTED, then FIXED** — see note + 2026-08-01 measurement] Result/Option payload read wrong field index: `unwrap()`/`match Ok(v)` return `__tag` (idx 0) not `__payload` (idx 1) → `Ok(42).unwrap()`=5. ~~`eval_methods.spl:112`~~ (construct site `eval_access.spl:482-504` uses `[__tag,__payload]`). ~~Silent-wrong-value.~~ **The silent-wrong-value never happened in the live lane.** Measured behaviour is now recorded below.
- **P1** [real] f64 silently → 0.0 when a nested call's return flows into a **typed** fast-local slot (typed param / array-literal elem). `eval_calls.spl:280` + `resolve.spl:105-133` + `env.spl:212-232` (pooled-frame LOAD_FAST). Wide, unpinned.
- **P1** [real] Trait **default** method calling `self.other_method()` → **SIGSEGV**. ~~`eval_methods.spl`~~ → live dispatch is `_EvalOps/call_method_eval.spl` (`eval_method_call` / `eval_method_with_args`). Wide, unpinned; the SIGSEGV was observed by *running*, so the symptom stands — only the file pointer was to the dead duplicate.
- **DOC** [~~real~~ **PARTLY NOW-WRONG**] `Array.map`/`reduce` unimplemented (UFCS fails); `print(array)` shows raw pointer. ~~`eval_methods.spl:230`~~. Feature. Re-derived 2026-08-01 against the live `eval_array_method` (`_EvalOps/call_method_eval.spl:788-925`): `map`, `filter`, `flat_map`/`flatmap`, `any`, `all`, `enumerate` **are** implemented; `reduce` is **not** (falls through to `eval_set_error("no method 'reduce' on array")`). So half this item is stale. **2026-08-01: `reduce` implemented** (`reduce`/`fold`, `(initial, fn(acc, item))`, same closure convention as the neighbouring `map`/`filter`/`flat_map` arms; misuse is a loud `eval_set_error`, not a silent identity return). Caveat recorded honestly: it is **not** behaviourally verified in the pure-Simple lane — a closure cannot be driven through `core_interpret_expr` at all; the pre-existing `map` arm aborts there identically with `array index out of bounds: index is 0 but length is 0`, so the **harness**, not the arm, is the blocker. `reduce` is verified by structural parity with `map` only. `print(array)` raw-pointer half is untouched.

> **Dead-code audit 2026-08-01.** Every `eval_methods.spl` citation in the
> Interpreter section above pointed at a file that was a **duplicate shadowed
> by package-local `_EvalOps` copies**, deleted in `f97dfbbb8ee`. Re-derived
> against the live `eval_method_call` (`_EvalOps/call_method_eval.spl:567-654`):
> it contains **no Option/Result built-in method block whatsoever** — no
> `unwrap`, `unwrap_or`, `is_some`, `is_none`, `unwrap_err`, `is_ok`, `is_err`
> arm exists anywhere in `src/compiler/10.frontend/core/interpreter/`. The
> `val_struct_get_field_idx(receiver, 1)` code the P0 quoted lived **only** in
> the deleted file. Therefore the P0 as written ("`Ok(42).unwrap()` = 5,
> silent-wrong-value") cannot be the live pure-Simple behaviour: the live path
> falls through `func_table_lookup("Result::Ok__unwrap")` and the callable-field
> fallback to `eval_set_error("no method 'unwrap' on struct")` — a **loud
> error, not a silent wrong value**. Marked NOW-WRONG rather than deleted:
> whether the deleted block ever executed is UNKNOWN, because the sabotage
> proof covered `eval_text_method` (call site inside `_EvalOps`) and never
> measured how `eval.spl:301` resolved `eval_method_call`. **What would settle
> the historical question:** nothing — only one definition survives.
> **What replaces this P0:** a new, differently-shaped defect —
> *Option/Result built-in methods are entirely absent from the pure-Simple
> interpreter*. See
> `doc/08_tracking/bug/2026-08-01_interpreter_eval_text_method_duplicate_live_subset.md`.

> **P0 settled by measurement, then fixed — 2026-08-01 (second pass).**
> The replacement defect was confirmed by *running* the pure-Simple
> interpreter, then implemented. Method: `core_interpret_expr(source)` driven
> from a scratchpad driver with the Rust seed
> (`src/compiler_rust/target/bootstrap/simple`, 154 MB canonical build) as
> **HOST ONLY**, compiling **working-copy** interpreter source. Every number
> below is produced by the **pure-Simple interpreter under test**, not by the
> seed's own evaluator. The probe carried a deliberately-failing SENTINEL row
> (`.definitely_not_a_method()`) that stayed red throughout, so it is
> falsifiable.
>
> **What the behaviour ACTUALLY was** (answering the P0 directly): not `5`,
> and not any wrong value — *every* Option/Result method raised
> `no method '<name>' on struct`. The P0's silent-wrong-value mechanism is
> **refuted for the live lane**; it could only ever have described the deleted
> file.
>
> | expression | before | after |
> |---|---|---|
> | `"1234".parse_int().unwrap()` | ERROR `no method 'unwrap' on struct` | `1234` |
> | `"1234".parse_int().is_some()` | ERROR | `true` |
> | `"abc".parse_int().is_none()` | ERROR | `true` |
> | `"abc".parse_int().unwrap_or(7)` | ERROR | `7` |
> | `"abc".parse_int().unwrap()` | ERROR `no method 'unwrap' on struct` | **ERROR `called unwrap on None`** |
> | `nil.unwrap_or(7)` | ERROR `no method 'unwrap_or' on nil` | `7` |
> | `nil.unwrap()` | ERROR `no method 'unwrap' on nil` | **ERROR `called unwrap on None`** |
>
> The loud failure on the last two rows is the point: before the fix the live
> path errored loudly **by accident** (no arm matched, indistinguishable from a
> typo — the SENTINEL produced a byte-identical diagnostic). It is now
> deliberate, with a diagnostic that names the actual fault.
>
> **ENCODING (this is the trap that made the original P0 plausible).** There is
> **no `VAL_ENUM`** in this interpreter — kinds stop at `VAL_THUNK`. An
> Option/Result is either **BOXED** (a `VAL_STRUCT` with `__tag` text at field
> 0 and payload at field 1) or **FLAT** (the raw payload word itself, with
> `nil` meaning `None`; see `match_enum_variant_pattern`, `eval.spl:912-921`).
> Crucially the struct **NAME is not a usable discriminator**: the two
> producers disagree. `eval_enum_variant_call` names it `"Option::Some"` /
> `"Result::Ok"` (`Type::Variant`), while `eval_text_method`'s `parse_int` arm
> names it plain `"Option"`. Measured: `"1234".parse_int()` =>
> `struct name='Option' __tag='Some'`. Only `__tag` is reliable, which is what
> `val_is_boxed_enum` (`eval.spl:857-864`) keys on. The fix discriminates on
> `__tag` and handles both encodings.
>
> Also measured: bare `Some(42)` / `Ok(42)` are **not constructible** through
> `core_interpret_expr` (`undefined function: Some`) — the bare-identifier call
> path has no Option/Result special case, so only `Enum.Variant(..)` with a
> registered enum table reaches `eval_enum_variant_call`. Unrelated to this
> fix; noted so the next lane does not mistake it for one.
>
> **Fix:** `is_option_result_method` / `option_result_tag` /
> `option_result_payload` / `eval_option_result_method` in
> `_EvalOps/call_method_eval.spl`, gated **before** the per-kind dispatch
> (a flat `Some(text)` would otherwise be swallowed by `eval_text_method`), and
> skipped for a non-enum `VAL_STRUCT` so a user-defined `Type__unwrap` still
> wins. Exported from `interpreter/__init__.spl` — that file uses **explicit
> export lists**, so a new helper is invisible to importers until listed.
> Regression pin: `test/01_unit/compiler/interpreter/option_result_method_dispatch_spec.spl`
> (7 examples), proven falsifiable by sabotage: replacing the
> `eval_set_error("called unwrap on None")` branch with a silent
> `return val_make_nil()` turns the "FAILS LOUDLY" example red **and** flips
> `"abc".parse_int().unwrap()` from the diagnostic to a silent `kind=nil`.
> Restored, 7/7 green.
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

## PARTIAL — re-verified 2026-08-17 (P2 triage, compiler lane)

Umbrella doc, re-checked at HEAD 2026-08-17. Of 31 `**P**`-tagged items: 1
REFUTED-then-FIXED (the P0 Result/Option payload index, now `[__tag,__payload]`
at `src/compiler/10.frontend/core/interpreter/eval_access.spl:482-504`), 1 marked
"PARTLY NOW-WRONG", 5 still `real=?` (never verified), 1 `real=False`, and the
remaining ~23 carry no fix annotation. The Type system, HIR, backends/regalloc,
AOP, loader, tooling and test-runner sections carry no fixed markers at all.

This doc is not actionable as a single P2 row and should not be closed as one:
it is an inventory whose items belong in separate records. Recommend splitting
the 5 `real=?` items into individually reproducible records and retiring the
umbrella. NOT FIXED by this lane.
