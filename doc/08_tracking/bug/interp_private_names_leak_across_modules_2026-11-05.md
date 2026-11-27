# Seed interpreter leaks private (non-pub) names across modules

- **Status:** OPEN (root-caused, fix not landed). P2.
- **Found:** tree_wipe follow-up work (family I4).
- **Layer:** Rust seed interpreter, `src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs` `register_definitions`.

## Repro (bin/simple.exe run, seed 2026-11-05)
`app/sub/lib_mod.spl`:
```
fn secret_helper() -> i64:
    42
pub fn open_api() -> i64:
    secret_helper()
```
`app/main3.spl`: `use app.sub.lib_mod.{secret_helper}` then `print secret_helper()`
-> prints `42`, no diagnostic. Glob `use app.lib_mod.*` likewise exposes it.
Language rule (syntax_quick_reference "Visibility"): bare `fn` is private to
its file; only same-path sibling access is in warn-only compatibility mode.

## Root cause
`register_definitions` inserts every `Node::Function` into the process-wide
`global_functions` table and `FUNCTION_OVERLOADS` with no `f.visibility` check,
and named/glob import binding never consults visibility. Any loaded module's
private fn is therefore callable from anywhere. This also hides the native
failure class in `glob_imported_private_fn_lowers_to_unmangled_extern_2026-09-13`.

## Why not fixed in this PR
Closing it means changing the seed's global function registry, which the whole
interpreter tier (and src/lib, ~75k non-pub fns) currently resolves through. A
hard error risks every seed-run spec and the bootstrap; it needs a census first.

## Next step
1. Warn-first: on an explicit `use m.{name}` / glob bind where `m` defines
   `name` as non-pub and does not `export` it, emit one warning per (importer,
   name) unless importer is a same-directory sibling; Rust unit test in
   `interpreter_module`. 2. Census warnings over `bin/simple test` corpus.
3. Flip to error once the census is zero; drop private fns from
   `global_functions` keyed lookups for non-owner modules.

## 2026-11-06 skipped (not attempted)
Needs the warn-first census over the stdlib (~75k non-pub fns) described above; too large for a minimal seed change.

## 2026-11-06 partial: warn-first step 1 landed (work/interp-p2-seed)
`module_loader.rs`: a braced `use m.{name}` naming a top-level private `fn` of `m` (not
re-exported) from a file outside `m`'s directory now prints one
`[visibility-warning] ... private fn ...` per (module, name, importer). Calls still resolve
(no behaviour change). Unit: `module_loader::private_fn_visibility_tests`. Remaining: glob
imports, the census (step 2) and the flip to error (step 3).

## 2026-11-09 call-time gate (work/interp-private-leak)
Status: fix-implemented-verification-pending. `interpreter_call/mod.rs gate_private_call` (P4-overload and P5-flat)
calls `interpreter_module::check_private_call_visibility`: a call that resolves to a private, non-exported top-level
`fn` of module M from a caller in a DIFFERENT directory is a hard error unless the (M|name) pair is in
`scripts/check/private_import_baseline.txt`. This covers glob imports and no-import leaks. Same-directory siblings
and the owner itself are unaffected. Limitation: entry-script callers (`<entry>`, directory unknown) are exempt;
braced imports from the entry are still rejected at import time. Red/green: `private_fn_call_visibility_spec.spl`
(pre-fix seed 1 failed; fixed seed 3/3) and Rust `private_call_visibility_tests` 2/2. Sample of 60 specs under
test/01_unit/{lib,common,compiler/95.interp,app}: zero new visibility errors. Not covered: the pre-existing
`private_fn_import_visibility_spec` fails on both seeds (`{{` fixture escape), unrelated to this change.
Item 4 (self-hosted compiler check) filed as interp_private_names_selfhost_check_2026-11-09.
Baseline census (20181 pairs / 3589 modules): src/lib/nogc_sync_mut 5578, src/lib/common 2624, src/app/llm_caret 1463,
src/os/kernel 1147, src/lib/gc_async_mut 857, src/lib/nogc_async_mut 818, src/app/office 522, src/os/crypto 385,
src/app/devhub 347, src/compiler/10.frontend 313.

## 2026-11-12 self-hosted check landed STAGED (work/bug-privnames-20261112, interp_private_names_selfhost_check_2026-11-09)
Status: fix-implemented, hard default BLOCKED by census. `HirLowering.private_fn_import_denied`
(`src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl`, called from the braced-item branch of
`resolve_import_list`) mirrors the seed's `check_private_use_names`: braced group only (a dotted `use m.x as y` is
`ImportTarget::Aliased` in the seed, not checked), bare `fn` (`Visibility.Private`, not method/extern), importer
directory != target directory, target module not opaque (any plain `export` list or glob re-export skips it, as
`module_surface_is_opaque` does), `rel|name` not in `scripts/check/private_import_baseline.txt` at the first `.git`
ancestor of the target (baselined => the seed's `[visibility-warning]`, recorded). Baseline is read once per process
into a hash-chain table (module-level vars, BOOT-20: no Dict). Non-baselined pair: recorded warning
`[W-HIR-PRIVATE-IMPORT-001]` by default, hard error `[E-HIR-PRIVATE-IMPORT-001]` under
`SIMPLE_STRICT_PRIVATE_IMPORTS=1` (same staging as W-HIR-UNDECL-IMPORT-001). Spec:
`test/01_unit/compiler/hir/private_fn_import_cross_module_visibility_spec.spl` (pristine resolver 3/7, fixed 7/7;
run WITHOUT SIMPLE_BOOTSTRAP=1 -- that env skips import resolution in module_build.spl).

**Why not a hard default.** Textual census (same predicate, module->file resolution of std/compiler/app/relative
paths) over the transitive `use` closure of `src/app/cli/bootstrap_main.spl` (1372 files) found 75 non-baselined
cross-directory braced private imports and over `src/app/cli/main.spl` (2385 files) 93; 49 distinct `target|name`
pairs, listed below. Stage 2 lowers every closure module through `resolve_import_list`, so a hard default would stop
the bootstrap on the first. 5 of the 49 names have several definitions in the tree (`is_digit` x11, `find_c_compiler`
x3, `_get_temp_dir` x3, `bug_database_from_sdn` x2, `check_formatting` x2), so promoting them to `pub` interacts with the
co-compiled-public-definition resolution rule and is a separate reviewed change.

**Seed caveat (measured on the pinned seed 4449288fc577).** `simple run src/app/cli/bootstrap_main.spl --version`
prints 1308 `[visibility-warning]` lines and 0 errors although its own predicate matches the 75 sites above: the seed
reaches only the modules that run actually loads. From an entry outside `src/` (`privprobe/*.spl`, in-repo) the
import-time check emitted nothing at all, not even for a baselined pair, and the bug doc repro printed 42. The
self-hosted check is therefore stricter in reach than the seed in practice; parity is with the seed's rule, not its reach.

**Flip worklist (49 pairs, make `pub` or `export`, then flip the default and delete the toggle) -- DONE 2026-11-12, see the section below:**
- `src/app/office/sheets/cell_ref.spl|expand_range_refs`
- `src/app/test_runner_new/json_wrapper.spl|run_test_json_wrapper`
- `src/app/test_runner_new/json_wrapper.spl|test_json_requested`
- `src/app/test_runner_new/json_wrapper.spl|test_json_worker_requested`
- `src/compiler/10.frontend/core/ast_types.spl|make_core_decl`
- `src/compiler/10.frontend/core/cfg_platform.spl|cfg_eval_key_value`
- `src/compiler/10.frontend/core/cfg_platform.spl|cfg_normalize_arch`
- `src/compiler/10.frontend/core/cfg_platform.spl|cfg_normalize_os`
- `src/compiler/10.frontend/core/cfg_platform.spl|cfg_os_is_unix`
- `src/compiler/10.frontend/core/cfg_platform.spl|cfg_strip_quotes`
- `src/compiler/10.frontend/core/lexer_chars.spl|is_digit`
- `src/compiler/10.frontend/core/parser_cli.spl|parse_cli_decl`
- `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl|get_eligible_rules_for_function`
- `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl|optimization_backend_kind_from_text`
- `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl|optimization_backend_kind_name`
- `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl|optimization_backend_policy_all`
- `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl|optimization_provider_stats_record_scope`
- `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl|optimization_provider_stats_zero`
- `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl|optimization_rule_provider_applies_to_backend_name`
- `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl|optimization_rule_provider_builtin_with_contract`
- `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl|optimization_rule_provider_is_pipeline_pass`
- `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl|optimization_rule_provider_missing_fact`
- `src/compiler/60.mir_opt/mir_opt/pattern/rules_clib_parity.spl|clib_parity_rule_table`
- `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl|ssa_alloca_transform_blocks`
- `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl|ssa_var_transform_blocks`
- `src/compiler/70.backend/backend/backend_helpers.spl|backend_helper_target_opt_context`
- `src/compiler/70.backend/backend/backend_helpers.spl|compile_llvm_module_to_object_path`
- `src/compiler/70.backend/backend/backend_helpers.spl|compile_module_with_backend`
- `src/compiler/70.backend/backend/backend_helpers.spl|compile_module_with_backend_scoped_v1`
- `src/compiler/70.backend/backend/backend_helpers.spl|get_effective_backend_name`
- `src/compiler/70.backend/backend/cmake_gen.spl|generate_cmake_for_modules`
- `src/compiler/70.backend/backend/io_compat.spl|backend_shell_tuple`
- `src/compiler/70.backend/backend/io_compat.spl|backend_tool_on_path`
- `src/compiler/70.backend/backend/llvm_ir_builder.spl|is_float_type`
- `src/compiler/70.backend/backend/llvm_ir_builder.spl|is_integer_type`
- `src/compiler/70.backend/backend/llvm_ir_builder.spl|is_signed_int_type`
- `src/compiler/70.backend/backend/llvm_ir_builder.spl|natural_alignment`
- `src/compiler/70.backend/backend/mir_target_context_provider.spl|backend_mir_target_context`
- `src/compiler/70.backend/backend/runtime_compiler.spl|find_c_compiler`
- `src/compiler/70.backend/backend/runtime_compiler.spl|_get_temp_dir`
- `src/compiler/70.backend/backend/runtime_compiler.spl|_is_msvc_cc`
- `src/compiler/90.tools/formatter/main.spl|check_formatting`
- `src/compiler/90.tools/formatter/main.spl|format_file_inplace`
- `src/compiler/90.tools/formatter/main.spl|print_diff`
- `src/compiler/99.loader/loader/module_loader_semantic.spl|_semantic_cache_is_fresh_from_maps`
- `src/compiler/99.loader/loader/module_loader_semantic.spl|_semantic_dependents_from_paths`
- `src/compiler/99.loader/loader/module_loader_semantic.spl|_semantic_fingerprint_dependents_from_paths`
- `src/compiler/99.loader/loader/module_loader_semantic.spl|text_array_push_unique`
- `src/lib/nogc_async_mut/database/bug.spl|bug_database_from_sdn`

## 2026-11-12 default FLIPPED: 49 pairs promoted to `pub`, toggle deleted (work/bug-privnames2-20261112)

Status: fixed. All 49 worklist pairs above were promoted mechanically (`fn NAME(` -> `pub fn NAME(`, one line
each, 18 files, no refactor or rename). `HirLowering.private_fn_import_denied` now emits the hard error
`[E-HIR-PRIVATE-IMPORT-001]` for every non-baselined cross-directory braced private-fn import; the recorded
`W-HIR-PRIVATE-IMPORT-001` warning and the `SIMPLE_STRICT_PRIVATE_IMPORTS` toggle are gone. Baselined pairs
(`scripts/check/private_import_baseline.txt`, 20,133 rows, NOT grown by this change) stay the seed's recorded
`[visibility-warning]`.

**Duplicate-definition names (5 of 49).** Each worklist pair names the *target file*, so the import's resolution
is already fixed by the pair: `is_digit` -> `src/compiler/10.frontend/core/lexer_chars.spl` (the other 10
`is_digit` definitions in the tree stay private), `find_c_compiler` and `_get_temp_dir` ->
`src/compiler/70.backend/backend/runtime_compiler.spl`, `bug_database_from_sdn` ->
`src/lib/nogc_async_mut/database/bug.spl`, `check_formatting` -> `src/compiler/90.tools/formatter/main.spl`.
Every target file holds exactly one bare `fn NAME` and no `pub fn NAME` twin or `export` list (verified for all
49). The 2026-11-12 concern that promotion "interacts with the co-compiled-public-definition resolution rule" does
not hold: the seed's flatten collision table (`hir/lower/lowerer.rs`, `flatten_fn_owners`) is built from every
`Node::Function` regardless of `pub`, and the module_loader "public function ... co-compiled definitions" warning
labels by name shape (`_` prefix = "private helper"), not by the keyword -- both are visibility-blind, so `pub` is
neutral to collision resolution. The self-hosted resolver's one visibility-sensitive rule (a private callable
reached through a glob never displaces an existing binding, `module_import_resolution.spl`) is not reached: no
file in `src/` glob-imports any of the 18 promoted modules (textual census; the `mir_opt` `__init__.spl` facades
re-export `rule_engine` / `rules_clib_parity` / `var_reassign_ssa` names selectively, which the promotion makes
legal).

**Safety gate (textual census, same scripts as 2026-11-12 above, re-run on this branch).** Stage 2 closure
(`src/app/cli/bootstrap_main.spl`, 1377 files): offenders 75 -> **0**, baselined 1033, 24 unresolved modules.
Full-CLI closure (`src/app/cli/main.spl` + `_CliMain/main_and_help.spl`, 2390 files): offenders 93 -> **0**,
baselined 2212, 111 unresolved modules (the unresolved residue is unchanged from the previous census and consists
of modules the textual resolver cannot map to a file; it is the same residue that existed when the 49 were
counted). Real-resolver probe: temporary single-case specs (not committed) lowered four formerly-offending importers
(`60.mir_opt/general_patterns.spl` vs `pattern/rule_engine.spl`, `99.loader/module_loader_compat.spl` vs
`loader/module_loader_semantic.spl`, `app/cli/_CliMain/main_and_help.spl` vs `test_runner_new/json_wrapper.spl`,
`app/io/cli_lint_commands.spl` vs `90.tools/formatter/main.spl`) against their real target files through
`parse_full_frontend` + `HirLowering.lower_module` (seed harness, no SIMPLE_BOOTSTRAP): 0 `E-HIR-PRIVATE-IMPORT-001`
in all four (unrelated diagnostics from the absent other imports were ignored; one baselined `[visibility-warning]`
still recorded where expected). Negative control: the same `general_patterns.spl` probe fed the pristine
(pre-promotion) `rule_engine.spl` content raised exactly 5 `E-HIR-PRIVATE-IMPORT-001`, naming the 5 promoted
`optimization_*` names, so the probe exercises the rule. The two largest importers (`_MirToLlvm/core_codegen.spl`,
`driver_aot_native_output.spl`, 3.7k/4.7k lines) were dropped from the probe: the seed-interpreted frontend did not
finish them within 20 min; the textual census covers them.

Spec `test/01_unit/compiler/hir/private_fn_import_cross_module_visibility_spec.spl`: rewritten so the default case
expects the hard error and no toggle exists; against the staged resolver 4/6 (the two hard-error cases red), after
the flip 6/6.

**Parity notes recorded with the flip (2026-11-12).** (1) The seed's import-time `check_private_use_names` has
NO `test/**` exemption -- `is_test_caller` belongs only to the seed's call-time gate
(`check_private_call_visibility`, module_loader.rs:2810). Measured: the pinned seed already hard-errors today on
`test/01_unit/compiler/mir_opt/clib_parity_hotspot_spec.spl` and
`test/01_unit/compiler_core/interpreter/registry_scoping_real_spec.spl` (`error: semantic: private fn ... is not
visible`), so the self-hosted import-time check deliberately carries no test exemption either. (2) Whole-tree
textual residue outside the two closures (same census over `src/` + `test/`): 130 further `target|name` pairs with
`src/` importers (283 import rows) and 661 pairs with `test/` importers (1110 rows). These are the seed's existing
hard errors wherever the seed reaches them (see (1)); the flip adds no new failure class, it only matches the seed's
reach to the self-hosted compiler's. Fixing them is ordinary `pub` promotion work per file, not a toggle question.
(3) The 21 other specs that use `module_surfaces_from_test_modules` were run with the seed on this branch and on
the base commit `a36cf62afc8`: 12 pass on both; 9 fail with identical `Results:` lines on both (none mentions
`PRIVATE-IMPORT`), so the flip changes no sibling spec outcome.
