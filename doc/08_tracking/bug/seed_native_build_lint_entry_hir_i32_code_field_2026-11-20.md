# Seed native-build of the lint entry fails: HIR "Cannot infer field type: struct 'i32' field 'code'"
- Status: fixed (2026-11-22)
- Severity: P3 (seed is bootstrap-only; pure-Simple lint is unaffected)
- Found: 2026-11-20, ubuntu-p2 WSL2
- Component: Rust seed compiler HIR type inference (`src/compiler_rust/`), compiling `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`

## Observation
`SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_BOOTSTRAP=1 ~/ssos-seed-target/release/simple native-build --target x86_64-unknown-linux-gnu --source src/compositions/kernel_llvm_cranelift --source src --entry-closure --entry src/app/cli/lint_entry.spl --mode dynload`
ends `[native-build] compiled=718 reused=0 failed=1` with
`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl: hir: Cannot infer field type: struct 'i32' field 'code'`.
Owner rule: seed semantics must match pure Simple; pure Simple accepts this file.

## Evidence (verified by reading source at origin/release/1.0.0)
- The file has ~50 `.code` accesses on `warning`/`finding`/`lint` receivers
  (e.g. `entry_and_fixes.spl:134,271,273,283,367,434-518,948,1006`); their types are
  `text`-coded structs (`AnyRuleFinding.code: text`, `any_rules.spl:40-44`), none is i32.
- The only i32-adjacent value near these is the tuple destructure at `entry_and_fixes.spl:255`
  (`val (_any_stdout, _any_stderr, any_code) = _cli_process_run(...)`; declared `-> (text, text, i64)`,
  `src/app/io/cli_ops.spl:343`) directly before `for finding in any_relay.findings` (:269) and
  `finding.code` (:271, :273). Suspected: seed mis-types a loop/tuple binding as i32.
- NOT bisected: which exact `.code` site the seed fails on is unconfirmed (no seed in this worktree).

## Root Cause & Resolution (2026-11-22)
- **Exact site:** `entry_and_fixes.spl:421` (`val option_me_warnings = if not run_opt_me:\n    []\nelif (linter.last_resolved_path == path and linter.last_source_locations_valid):\n    linter.last_option_me_warnings\nelse:\n    check_option_me_call_source(path, content)`) iterated at `:512` (`for warning in option_me_warnings:` -> `warning.code` at `:514`).
- **Why `i32`:** `Lowerer::lower_array` gives an empty array literal `[]` the configured default element type `TypeId::I32`. `Lowerer::lower_if` (`src/compiler_rust/compiler/src/hir/lower/expr/control.rs`) only recognized inline `Expr::Array([])` branches and concrete `HirType::Array` siblings, missing both multiline `Expr::DoBlock([Node::Expression(Expr::Array([]))])` branches and `elif` chains whose sibling lowered to `TypeId::ANY` across modules — leaving `option_me_warnings` typed `[i32]` and `warning` typed `i32`.
- **Fix:** Taught `lower_if` (`expr_is_empty_array_literal` + `retype_empty_array_branch` in `control.rs`) to unwrap `DoBlock` empty-array tails and contextualize empty-array branches against both `HirType::Array` and `ANY` siblings. Added regression tests `multiline_if_elif_empty_array_never_narrows_struct_or_any_elements_to_i32` (`conditional_empty_array_tests.rs`) and `lint_entry_closure_lowers_entry_and_fixes_without_i32_code_field_error` (`native_project/discovery.rs`).
