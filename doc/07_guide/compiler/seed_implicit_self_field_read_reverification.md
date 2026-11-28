# Seed re-verification: implicit `self` field read in plain `fn` methods

Recipe for re-checking the seed fix for
`doc/08_tracking/bug/implicit_self_field_read_unresolved_in_plain_fn_method_2026-09-03.md`
after the next Rust seed rebuild + `bin/simple.exe` refresh. Do not edit the
bug record; run this recipe and append the outcome as a new lane addendum
elsewhere if a lane owns one.

## What was fixed

Two seed frontend layers, mirroring the pure-Simple frontend semantics
(`src/compiler/10.frontend/core/parser_decls_use.spl` is the reference):

1. `src/compiler_rust/parser/src/types_def/mod.rs` (`parse_class_body`):
   a plain `fn` method in a class body with no explicit `self`/`me` parameter
   and a non-constructor name now gets a synthesized immutable `self`
   parameter (instance method) instead of being marked `is_static`.
   Constructor-named factories (`new`/`create`/`default`/`from_*`, per
   `trait_impl_parsing::is_constructor_name`) stay static, and the
   FlatPoolReader calling-convention fix for `Type.new(args)` is preserved.
   This matches the pure-Simple rule
   (`method_name_is_implicitly_static` + synthesized `self`).
2. `src/compiler_rust/compiler/src/mir/lower/receiver_field_rewrite.rs`
   (driven from `MirLowerer::lower_function` in `lowering_core.rs`, before any
   per-function analysis): scans a method body for `Global(name)` exprs that
   resolve to no module-level symbol (`global_types` / `available_functions`
   / `function_value_globals` / `imported_function_names` all miss) but match
   a field of the receiver type (param local 0, `self`/`me`), and rewrites
   them into ordinary, CONCRETELY typed `self.<field>` `HirExpr`s (cloning
   the `HirFunction` only when a candidate exists). Re-typing matters: the
   unresolved `Global` arrives typed ANY, and ANY-typed operands take runtime
   tag-dispatched paths (`rt_any_add`, boxed equality) that misinterpret the
   raw field word. A residual net in
   `mir/lower/lowering_expr_ident.rs::lower_implicit_receiver_field` catches
   the same shape at lowering time for expressions outside the walked body
   (e.g. contract clauses). Both parts are needed: (1) makes the receiver
   exist, (2) resolves the bare name against it with the field's declared
   type. Scope: every MIR lane (Cranelift JIT, LLVM, MIR interpreter).

The tree-walking interpreter fallback lane is a separate component; if a
bare read still fails when the run is forced to the interpreter
(`SIMPLE_EXECUTION_MODE=interpreter`), that lane has its own fix/record.
Note the parser change (1) also changes the AST the interpreter consumes;
previously-static plain `fn` class methods now declare `self`, so the
interpreter's method-call arity handling must key off the declared
signature (params[0] == "self"), as `import_loader.rs`/`module_pass.rs`
already do for the compiled lanes.

## Rebuild the seed (after the fix is in the tree)

```sh
cd src/compiler_rust
CC="$HOME/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64/bin/clang.exe" \
  CARGO_TARGET_DIR=$PWD/../build/p3cache/impself/cargo-target \
  cargo build --release -p simple-driver
# artifact: src/build/p3cache/impself/cargo-target/release/simple.exe
```

Do not overwrite `build/p3cache/fresh-seed/simple.exe` from a lane scratch
build; the seed deploy flow (`scripts/bootstrap/`) owns that copy.

## Checks (in order)

1. Doc repro prints `code=4` and exits 0 on the default JIT lane:

   ```sh
   SIMPLE_HIR_CACHE_DIR=$PWD/build/p3cache/impself/hir-cache \
   TMPDIR=$PWD/build/p3cache/impself/tmp \
   <scratch-simple.exe> run build/p3cache/impself/repro_kind.spl
   echo "exit=$?"   # expect: code=4 / exit=0
   ```

   (Repro source is the 12-line program in the bug record; a copy lives at
   `build/p3cache/impself/repro_kind.spl` on the fixing lane.)

2. Regression spec (RED on the pre-fix seed, GREEN after):

   ```sh
   SIMPLE_BINARY=<scratch-or-deployed-simple.exe> \
   <simple.exe> test test/01_unit/language/implicit_self_field_read_plain_fn_jit_spec.spl
   # expect: 4 examples, 0 failures
   ```

3. Acceptance suite stays green (no regression from the fix):

   ```sh
   <simple.exe> test test/01_unit/app/devhub/itf_config_spec.spl
   # expect: 32 total, 32 passed
   ```

4. Fail-closed guard stays intact: an unknown bare name inside a method must
   still exit non-zero (case 4 of the regression spec covers this; the
   generic contract is `test/01_unit/app/cli/run_semantic_error_exit_code_spec.spl`).

## Evidence recorded by the fixing lane (2026-11-27, lane p3-sweep4)

- Baseline (pre-fix scratch seed): repro → `GlobalLoad: unresolved identifier
  'kind'`, interpreter fallback `variable 'kind' not found`, exit 1.
- Baseline spec: 3 of 4 examples fail (guard case passes) — RED.
- Post-fix scratch seed: repro → `code=4`, exit 0; regression spec 4/4;
  `itf_config_spec.spl` 32/32.
