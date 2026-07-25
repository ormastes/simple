# #138 self-host remaining-work audit (read-only, 2026-07-12)

## 1. `rt_native_build` references (src/compiler + src/app, excl. compiler_rust/vendor)

Real caller (extern decl + 3 call sites) — the ONLY place that actually invokes the Rust seed symbol:
- `src/app/cli/bootstrap_main.spl:2` — `extern fn rt_native_build(args: [text]) -> i64` (declaration)
- `src/app/cli/bootstrap_main.spl:108` — `return rt_native_build(args)` (call, explicit --entry path)
- `src/app/cli/bootstrap_main.spl:111` — `return rt_native_build(args)` (call, no single-.spl-positional detected)
- `src/app/cli/bootstrap_main.spl:120` — `rt_native_build(forwarded)` (call, forwarded --entry/--entry-closure)
- `src/app/cli/bootstrap_main.spl:73` — comment describing rt_native_build's Rust arg parser quirk

Everywhere else is compiler-internal plumbing that exists ONLY to let the self-hosted compiler compile `bootstrap_main.spl` itself (recognize the literal name as a "bootstrap builtin", lower its one extern-call body, and emit a matching LLVM `declare`). None of these call the symbol; they support compiling the one file that does:
- `src/compiler/80.driver/driver_bootstrap.spl:73` — `if name == "rt_native_build":` symbol-id table entry
- `src/compiler/80.driver/driver_bootstrap.spl:78` — name listed in `bootstrap_function_names()`
- `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl:105` — reverse index→name table entry
- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:880` — reverse index→name table entry (`self.bootstrap_symbol_name`)
- `src/compiler/20.hir/hir_lowering/expressions.spl:61` — `is_bootstrap_builtin_fn` recognizes the name
- `src/compiler/20.hir/hir_lowering/_Items/lowering_helpers.spl:104` — symbol-id lookup table entry
- `src/compiler/70.backend/backend/llvm_lib_translate.spl:427` — `declare_fn(mod_, "rt_native_build", ...)` (LLVM extern declare for linking)
- `src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl:204-206` — emits `declare i64 @rt_native_build(ptr)` in bootstrap codegen path, with comment explaining why (symbol lives in `libsimple_native_all.a`)
- `src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl:241` — registers name in `defined_func_names` to avoid duplicate declares
- `src/compiler/70.backend/backend/llvm_native_link.spl:236-249` — comments explaining why the Rust `native_all` archive must stay linked when a module (bootstrap_main's extern) references `rt_native_build`

Confirms the mainline path refuses fallback:
- `src/app/io/_CliCompile/compile_targets.spl:1016` — `_cli_eprint("The Rust seed is bootstrap-only; native-build no longer falls back to rt_native_build.")` — hard error, not a fallback call.

**Verdict: `bootstrap_main.spl` is still the sole real caller of `rt_native_build`.** All other hits are either comments or dead-until-needed symbol-table/codegen scaffolding that exists solely to compile that one file's extern declaration+calls.

## 2. Other seed-FFI escape hatches

- `rt_native_all` — 0 hits in src/compiler or src/app. Not referenced (only the Rust crate `src/compiler_rust/native_all` exists, out of scope).
- `aot_native_file_with_backend` — 16 hits (driver_api.spl, driver_api_core.spl, driver_api_native_single.spl, driver_public_compile.spl, bootstrap_api.spl, build_native_pipeline.spl, `__init__.spl`, app/compile/native.spl, compile_opt_and_driver.spl). This is a **legitimate pure-Simple `compiler_driver` API**, not a seed hatch — it's part of the self-hosted driver surface used by the normal native-build path.
- `SIMPLE_BOOTSTRAP` — 93 hits across ~28 files (hir_lowering, mir lowering, mir_opt, backend/_MirToLlvm, driver.spl, driver_bootstrap.spl). All gate the same narrow "bootstrap builtin" special path (`bootstrap_lower_to_mir_context`, `bootstrap_compile_to_native_local`, `bootstrap_compile_context_to_native_local`, skip-mono/skip-mir-opt fast paths) used only when compiling `bootstrap_main.spl`. Grep for who actually **sets** `SIMPLE_BOOTSTRAP=1` shows: `scripts/bootstrap/bootstrap-from-scratch.sh:491` (seed bootstrap script — explicitly bootstrap-only per CLAUDE.md) and a large set of `scripts/os/*.shs` / `scripts/check/*.shs` SimpleOS/QEMU baremetal-build scripts (kernel/no-libc compile mode — unrelated to Rust-seed FFI, out of #138's scope). No everyday native-build invocation sets it.
- `SIMPLE_NATIVE_BUILD_FORCE_WORKER` — 1 hit, `src/app/cli/native_build_main.spl:150` — routes to a worker **subprocess** of the self-hosted compiler for isolation/timeout handling, not seed FFI.
- `SIMPLE_BOOTSTRAP_REAL_LLVM` — 4 hits: `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:98`, `src/compiler/80.driver/driver_bootstrap.spl:196` (comment), `:426`, `:439`. Gates whether the bootstrap-builtin path emits real LLVM vs. a stub; scoped to the same narrow bootstrap_main.spl path.

## 3. Blocker assessment

After bootstrap_main.spl's endgame routing lands (routing single-file compiles through `compiler_driver_create`/`compiler_driver_run_compile` instead of the seed extern):
- The `extern fn rt_native_build` declaration is removed from its only declaration site (bootstrap_main.spl:2), and its only 3 call sites go with it.
- All the "bootstrap builtin" symbol-table/codegen scaffolding listed in §1 (driver_bootstrap.spl, bootstrap_globals.spl, method_calls_literals.spl, expressions.spl, lowering_helpers.spl, llvm_lib_translate.spl, asm_constraints_helpers.spl) becomes dead code — it does not itself call the seed, so it is **not a functional blocker**, just follow-up cleanup (delete the now-unused table entries and LLVM declare-support code).
- `SIMPLE_BOOTSTRAP` / `SIMPLE_BOOTSTRAP_REAL_LLVM` become unreachable for the ordinary compile path once nothing sets them for compiling bootstrap_main.spl; their other users are the seed's own bootstrap script and SimpleOS baremetal builds, both out of #138's scope.
- No other seed-FFI surface was found in src/compiler or src/app.

**No blocker to declaring #138 done besides the bootstrap_main.spl rewrite itself** (plus optional dead-code cleanup of the bootstrap-builtin scaffolding, which can be a follow-up, not a gate).
