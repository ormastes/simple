# Pure-Simple bootstrap nil lowering fixes and remaining worker repro

Date: 2026-07-07
Status: fixed-in-main-with-follow-up
Severity: P1 bootstrap stability
Fixed commit: `0e0214f24aca` (`fix: stabilize pure Simple bootstrap`)

## Log/error-reporting follow-up (2026-07-07)

Implemented after reviewing the debugging loop:

- Rust seed interpreter field-access diagnostics now share the cached
  `field_access_debug_enabled()` gate. It is enabled by
  `SIMPLE_DEBUG_FIELD_ACCESS=1` or `SIMPLE_BOOTSTRAP_DIAG=1` before process
  start, so normal runs avoid repeated environment lookups and call-stack
  collection.
- Rust field-access failures now include the opt-in hint in the detailed
  `[field-access-error]` line.
- Pure-Simple driver MIR lowering now reports missing HIR at the driver
  boundary, e.g. `MIR lowering missing HIR module for <module> (<path>)`,
  instead of continuing until a later nil `.symbols` field access.
- Pure-Simple HIR/MIR bootstrap probes now include module, path, function count,
  function name, and source index where relevant.
- New HIR/MIR bootstrap diagnostic logs are gated by
  `SIMPLE_BOOTSTRAP_DIAG=1`, `SIMPLE_COMPILER_TRACE=1`, or
  `SIMPLE_COMPILER_PHASE_PROFILE=1`; with these unset the added log paths do
  not emit. Driver phase timing keeps its existing
  `SIMPLE_COMPILER_TRACE=1` / `SIMPLE_COMPILER_PHASE_PROFILE=1` gate to avoid
  regressing the deployed checker on this bootstrap lane.

Verification item:

```sh
bin/release/simple test test/01_unit/compiler/mir/mir_lowering_new_spec.spl --mode=interpreter
```

Current verification blocker:

```text
bin/release/simple check src/compiler/80.driver/driver_log_helpers.spl
Checking src/compiler/80.driver/driver_log_helpers.spl...
exit 139

bin/release/simple check test/01_unit/compiler/mir/mir_lowering_new_spec.spl
Checking test/01_unit/compiler/mir/mir_lowering_new_spec.spl...
exit 139
```

The driver log helper has no remaining source diff, so the first crash is not
caused by the new error-reporting branch. Until the deployed pure-Simple
runtime is repaired or redeployed, use the source assertions in
`test/01_unit/compiler/mir/mir_lowering_new_spec.spl` plus Rust
`cargo check -p simple-compiler` as partial evidence only.

Follow-up root cause found during redeploy:

```text
Program received signal SIGSEGV, Segmentation fault.
__strlen_avx2
__add_to_environ(... value=0x1b ...)
rt_env_set
frontend__core___AstExpr__nodes__expr_count_set
```

The checked-in source already converts `SIMPLE_BOOTSTRAP_EXPR_COUNT` through
`int_to_str(value)`, so the deployed binary was stale. Redeploy then exposed a
bootstrap parser blocker: named tuple return types such as
`-> (stdout: text, stderr: text, exit_code: i64)` in compiler sources stop the
Stage 4 parser. The fix request now includes keeping bootstrap compiler-source
tuple returns positional, e.g. `-> (text, text, i64)`, with
`test/01_unit/compiler/frontend/parser_spec.spl` guarding the high-risk paths.

## Fixed errors

The 2026-07-07 bootstrap repair loop fixed several independent failures that
were hiding behind each other:

- `scripts/setup/setup-gui-web-2d-vulkan-env.shs` accepted an executable but
  crashing explicit `SIMPLE_BIN`/`SIMPLE_BINARY`. `bin/simple_native --version`
  exited `139`; the setup path now probes startup and reports
  `startup-failed-<code>` instead of treating a stale binary as valid.
- `src/app/cli/native_build_main.spl` resolved worker binaries to absolute
  paths and stopped forwarding `--mode=interpreter` as a native-build option.
  Interpreter execution is selected through `SIMPLE_EXECUTION_MODE=interpret`.
- `src/compiler/10.frontend/core/parser.spl` now returns lexer token text for
  string/label token kinds instead of reconstructing decoded string literals
  from raw source offsets.
- MIR lowering no longer lets nil HIR type metadata reach `.kind` reads:
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`,
  `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`, and
  `src/compiler/50.mir/mir_lowering_stmts.spl` use explicit nil guards instead
  of fragile optional presence checks or nil coalescing in bootstrap-sensitive
  paths.

## Bootstrap evidence

Main cached pure-Simple build:

```text
Build complete: 56 compiled, 1119 cached, 0 failed
```

Mini-build evidence from the same loop:

```text
bootstrap_main: produced build/mini_builds/full_bootstrap_main/bootstrap_main
native_build_main: Build complete: 635 compiled, 0 cached, 0 failed
mcp_main: Build complete: 205 compiled, 0 cached, 0 failed
```

Smoke:

```text
bin/release/simple --version
Simple v1.0.0-beta
```

## Tests and guards

- `bin/release/simple check` passed for the touched compiler, parser,
  native-build, and focused spec files.
- `test/01_unit/compiler/mir/mir_lowering_new_spec.spl` passed with 14
  scenarios and pins the bootstrap nil guards.
- `test/01_unit/app/cli_native_build_main_contract_spec.spl`,
  `test/01_unit/compiler/driver/native_build_jit_ambiguity_source_spec.spl`,
  and `test/01_unit/compiler/frontend/parser_spec.spl` covered the CLI/parser
  fixes during the repair loop.
- `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` passed.
- `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.

## Remaining fix request

The following synthetic worker repro still needs cleanup if that invocation
shape is considered supported:

```sh
env SIMPLE_BOOTSTRAP=1 SIMPLE_LIB=src \
  SIMPLE_NATIVE_BUILD_FORCE_WORKER=1 \
  bin/release/simple run src/app/cli/native_build_main.spl -- \
  --backend cranelift \
  --source src/compiler --source src/app --source src/lib \
  --entry build/mini_builds/agent_replace_probe/min_while_const.spl \
  --entry-closure \
  --cache-dir build/mini_cache_agent_replace_probe_src \
  -o build/mini_builds/agent_replace_probe/min_while_const.worker
```

Observed follow-up error:

```text
[hir-lower] functions:count 0
[hir-lower] bootstrap-functions:count 0
[DEBUG FIELD ACCESS] Trying to access field 'symbols' on value type: "nil"
error: semantic: undefined field 'symbols': cannot access field on value of type 'nil'
```

Direct `native-build` of the same minimizer succeeds, so this is not blocking
the verified bootstrap path. The likely fix is to make the `simple run
src/app/cli/native_build_main.spl -- ...` worker path either reject external
entries under `SIMPLE_BOOTSTRAP=1` with a clear diagnostic, or route them
through the normal non-bootstrap HIR module path instead of returning an empty
bootstrap HIR module.

## 2026-07-07 follow-up: native declaration collision crash

Later cache-backed mini builds reproduced a separate stage4 native crash after
the parser blockers were removed. CLI, MCP, and LSP shards all converged on
Cranelift `IncompatibleDeclaration` warnings for constructor-looking names that
were already declared as data/type symbols:

- `Backend`
- `Codegen`
- `Symbol`

Root cause: unresolved constructor calls can reach cross-module call codegen,
where bare type names are treated as importable functions. The old path logged a
warning and injected nil, allowing object creation/use to continue until a
segfault. The repair now:

- renames backend concrete constructors to `CompilerBackend` and
  `CraneliftCodegenState`, with compatibility aliases `type Backend = ...` and
  `type Codegen = ...`;
- renames the HIR concrete symbol-table record to `HirSymbol`, with
  `type Symbol = HirSymbol`;
- makes Rust call codegen fail closed when a call target resolves to an existing
  data/type declaration instead of synthesizing nil;
- adds `test/01_unit/compiler/backend/backend_declaration_name_collision_spec.spl`
  to prevent reintroducing short `Backend`, `Codegen`, or HIR `Symbol`
  constructors.

## 2026-07-13 follow-up: optional presence emits unsafe nil equality

Status: open, blocks SimpleOS filesystem compiler LLVM emission.

The stage2/Cranelift target lowering of `if value.?` first calls `rt_is_some`,
then emits a fallback `rt_native_eq(value, nil)` on the false path. For an
absent `MirOperand?`, the fallback reaches `rt_native_eq+0xe1` and dereferences
an invalid decoded heap address (`CR2=0x183f6f18`) in ring 3. A direct
`match value: Some(...) / nil` emits the same unsafe equality.

Reproducer owner:

```text
src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl
MirToLlvm.translate_terminator -> Ret(value: MirOperand?)
```

Required fix: optional presence lowering must trust the boolean result of
`rt_is_some`/`rt_is_none` and must not append generic native equality against
nil. Add a focused generated-code regression proving the absent path contains
the predicate call and branch but no `rt_native_eq`. Do not work around the
compiler bug with a new backend-local raw runtime extern.

Live evidence: target ELF SHA-256
`38dab594f3d82f2745e6d30765fee49468012a7d5c56d855a2a7b5a096da1355`,
image SHA-256
`7e18aa0d8f6518c0bef9ec62aab6376d45f22fa6c52e0836dce459acd0bb544b`,
fault RIP `0x556589` (`rt_native_eq+0xe1`).

Owner follow-up evidence: Rust `lower_exists_check` now emits a direct
`rt_is_some` builtin, its focused HIR regression passes, and an isolated full
bootstrap rebuilt stage2/stage3 successfully. Nevertheless, the rebuilt
SimpleOS compiler still contains a false-path `rt_native_eq(value, nil)` after
the `rt_is_some` call in `translate_terminator` and faults at RIP `0x103543b9`.
The remaining owner is downstream native codegen/truthiness handling, not the
HIR existence rewrite. Map that exact fallback before another edit.
