# Lane: stage4 / $sp_dev remake plan (ex-codex 019f9c04)
Goal: "$sp_dev remake plan; do all item tasks in parallel."
Last state: parser ambiguity in `src/compiler/70.backend/backend/vulkan_backend.spl` was patched by replacing `if ... else` expression-form branches with explicit `if ... return` blocks.
Current status: stage4 native-build now reaches parse completion; no parser errors from `vulkan_backend.spl`.
Blocking: stage4 consistently crashes with segmentation fault during phase3 hir lowering (`[hir-lower] lower_expr:kind`) after `phase3:hir_typecheck` begins, exit code 139.

Parallel execution split is now defined in
[`doc/03_plan/agent_tasks/stage4_spdev.md`](doc/03_plan/agent_tasks/stage4_spdev.md)
with Team A–D lanes and merge/final-review ownership.

Recent commands:
- Ran direct stage4 native-build command with `SIMPLE_NATIVE_BUILD_THREADS=4`; logs: `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build-current.log`; result `EXIT:139`.
- Ran same command with `SIMPLE_NATIVE_BUILD_THREADS=1` (to exclude concurrency effects); logs: `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build-threads1.log`; result `EXIT:139`.

Next: classify phase3 `hir_lower` segfault and either bisect or escalate with compiler/runtime team; do not re-run full native-build until blocker is isolated/fixed.

## 2026-08-01 Stage2/Stage3 continuation

- GDB localized the earlier SIGILL to `module_surfaces_from_modules`, where a
  staged-native `Dict<text, i64>` physical-path lookup returned the wrong
  parsed-module index. Replacing that lookup with scalar open-addressed arrays
  and retaining `ParserModule` behind class handles removed the missing-module
  diagnostic and crash.
- Three grouped HIR fix/verify cycles reduced Stage3 diagnostics from 274 to
  119, then 47, then 22. The missing-module/SIGILL failure did not recur.
- Focused temporary Rust-runner evidence passed: HIR resolver 9/9 and the new
  nested placeholder-lambda parser example. The parser file retained one
  unrelated optional-chaining failure.
- Final Stage2 compiled 727 files with 0 failures and passed version,
  unsupported-command, frontend-smoke, and immutable admission checks.
  Candidate SHA-256:
  `4e0bf93ef744c59608589e40d1eeebef696aab1cb77f0ecce7267a0b11097aef`.
- Final Stage3 exited 1 after phase-4 HIR lowering. The remaining 22
  diagnostics grouped as raw documentation interpolation identifiers (11),
  placeholder names `_`/`_1` (8), stale `selected` and
  `nilnilnilnilnilnil` names (2), and one loader placeholder.
- Evidence:
  `build/bootstrap/stage4-spdev-current/global-cycle3-stage2/stage2.log` and
  `build/bootstrap/stage4-spdev-current/global-cycle3-stage3/stage3.log`.
- The mandatory three-cycle cap was exhausted for that session. Stage4 was not
  launched because Stage3 did not produce a compiler; completion is unproven.

Next: start a fresh grouped-error session from the 22-error frontier. First
confirm the current-main sources contain the intended raw-doc, placeholder,
and local-name fixes, then build/admit one fresh Stage2 and run Stage3. Do not
rerun the previous cycle unchanged.

## 2026-08-01 current-main integration and capped pre-build result

- Rebased the Stage4 lane onto current `main` in an isolated jj workspace and
  resolved seven owned-file conflicts semantically. A diff audit caught and
  removed 45,269 lines of unrelated rebase deletions before integration.
- Merged focused evidence passed once: parser, HIR import resolution, and
  entry-closure physical-source deduplication all exited 0 under the temporary
  Rust test-runner opt-in.
- Reapplied the remaining 22-error source fixes against current main: explicit
  placeholder loops, stale-local renames, module-scope runtime declarations,
  linker imports, and escaped raw block examples.
- All three fresh Stage2 attempts stopped before compilation on current-main
  `src/compiler_rust/lib/std/src/core/__init__.spl` package-export ambiguity.
  Cycle 1 reported `Debug`; cycle 2 reported `Error`; cycle 3 confirmed that
  unqualified `export Display, Debug` still scans both `fmt.spl` and
  `traits.spl` even without `export traits.*`.
- The experimental wildcard/facade edits were reverted because they did not
  pass admission. Evidence is retained under
  `build/bootstrap/stage4-spdev-current/fresh-cycle{1,2,3}-stage2/stage2.log`.
- The mandatory three-cycle cap is exhausted. No Stage2 candidate was produced
  in this session, so Stage3 and Stage4 were not launched.

Next: in a fresh session, qualify specialized package exports at their owners
(starting with `export use fmt.{Display, Debug, ...}` and
`export use error.{Error, ...}`) and audit the remaining explicit core exports
for duplicate owners before one new Stage2 attempt. Do not rerun cycle 3
unchanged.

## 2026-08-01 qualified package-facade recovery

- Replaced ambiguous unqualified core exports with owner-qualified facades,
  excluded specialized names from `traits.*`, removed duplicate regex exports,
  and removed the internal `random.sqrt` collision with canonical `math.sqrt`.
- Restored `std.spec` to its documented fast/default contract. The appended
  advanced block had contradicted the header, re-exported excluded mocking and
  diagram modules, and defined `MockMode` from both `mock` and `registry`.
  Advanced APIs remain available through `std.spec.adv`.
- Removed the redundant unqualified tail from `std.tooling`, eliminated
  duplicate qualified public names, and removed exports for four absent modules
  (`test_output`, `test_args`, `test_discovery`, `test_summary`).
- Stage2 cycle 1 moved from core `Debug` to spec `MockMode`; cycle 2 moved to
  tooling `MigrationResult`; cycle 3 cleared all package-export ambiguity and
  reached source discovery/parsing.
- The final cycle stopped at an independent parser error in
  `src/compiler_rust/lib/std/src/core/cmp_ord.spl:116`:
  `impl Reverse<T>: Ord<T>:` is rejected because the grammar requires a newline
  after the impl target colon.
- Evidence:
  `build/bootstrap/stage4-spdev-current/qualified-cycle{1,2,3}-stage2/stage2.log`.
- The mandatory three-cycle cap is exhausted. No Stage2 candidate was produced;
  Stage3 and Stage4 were not launched.

Next: in a fresh session, rewrite the `Reverse<T>` implementation using the
canonical trait-implementation syntax already accepted elsewhere in this tree,
add a focused parser fixture for that syntax, then start one new Stage2 cycle.
Do not rerun qualified cycle 3 unchanged.

## 2026-08-01 parser-frontier recovery after main integration

- Rewrote `Reverse<T>` with canonical generic trait-implementation syntax and
  added a focused parser regression fixture.
- Renamed the `graph.spl` nested `union` helper because `union` is reserved,
  and added a static parser regression guard.
- Converted block doc comments between `ParIter<T>` trait methods to ordinary
  comments because that grammar slot only accepts method declarations.
- The focused parser evidence passed all three new regression checks
  (`11 examples, 0 failures` in the relevant describe block). The file retains
  one unrelated, pre-existing optional-chaining failure.
- Stage2 cycle 1 advanced to `core/graph.spl:529`; cycle 2 advanced to
  `infra/parallel.spl:31`; cycle 3 advanced to `infra/parallel.spl:359`.
- The final frontier is `processor: fn(<T>) -> R`: discovery rejects `<T>` as
  the function parameter type (`expected identifier, found Lt`). Evidence:
  `build/bootstrap/stage4-spdev-current/cmp-cycle{1,2,3}-stage2/stage2.log` and
  `build/mini_builds/stage4-trait-doc-parser.log`.
- The mandatory three-cycle cap is exhausted. No Stage2 candidate was produced;
  Stage3 and Stage4 were not launched, and nothing was pushed.

Next: in a fresh session, determine the canonical callable parameter syntax for
`par_chunks` (likely a named or tuple-style parameter rather than `<T>`), add a
focused parser fixture, and begin a new bounded Stage2 cycle. Do not rerun
`cmp-cycle3-stage2` unchanged.

## 2026-08-01 callable and member-declaration recovery

- Replaced the invalid `par_chunks` callback type `fn(<T>) -> R` with the
  canonical generic-list callable type `fn([T]) -> R`; its focused executable
  parser test passed.
- Converted indented block doc comments in `infra/synchronization.spl` member
  slots to ordinary comments; the focused source guard passed.
- Added the five missing body colons on `LanguageCompiler` methods in
  `tooling/compiler/python.spl`; the focused source guard passed.
- Stage2 cycle 1 advanced to `infra/synchronization.spl:71`; cycle 2 advanced
  to `tooling/compiler/python.spl:86`; cycle 3 advanced to
  `tooling/deployment/automation.spl:179`.
- The final frontier is `pub fn parse_platform(self): (text, text):` where the
  return-type colon is placed before the tuple type. Evidence:
  `build/bootstrap/stage4-spdev-current/callable-cycle{1,2,3}-stage2/stage2.log`
  and focused logs `build/mini_builds/stage4-{callable-list,sync-doc,python-signature}-parser.log`.
- The mandatory three-cycle cap is exhausted. No Stage2 candidate was produced;
  Stage3 and Stage4 were not launched, and nothing was pushed.

Next: in a fresh session, rewrite `parse_platform` as
`pub fn parse_platform(self) -> (text, text):`, audit this file for the same
signature inversion, add focused parser coverage, and begin a new bounded
Stage2 cycle. Do not rerun `callable-cycle3-stage2` unchanged.

## 2026-08-01 deployment and tooling-parser recovery

- Rewrote `parse_platform` with the canonical tuple return arrow and confirmed
  there were no other inverted signatures in `automation.spl`.
- Replaced two raw regex literals in `tooling/spec_gen.spl` whose escaped quote
  prematurely ended the raw string with ordinary escaped regex strings.
- Removed one stray C-style closing brace from the indentation-based loop in
  `tooling/testing/filter.spl`; the other standalone braces in the file close
  valid struct literals and were preserved.
- All three focused parser/source guards passed. Stage2 cycle 1 advanced to
  `tooling/spec_gen.spl:90`; cycle 2 advanced to
  `tooling/testing/filter.spl:623`; cycle 3 advanced to
  `tooling/testing/parallel.spl:402`.
- The final frontier is the Rust-style zero-argument lambda
  `val work_fn = || runner(item.suite)`, rejected as `DoublePipe` where an
  expression is required. Evidence:
  `build/bootstrap/stage4-spdev-current/deployment-cycle{1,2,3}-stage2/stage2.log`
  and focused logs `build/mini_builds/stage4-{deployment-tuple,spec-gen-regex,filter-brace}-parser.log`.
- The mandatory three-cycle cap is exhausted. No Stage2 candidate was produced;
  Stage3 and Stage4 were not launched, and nothing was pushed.

Next: in a fresh session, replace the zero-argument lambda with canonical Simple
syntax (expected `\: runner(item.suite)`), audit the file for additional `||`
lambdas, add focused parser coverage, and begin a new bounded Stage2 cycle. Do
not rerun `deployment-cycle3-stage2` unchanged.

## 2026-08-01 lambda and HTTP discovery recovery

- Replaced the sole Rust-style zero-argument lambda in
  `tooling/testing/parallel.spl` with canonical Simple `\:` syntax and added an
  executable zero-argument-lambda fixture.
- Renamed the reserved `actor` extern parameter to `actor_handle`.
- Replaced both Rust-style tuple closures in `host/common/net/http.spl` with
  established Simple tuple-destructuring lambdas (`\(n, _): ...`).
- All focused regression checks passed. Stage2 cycle 1 advanced to the reserved
  actor parameter at `parallel.spl:467`; cycle 2 advanced to the first HTTP
  tuple closure at `http.spl:32`; cycle 3 advanced to `http.spl:143`.
- The final frontier applies `_hval` directly to an interpolated literal:
  `"Bearer {token}"_hval` (with the same form for basic auth at line 149).
  Discovery parses the suffix as a separate identifier in the call arguments.
  `HeaderValue.from_str(text)` is the canonical conversion surface. Evidence:
  `build/bootstrap/stage4-spdev-current/lambda-cycle{1,2,3}-stage2/stage2.log`
  and focused logs `build/mini_builds/stage4-{zero-lambda,actor-param,http-tuple-lambda}-parser.log`.
- The mandatory three-cycle cap is exhausted. No Stage2 candidate was produced;
  Stage3 and Stage4 were not launched, and nothing was pushed.

Next: in a fresh session, replace both interpolated `_hval` expressions with
`HeaderValue.from_str(...)`, add focused parser/source coverage, and begin a new
bounded Stage2 cycle. Do not rerun `lambda-cycle3-stage2` unchanged.

## 2026-08-01 header values, varargs, and Error impl recovery

- Replaced both interpolated `_hval` suffix expressions with the canonical
  `HeaderValue.from_str(...)` conversion.
- Rewrote all three filesystem staging signatures from legacy prefix varargs
  (`...files: FilePath`) to documented postfix varargs (`files: FilePath...`).
- Added the missing body colon to five empty `impl Error for Type` marker blocks
  found by the scoped audit (`HttpError`, `NetError`, `StaticVecError`,
  `StaticStringError`, and `FixedVecError`).
- All focused regression guards passed. Stage2 cycle 1 advanced to the first
  filesystem vararg at `async_nogc_mut/io/fs/file.spl:214`; cycle 2 advanced to
  `host/common/net/http_error.spl:181`; cycle 3 advanced to
  `host/common/net/runtime.spl:98`.
- The final frontier is function-typed parameter syntax
  `task: async fn() -> T`; the same form occurs in `block_on` at line 116.
  Discovery expects a function type directly after the parameter colon and
  rejects `async fn`. Evidence:
  `build/bootstrap/stage4-spdev-current/hval-cycle{1,2,3}-stage2/stage2.log`
  and focused logs `build/mini_builds/stage4-{http-hval,fs-varargs,error-impl}-parser.log`.
- The mandatory three-cycle cap is exhausted. No Stage2 candidate was produced;
  Stage3 and Stage4 were not launched, and nothing was pushed.

Next: in a fresh session, establish the supported callable representation for
these runtime wrappers (the current grammar accepts `fn() -> T`, not
`async fn() -> T`), update both `spawn` and `block_on` without claiming async
type semantics the language cannot express, add focused coverage, and begin a
new bounded Stage2 cycle. Do not rerun `hval-cycle3-stage2` unchanged.

## 2026-08-01 async callable and Rust struct-mixin parser diagnosis

- Replaced the unsupported callable parameter types `async fn() -> T` in
  `host/common/net/runtime.spl` with the grammar-supported `fn() -> T`; the
  wrappers retain their existing runtime-stub delegation behavior.
- The focused parser/source regression passed.
- Stage2 cycle 1 reached `host/common/net/tcp.spl:32` at the documented
  `pub struct TcpListener with LeakTracked:` syntax.
- A current installed seed `check` parsed that declaration, but native-build
  discovery rejected it. To eliminate stale-artifact uncertainty, rebuilt a
  dedicated current-source Rust bootstrap seed. Build log:
  `build/bootstrap/stage4-spdev-current/fresh-rust-seed-build.log`; pinned seed:
  `build/bootstrap/stage4-spdev-current/fresh-rust-seed/simple`, SHA-256
  `e06ebd42cc8735859c8dc9286af7c5f9f62d4f55777724a8e213c0e36010f01f`.
- Cycles 2 and 3 (installed current seed, then pinned freshly rebuilt seed)
  reproduced the same native-discovery failure. This is not a stale seed and
  valid mixin declarations must not be rewritten away.
- Root cause: `src/compiler_rust/parser/src/types_def/mod.rs` parses explicit
  `with` mixins in `parse_class_with_attrs`, but `parse_struct_with_attrs`
  proceeds directly from optional legacy parent syntax to `where`/body parsing.
  The pure-Simple parser already handles mixins for both structs and classes in
  `src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl`, and the
  language guide explicitly documents `struct X with Mixin:`.
- Evidence:
  `build/bootstrap/stage4-spdev-current/asyncfn-cycle1-stage2/stage2.log`,
  `current-seed-cycle2-stage2/stage2.log`, and
  `fresh-seed-cycle3-stage2/stage2.log`.
- The mandatory three-cycle cap is exhausted. No Stage2 candidate was produced;
  Stage3 and Stage4 were not launched, and nothing was pushed.

Next: in a fresh session, extend Rust `parse_struct_with_attrs` to parse the
same explicit mixin list as classes, preserve those mixins in the struct AST
(adding/using the corresponding StructDef field as required), add Rust parser
coverage for single/multiple/generic struct mixins, rebuild the dedicated seed,
then begin a new bounded Stage2 cycle. Do not rewrite the valid TCP/UDP structs
and do not rerun `fresh-seed-cycle3-stage2` unchanged.

## 2026-08-01 Rust struct mixins and external enum identities

- Added shared explicit-mixin parsing to the Rust parser. A struct with mixins
  lowers to the existing `ClassDef` mixin pipeline with `is_value_type: true`,
  preserving struct copy semantics while reusing established mixin expansion.
- Added Rust parser coverage for single, multiple, and generic struct mixins;
  `simple-parser --test data_structures` passed all 25 tests.
- Rebuilt and pinned the struct-mixin seed at
  `build/bootstrap/stage4-spdev-current/struct-mixin-rust-seed/simple`, SHA-256
  `fd2a748933d4ab0c4bb7af663facf3e3cd9b1ca26f6142835ee2c48f106580c5`.
- Stage2 cycle 1 cleared all parsing and reached compilation, reporting 53
  failing files. The largest cluster was 24 missing enum runtime identities.
- Extended enum identity qualification to use a unique global mangled suffix
  when imports/facades lose the direct owner. The focused test passed. Cycle 2
  showed external/runtime owners (`ByteOrder`, `RiscvTargetAbi`, primitive-like
  `f32`) are absent from the selected source sidecar, so unique-suffix lookup
  alone could not resolve them.
- Added a final stable bare-owner fallback only after local, import, qualified,
  and unique-global resolution are exhausted. Declared enum collisions remain
  rejected when the global sidecar is constructed. The focused external-owner
  test passed.
- Rebuilt and pinned the final seed at
  `build/bootstrap/stage4-spdev-current/external-enum-rust-seed/simple`, SHA-256
  `fca4042932ef92a449b654a8da97b09dadc4389f6a07262c1dea6472588f0189`.
- Stage2 cycle 3 eliminated all 24 enum-identity failures and reduced the total
  from 53 to 29 failing files. Evidence:
  `build/bootstrap/stage4-spdev-current/mixin-cycle{1,2,3}-stage2/stage2.log`,
  `build/mini_builds/stage4-rust-struct-mixin-parser.log`,
  `stage4-enum-runtime-suffix.log`, and `stage4-enum-runtime-external.log`.
- The next dominant MIR cluster is variant resolution: lowercase
  `Option.some/none` in `core/cmp_ord.spl`, `core/error.spl`, `core/iter.spl`,
  and `sys/args.spl`, plus `SdnValue.String` in `sdn/parser.spl`. Remaining
  groups include ten field-type inference failures, three capability errors,
  nine codegen/stub-prevention failures, two duplicate vtables, and one module
  resolution failure.
- The mandatory three-cycle cap is exhausted. No Stage2 candidate was produced;
  Stage3 and Stage4 were not launched, and nothing was pushed.

Next: in a fresh session, diagnose enum variant canonicalization in Rust MIR
lowering. Preserve documented Option aliases if they are language-supported;
otherwise normalize these five leaf call sites to declared variant names with
focused coverage. Begin a new bounded Stage2 cycle using the pinned
`external-enum-rust-seed` and do not rerun `mixin-cycle3-stage2` unchanged.

## 2026-08-01 Option aliases, stale materialization, and runtime link frontier

- Extended Rust MIR builtin lowering to accept the documented lowercase
  `Option.some/none` aliases alongside `Some/None`. The focused MIR test passed:
  `build/mini_builds/stage4-option-alias-mir.log`.
- Corrected the invalid `SdnValue.String(combined)` call to the declared
  `SdnValue.text(combined)` variant and added a source regression guard. The
  relevant parser examples passed (25 examples, 0 failures); the whole parser
  file retains one unrelated optional-chaining failure. Evidence:
  `build/mini_builds/stage4-sdn-text-variant-parser.log`.
- Rebuilt and pinned the current seed at
  `build/bootstrap/stage4-spdev-current/option-alias-rust-seed/simple`, SHA-256
  `cb957967bddcde0e2ec809b01d4e543f1db424522e866dff675f40d27d59a138`.
- Diagnosed the first Stage2 result as a stale sparse-workspace materialization:
  8,080 tracked files were physically absent despite a clean jj status. Clearing
  and re-adding the `.` sparse pattern restored 109,613 paths without changing
  the commit; only 10 expected submodule/platform artifacts remain absent.
- On the corrected tree, Stage2 compiled every module and reached the linker,
  eliminating all prior 24 compile failures. The sole failure is four undefined
  references to `rt_string_repeat`. Evidence:
  `build/bootstrap/stage4-spdev-current/materialized-cycle2-stage2/stage2.log`.
- Rebuilt `simple-runtime` with bootstrap LTO disabled in a dedicated directory.
  `nm` confirms a concrete `T rt_string_repeat` definition in
  `build/bootstrap/stage4-spdev-current/runtime-authority-nolto/libsimple_runtime.a`;
  build evidence is `build/mini_builds/stage4-runtime-nolto-build.log`.
- Final bounded cycle 3 selected that dedicated runtime path but the stage linker
  still omitted/unresolved the symbol. Evidence:
  `build/bootstrap/stage4-spdev-current/materialized-cycle3-stage2/stage2.log`;
  retained objects are in
  `build/bootstrap/stage4-spdev-current/native-objects-Gp2RQf`.
- The mandatory three-cycle cap is exhausted. No Stage2 candidate was produced;
  Stage3 and Stage4 were not launched, verification did not pass, and nothing
  was pushed.

Next: in a fresh session, inspect the native-build runtime archive selection and
final linker command (especially `core-c-bootstrap` composition) to determine
why the explicitly selected no-LTO `libsimple_runtime.a` definition is not
included. Add focused coverage for runtime-path/archive precedence, then begin a
new bounded Stage2 cycle. Do not rerun `materialized-cycle3-stage2` unchanged.

## 2026-08-01 native-all correction and 11-error Stage3 frontier

- Traced bootstrap runtime selection: with `SIMPLE_BOOTSTRAP=1`, the
  `bootstrap_main.spl` entry intentionally selects `libsimple_native_all.a`
  before `libsimple_runtime.a`. The prior dedicated authority replaced only the
  latter, so the stale native-all archive remained authoritative.
- Rebuilt `simple-native-all` with bootstrap LTO disabled and installed it only
  into the dedicated lane authority. It contains both the requesting and
  defining `rt_string_repeat` members; SHA-256:
  `c4d732d6d1e35a4713799947551c452d93eb2458b741a47a4f627d2b4a2645d6`.
  Evidence: `build/mini_builds/stage4-native-all-nolto-build.log`.
- All three Stage2 builds linked, and the final candidate passed bootstrap
  version, unsupported-command, frontend native-build smoke, and immutable
  digest admission. Candidate SHA-256:
  `8d621f2f91a90c29014beff58d645d2eb5f21878b0093d253a861e3fa9293574`.
- Stage3 cycle 1 reported 23 HIR errors. Explicit imports fixed `Symbol`,
  `Effect`, and `GpuBarrierScope`; moving function-local runtime externs to
  module scope fixed `rt_process_exists` and `rt_file_rename`. Cycle 2 removed
  all 12 of those errors.
- Added explicit lexer token provenance for raw/single/triple strings and a
  focused flat-AST regression. The focused temporary Rust-runner test passed:
  `build/mini_builds/stage4-raw-string-provenance-fixed.log`.
- Stage3 cycles 2 and 3 both stop at the same remaining 11 names in
  `builtin_blocks_math.spl` and `builtin_blocks_shell.spl`. Removing only the
  raw-doc snippets did not change the frontier, proving the active trigger is
  the ordinary strings returned by `examples()` (for example
  `"m\\{ x^2 + y^2 }"` and `"sh\\{ ls -la }"`). The `\\{` spelling is not an
  interpolation escape in this bootstrap path, so names inside braces enter
  HIR resolution. Evidence:
  `build/bootstrap/stage4-spdev-current/nativeall-cycle{1,2,3}-stage3/stage3.log`.
- The mandatory three-cycle cap is exhausted. Stage3 produced no compiler;
  Stage4 and release verification were not launched, and nothing was pushed.

Next: in a fresh session, change the ordinary block-example strings to the
language's doubled-brace interpolation escape (`{{` / `}}`) so their runtime
value remains a single-brace block example, add focused value assertions for
math/loss/nograd/shell `examples()`, then begin a new bounded Stage2/Stage3
cycle. Do not rerun `nativeall-cycle3-stage3` unchanged.

## 2026-08-01 block examples and staged SSA payload recovery

- Replaced `\\{` in the ordinary math/loss/nograd/shell `examples()` strings
  with doubled braces. Focused assertions prove their runtime values retain the
  intended single-brace block syntax. Evidence:
  `build/mini_builds/stage4-block-example-brace-values.log`.
- Stage3 cycle 1 cleared all 11 block-example HIR errors and reached MIR
  lowering, then trapped with `field access on nil receiver`/SIGILL.
- GDB localized the trap exactly to
  `var_reassign_local_id_value` through
  `ssa_operand_push_local -> ssa_collect_inst_operand_locals ->
  ssa_cross_block_live_locals -> ssa_alloca_transform_blocks`. Evidence:
  `build/bootstrap/stage4-spdev-current/braces-cycle2-gdb-stage3.log`.
- Kept nested `MirOperand.Copy/Move(LocalId)` decoding inside the SSA module
  rather than crossing the staged-native module boundary, then added a
  fail-closed operand-payload gate: malformed nil LocalIds reject the alloca
  transform and preserve original MIR instead of inventing local 0 or silently
  dropping a read. Focused source contracts passed:
  `build/mini_builds/stage4-ssa-local-payload-focused.log` and
  `stage4-ssa-malformed-operand-gate.log`.
- All three Stage2 candidates linked and passed bootstrap admission. The final
  admitted candidate SHA-256 is
  `84a57950e709eb479c505f30c74a5375615defa5f119a4532e8469fe5c3740cd`.
- Final Stage3 cleared the nil-receiver/SIGILL trap and advanced further through
  MIR lowering. It now fails cleanly during bootstrap flat MIR type
  registration: `unsupported MIR type kind: <enum@0xb7b2eb40>`, after unresolved
  `get` and two `to_f64` method placeholders. Evidence:
  `build/bootstrap/stage4-spdev-current/braces-cycle3-stage3/stage3.log`.
- The mandatory three-cycle cap is exhausted. Stage3 produced no compiler;
  Stage4 and release verification were not launched, and nothing was pushed.

Next: in a fresh session, instrument `register_bootstrap_type_recursive` around
`function_lowering.spl:637/649` to retain the owning function/local/type source
when a staged enum payload reaches the unsupported-kind arm. Diagnose whether
the value is a lost `MirTypeKind` nested payload or a missing supported kind,
add focused type-registration coverage, then begin a new bounded Stage2/Stage3
cycle. Do not rerun `braces-cycle3-stage3` unchanged.

## 2026-08-01 optional-field MIR type registration frontier

- Added fail-only flat type-registration context. The unsupported values are
  exactly `BackendError.span: Span?` and `CompiledUnit.entry_point: text?`, not
  anonymous nested MIR payloads. Focused contract evidence:
  `build/mini_builds/stage4-type-registration-context-cycle2.log`.
- Qualified the broad MIR-lowering match with `HirTypeKind` ownership, then
  added discriminant-first isolated extraction for `HirTypeKind.Optional`,
  mirroring the existing staged `Dict` workaround. The ownership/predispatch
  contract passes; evidence:
  `build/mini_builds/mir-hir-type-kind-ownership-cycle2.log`.
- Discovered that `current-seed-cache` returned a byte-identical stale Stage2
  binary after compiler-source edits (SHA-256 `b0552da1207246cd7249022793b4a63a951a4a4512d6e44e4fc9cfa115c4e5e6`).
  Rejected it and used fresh per-cycle caches thereafter.
- Fresh Stage2 candidates passed version, unsupported-command, frontend smoke,
  and immutable-hash admission. Cycle 2 SHA-256:
  `be886e82c0da5e97d6a944b72241fee5fbdb2c23beeb0f447d2deda5dde75836`;
  cycle 3 SHA-256:
  `a60175a216777ba050cc17fd74bd243053d7124d931a4cc9cc8f1e6c36a83174`.
- Stage3 cycles 1 through 3 all fail on the same two optional fields. Owner
  qualification and discriminant-first predispatch do not recognize these
  staged values, indicating their `HirTypeKind` discriminants/payloads are
  already malformed before `MirLowering.lower_type`. Final evidence:
  `build/bootstrap/stage4-spdev-current/typekind-cycle3-stage3/stage3.log`.
- The mandatory three-cycle cap is exhausted. Stage3 produced no compiler;
  Stage4, essential-tools smoke, and release verification were not run. Nothing
  was pushed.

Next: in a fresh session, instrument `lower_struct_type` to print the numeric
field-kind discriminant alongside reference discriminants for `Optional`,
`Infer`, `Error`, and `Named`, and instrument HIR struct-field construction for
these two owners. Determine where `Span?`/`text?` cease to be valid Optional
values before changing MIR fallback semantics. Use fresh per-cycle Stage2
caches; do not reuse `current-seed-cache` or rerun `typekind-cycle3-stage3`.

## 2026-08-01 flat optional tags and recursive Span frontier

- Paired HIR/MIR numeric receipts proved both failing fields were already
  `HirTypeKind.Infer` at HIR construction and were not corrupted by
  `HirStruct.fields` storage. Cycle 1 values: actual/infer `3031551406`,
  optional reference `2589120870`. Evidence:
  `build/bootstrap/stage4-spdev-current/typekind-cycle4-stage3/stage3.log`.
- Root cause was the flat bridge's unguarded imported `TYPE_OPTION*` constants.
  Stage3 misreads imported fixed module values, while optional tags 14..18 had
  no ordered-literal guards like primitive tags already did. Added fixed-tag
  decoding for bare, i64, f64, text, and bool optionals. Focused contract:
  `build/mini_builds/flat-optional-fixed-tag-guard.log`.
- Cycle 2 proved both target fields remain Optional across HIR construction and
  MIR consumption: actual/optional `2589120870`, infer `3031551406`. The
  `CompiledUnit.entry_point: text?` path then lowered without an error, while
  `BackendError.span: Span?` failed recursively on its inner type. Evidence:
  `build/bootstrap/stage4-spdev-current/typekind-cycle5-stage3/stage3.log`.
- Added discriminant-first isolated handling for `HirTypeKind.Named`, preserving
  the existing custom-primitive and canonical struct-symbol semantics. Focused
  ownership contract passed:
  `build/mini_builds/mir-hir-type-kind-ownership-cycle3.log`.
- Fresh Stage2 candidates passed version, unsupported-command, frontend smoke,
  and immutable-hash admission. Cycle 1 SHA-256:
  `95a43bed4472a4887f63f75d5291fc1a3b351f16e325e67992c429c7638c52af`;
  cycle 2: `e731509a138fd755ac41c4b8e4bdbd59e2ee762c063f5ab467a8444274c49e3b`;
  cycle 3: `a30fe01181cef6513a3ee2952d6a36620556277b0255211bcbdaafb9e206fc79`.
- Cycle 3 still fails recursively while lowering `BackendError.span`; its outer
  Optional discriminant remains correct. Named predispatch therefore either
  does not recognize the inner staged value or receives a non-Named/malformed
  inner payload. Final evidence:
  `build/bootstrap/stage4-spdev-current/typekind-cycle6-stage3/stage3.log`.
- The mandatory three-cycle cap is exhausted. Stage3 produced no compiler;
  Stage4, essential-tools smoke, and release verification were not run. Nothing
  was pushed.

Next: in a fresh session, add an Optional-owner diagnostic inside
`MirLowering.lower_type` that prints the extracted inner discriminant and
references for Named/Infer/Error/Str before recursing, plus the `SymbolId` only
when the inner discriminant is proven Named. Compare `Span?` against `text?`.
Fix the first proven inner-payload boundary; do not add an i64/error fallback.
Use fresh per-cycle caches and do not rerun `typekind-cycle6-stage3` unchanged.
