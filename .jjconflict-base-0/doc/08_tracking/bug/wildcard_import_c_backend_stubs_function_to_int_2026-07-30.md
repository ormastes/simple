# `use compiler.backend.backend.c_backend_stubs.*` deterministically poisons the interpreter session with "cannot convert function to int"

- **Filed:** 2026-07-30
- **Severity:** medium — deterministic false-red for any spec that wildcard-imports this module
- **Status:** open (worked around in the one known-affected spec; root symbol collision not yet identified)
- **Found via:** BCAP lane triage of `test/01_unit/compiler/backend/backend_capability_spec.spl`

## Symptom

Under `bin/simple test --no-session-daemon <spec>`, a spec that contains
```simple
use compiler.backend.backend.c_backend_stubs.*
```
(wildcard import) runs all of its real `it` blocks successfully (they print
`✓` and the evidence file records 0 real failures), but the **child process
then exits non-zero**, printing after the last test result:
```
error: semantic: type mismatch: cannot convert function to int
error: test-runner: spec failed
```
`test_runner_single.spl`'s fail-safe (`code != 0 and assert_ran` branch,
`src/app/test_runner_new/test_runner_single.spl:~419`) correctly refuses to
trust a non-zero exit even with clean evidence, and forces one phantom
`failed` count — so a spec whose every real assertion passes still reports
as `N+1 total, N passed, 1 failed` / exit 1.

## Minimal repro (all run 2026-07-30, deterministic)

| variant | result |
|---|---|
| `use compiler.backend.backend.c_backend_translate.{MirToC}` alone + trivial `it` | PASS, exit 0 |
| same + `use compiler.backend.backend.c_backend_stubs.*` (wildcard) + trivial `it` | **FAIL** — exit 1, "cannot convert function to int" after the (passing) test prints |
| same + `use compiler.backend.backend.c_backend_stubs` (**no** wildcard) + trivial `it` | PASS, exit 0 |

So: importing the module for its side effect (registering the `impl MirToC:`
stub methods `translate_create_promise`, `translate_receive`, etc.) is
harmless; the **wildcard star** is what triggers the crash. The crash fires
even when the `it` bodies never call anything from `c_backend_stubs` at all
and no `describe`/`it` names or counts affect it — reproduced with a single
`expect(1).to_equal(1)` body.

## Likely family

Same interpreter cross-module global-registry class as
`doc/08_tracking/bug/interp_lint_main_then_frontend_dict_to_int_2026-07-28.md`
("Executing lint-main then the frontend in one interpreter session fails
with cannot convert dict to int") — that doc's own working theory: "the flat
function/type registry lets one module's same-named symbol hijack another's"
(family: `feedback_interp_struct_name_collision_global_registry`). This is
the same shape of bug (`cannot convert <T> to int`, deterministic, triggered
by importing/executing a specific module graph) with a different colliding
type (`function` here vs `dict` there). The exact colliding symbol was not
identified in either case — `c_backend_stubs.spl` conditionally imports
(inside `when not BOOTSTRAP_NO_C:`) `compiler.mir.mir_data.*`,
`compiler.backend.c_type_mapper.{CTypeMapper}`,
`compiler.backend.c_ir_builder.{CIRBuilder, escape_c_string}`,
`compiler.backend.common.mir_text_codegen.MirTextCodegen`,
`compiler.backend.backend.backend_types.{CodegenTarget, CompileOptions,
CompiledModule}` — the wildcard re-export of one of these (or a name from
the `impl MirToC:` method block itself) most likely hijacks a same-named
symbol the test-runner's own post-test finalize/doc-coverage pass expects to
be an `int`.

## Workaround (applied)

`test/01_unit/compiler/backend/backend_capability_spec.spl` changed:
```simple
use compiler.backend.backend.c_backend_stubs.*
```
to
```simple
use compiler.backend.backend.c_backend_stubs
```
Verified the three tests exercising `MirToC.translate_create_promise` /
`translate_receive` (which live in `c_backend_stubs.spl`'s `impl MirToC:`
block) still pass — confirming the non-wildcard import still registers the
impl block; only the flat-namespace re-export of its transitive imports was
the hazard.

## Impact

Any spec wildcard-importing `compiler.backend.backend.c_backend_stubs` (or
structurally similar modules with a `when ...:`-gated import block) risks
this same false-red, independent of what the spec actually tests. Worth a
repo-wide grep for `c_backend_stubs\.\*` and similar `_stubs.*` /
conditionally-gated-import modules.

## UPDATE 2026-07-30 (lane WCI1): NOT scoped to c_backend_stubs — 6 independent
## trigger modules found; mechanism still not pinned to a symbol pair

### The bug is much broader than the title suggests

Bisecting via single-module `use compiler.X.*` specs (trivial `it`, no calls
into the imported module at all) shows the crash is **independently**
triggered — with `c_backend_stubs` removed from the import list entirely —
by wildcard-importing any of:

| module (wildcard alone reproduces) | result |
|---|---|
| `compiler.backend.backend.c_backend_stubs` | FAIL (original finding) |
| `compiler.backend.common.type_mapper` | FAIL |
| `compiler.backend.backend_api` | FAIL |
| `compiler.backend.backend_helpers` | FAIL |
| `compiler.backend.codegen_factory` | FAIL |
| `compiler.backend.wasm_backend` | FAIL |

None of these five share a `use`-graph with `c_backend_stubs.spl` (confirmed
by reading each file's own `use` list) — so this is not "one bad file", it's
a property of wildcard-importing several different, otherwise-unrelated
backend modules.

### What does NOT reproduce it alone (ruling out single-file causes)

Every module transitively reachable from the FAIL set above was tested with
its own standalone `use compiler.X.*` + trivial `it`, and **all pass clean**:
`compiler.mir.mir_data`, `compiler.mir.mir_instructions`,
`compiler.backend.c_ir_builder`, `compiler.backend.common.mir_text_codegen`,
`compiler.backend.backend.backend_types` (the double-`backend` one, direct),
`compiler.backend.codegen_types`, `compiler.backend.llvm_codegen_adapter`,
`compiler.backend.llvm_lib_backend`, `compiler.backend.cranelift_codegen_adapter`,
`compiler.mir_opt.mir_opt.mod`, `compiler.backend.llvm_support_matrix`,
`compiler.common.mir_target_context`.

So no *single* sub-module carries the offending symbol either — the crash
needs the **combination** each FAIL-set module assembles (its own
declarations plus several `use`d names flattened together), not any one
piece in isolation. This argues against a simple two-file name clash and
for either (a) a collision between two specific names that only co-occur
once a module's full transitive `use` graph is flattened, or (b) a
scale/depth effect in the interpreter's flat wildcard-import registry
(number of names flattened, or wildcard-of-a-wildcard re-export depth)
rather than a single reproducible name pair.

### Mechanism confirmed: child-process Rust seed, `Value::as_int()`

The "child binary" line in a full-output run (not just the tail) shows the
crash happens in `bin/release/x86_64-unknown-linux-gnu/simple`, i.e. the
**Rust-built seed**, invoked as a child process by the test runner — the
seed itself prints `WARNING: this Rust-built Simple binary is a bootstrap
seed only; do not use it as the normal tool.` on every run. So `bin/simple
test` currently executes specs via the seed's interpreter, not the
pure-Simple one (worth flagging separately from this bug — the "default
tooling = self-hosted binary" rule is currently not what's deployed at
`bin/release/x86_64-unknown-linux-gnu/simple`).

The exact error text (`"type mismatch: cannot convert {actual_type} to
int"`) is generated at `src/compiler_rust/compiler/src/value_impl.rs:137`,
inside `Value::as_int()`'s fallback arm. Every other `Value` variant has an
explicit conversion (Int, UInt, Float, Bool, Unit, Unique/Shared/Weak/Handle/
Borrow unwrap, single-field newtype-object unwrap, Str/Symbol get dedicated
messages) — a bare `Function` value only reaches this fallback, so *some*
code path calls `.as_int()` on a `Value::Function` after the spec's real `it`
blocks finish. We were not able to find the call site (would require
instrumenting/rebuilding the Rust seed, out of scope for this contained
lane) or the name of the symbol whose lookup returns a function where an int
was expected.

### A SEPARATE, unrelated bug found by accident while probing this one

`test/01_unit/compiler/backend/type_mapper_spec.spl`'s "handles composite
types using each backend strategy" test has a **genuine, real** failure
(`semantic: undefined field 'kind': cannot access field on value of type
'function'`) that is **not** this bug — bisected down to:
```
[("count", MirType.i64()), ("ready", MirType.bool())].map("{_.0}: {_.1}")
```
i.e. `Array<(text, T)>.map(...)` with a **string-template closure that
tuple-indexes the placeholder** (`_.0` / `_.1`) inside string interpolation
combined with a nested `self.` method call, is broken standalone (reproduced
in a fresh scratch spec with zero backend imports). Filed only as a note
here since it was found alongside; not investigated further and no fix
attempted — worth its own bug doc if picked up.

#### UPDATE 2026-07-30 (lane TMF1) — root-caused and fixed for the nested-call shape

Bisected the minimal failing combination: tuple-indexing alone (`_.0` or
`_.1` used once, bare or wrapped in a call) works fine; the break needs a
placeholder used a SECOND time in the same template where that second use is
itself a call/method-call argument (e.g. `{_.0}: {self.map_type(_.1)}` or the
smaller repro `{_.0}: {double(_.1)}`), evaluating to a bare unapplied
function ("cannot access field on value of type 'function'" /
"cannot convert function to int") instead of the field value.

Root cause: a `"{...}"` interpolation region is sub-parsed standalone via a
fresh `parse_expr()` call
(`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:flat_bridge_parse_interp_inner`).
Inside such a region a bare `_` already has a fixed meaning (the value bound
by the enclosing `.map()`/etc. call), but `parse_call_arg()`
(`src/compiler/10.frontend/core/parser_expr.spl:657`) unconditionally applies
the `_`-placeholder-shorthand transform
(`src/compiler/10.frontend/desugar/placeholder_lambda.spl:transform_placeholder_lambda`)
to EVERY call/method-call argument anywhere in the language — including a
nested call parsed while sub-parsing an interpolation region. So
`self.map_type(_.1)`'s argument `_.1` got hijacked into its own unapplied
`\__p0: __p0.1` closure instead of staying a plain field access on the
template's already-bound `_`.

Fix (pure Simple, frontend/desugar layer only, no lexer.spl touched): added a
save/restore suppression flag
(`placeholder_transform_suppressed`/`set_placeholder_transform_suppressed` in
`placeholder_lambda.spl`) that `transform_placeholder_lambda` checks first and
no-ops on; `flat_bridge_parse_interp_inner` sets it around its `parse_expr()`
call and restores the previous value on every return path. This is contained
to the interpolation-region mini-parse and does not change ordinary
`_`-shorthand behavior anywhere else (verified: all 22 pre-existing cases in
`test/feature/usage/placeholder_lambda_spec.spl` are unaffected).

Regression coverage added: `test/feature/usage/placeholder_lambda_spec.spl`
(+ byte-identical `test/03_system/` twin), new context "string template
placeholder scoping" — plain-function and method-call nested-argument shapes.

**Not yet verified against the deployed binary**: `bin/simple test` executes
the pre-built self-hosted `bin/release/x86_64-unknown-linux-gnu/simple`
artifact, which only picks up `src/compiler/**.spl` changes after a
self-hosting rebuild (`bin/simple build bootstrap`). Per standing repo
guidance ("no bootstrap unless essential"), that rebuild was not run in this
contained lane — the two new regression `it` blocks and
`type_mapper_spec.spl`'s "handles composite types using each backend
strategy" case are confirmed still red against the current (pre-fix) binary
(matches the trace above exactly: "cannot convert function to int"). The fix
should turn all three green once the compiler is next rebuilt from this
source.

**A second, separate issue found while bisecting, NOT fixed**: two BARE
(non-call) placeholder uses in one template, e.g. `"{_.0}: {_.1}"` with no
nested call at all, ALSO fails, with `semantic: variable `__p1` not found` —
reproduced standalone in a fresh single-`it` spec file, so it is not test-state
leakage. This does NOT go through the nested-call path above (no call
argument is involved), and despite an exhaustive repo-wide grep (the string
`__p` and the pattern `__p{i}`/`"__p" + ...` appear ONLY in
`placeholder_lambda.spl`, so the naming can only originate there, yet no
static call-graph path from `flat_bridge_parse_interp_inner`'s bare-`_`
regions reaches `transform_placeholder_lambda`), the exact mechanism was not
pinned down in this contained lane. Filed separately:
`doc/08_tracking/bug/string_template_multi_placeholder_slot_not_found_2026-07-30.md`.

### Real specs confirmed currently affected and fixed (same workaround as
### the original `backend_capability_spec.spl` fix: drop the `.*`)

| spec | before | after |
|---|---|---|
| `test/01_unit/compiler/backend/c_backend_async_spec.spl` | 4 total, 3 passed, 1 failed | 3 total, 3 passed, 0 failed |
| `test/01_unit/compiler/backend/c_backend_bulk_hint_spec.spl` | 5 total, 4 passed, 1 failed | 4 total, 4 passed, 0 failed |
| `test/01_unit/compiler/backend/c_backend_bulk_copy_memmove_spec.spl` | 6 total, 5 passed, 1 failed | 5 total, 5 passed, 0 failed |
| `test/unit/compiler/backend/c_backend_async_spec.spl` (legacy dup tree) | 4 total, 3 passed, 1 failed | 3 total, 3 passed, 0 failed |
| `test/01_unit/compiler/backend/type_mapper_spec.spl` | 4 total, 3 passed, 1 failed (phantom stacked on the real map/template bug above) | 4 total, 3 passed, 1 failed (phantom gone; the 1 failure is now only the real, separate map/template bug) |

All five changed `use compiler.backend.backend.c_backend_stubs.*` (or
`use compiler.backend.common.type_mapper.*`) to the non-wildcard form
(`use compiler.backend.backend.c_backend_stubs` /
`use compiler.backend.common.type_mapper`), verified by grep that no bare
name from the wildcarded module is used directly in the file (the import
exists only for its `impl`/trait-registration side effect), and re-ran each
spec to confirm the real assertion count/pass count is unchanged and the
`cannot convert function to int` error is gone.

### Found but NOT fixed (deferred — larger blast radius)

- `test/feature/usage/wasm_compile_spec.spl` (+ `test/03_system/feature/usage/`
  duplicate) wildcard-imports `compiler.backend.wasm_backend.*` (confirmed
  FAIL-set member above) **and** uses ~7 bare names from it
  (`WasmBackend__create`, `WasmTarget`, `WatBuilder__create`, `WasmType`,
  `JsGlueGenerator__create`, `WasmImport`, `WasmCompileResult`). Fixing this
  one requires enumerating `wasm_backend.spl`'s full export surface into an
  explicit `.{...}` import instead of just dropping the wildcard (unlike the
  `c_backend_stubs`/`type_mapper` cases, which used only the `impl`
  side-effect and nothing else by bare name) — deferred as too large a
  blast-radius edit for this contained lane. Its `use
  compiler.backend.backend_api.*` was narrowed to a bare
  `use compiler.backend.backend_api` (verified no regression) since that
  half of the fix was zero-risk, but the file is still red on this bug via
  `wasm_backend.*`.
- `.spipe_matchers_*` generated-fixture copies of the fixed specs (e.g.
  `.spipe_matchers_c_backend_async_spec.spl`) were left untouched —
  auto-generated SPipe artifacts, out of scope per repo convention.

### Repo-wide wildcard-import audit (test/)

`grep -rEo 'use compiler\.backend\.[A-Za-z0-9_.]+\*' test/` found ~115
matches across the `test/`, `test/01_unit/`, `test/unit/`, `test/03_system/`
and `.spipe_matchers_*` mirror trees (heavy duplication from the ongoing
test-tree reorg, not 115 distinct specs). Of the confirmed FAIL-set modules,
only `c_backend_stubs.*`, `type_mapper.*`, `backend_api.*` and
`wasm_backend.*` are actually wildcard-imported by real specs today (see
tables above); `backend_helpers.*` and `codegen_factory.*` are not
wildcard-imported by any spec currently, only confirmed as independent
crash triggers in isolation — worth a grep sweep again if new specs start
using them with `.*`.

## To actually fix (still open)

Root-causing the exact colliding symbol requires instrumenting the Rust
seed's interpreter (`src/compiler_rust/compiler/src/value_impl.rs` and
whatever calls `.as_int()` on a value produced via the flat wildcard-import
registry) and rebuilding it — out of scope for a contained lane. The
workaround (drop `.*`, use bare `use module` when only the side effect is
needed, or an explicit `.{...}` list when bare names are used) remains the
safe per-spec fix; it does not address the underlying registry bug, which
can resurface in any new spec that wildcard-imports one of the FAIL-set
modules (or, per the scale/depth theory above, any other module whose own
`use` graph reaches a similar size/depth).

## Related

- `doc/08_tracking/bug/interp_lint_main_then_frontend_dict_to_int_2026-07-28.md`
- `reference_interpreter_dict_and_value_quirks` (session memory)
