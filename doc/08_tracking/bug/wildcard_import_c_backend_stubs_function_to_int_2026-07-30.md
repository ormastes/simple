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

## To actually fix

Root-cause the exact colliding symbol per the sibling bug doc's suggested
method: bisect by commenting out `c_backend_stubs.spl`'s transitive imports
one at a time under the wildcard, or instrument the interpreter's flat
registry lookup to log the symbol name at the point of the failed int
conversion.

## Related

- `doc/08_tracking/bug/interp_lint_main_then_frontend_dict_to_int_2026-07-28.md`
- `reference_interpreter_dict_and_value_quirks` (session memory)
