# Static lock-level acceptance plan

The source requirement is REQ-MC-006 and safety-audit item 10. Tests establish
ranked function contracts and real synchronous Mutex callback lifetimes.
Unsupported manual-guard, dynamic/imported-effect and exception-manifest
boundaries must reject; they are not certified by the supported tests.

## Shared SSpec interface

Use `check_lock_level_source(source)`,
`expect_lock_level_error(source, code)` and `expect_lock_level_success(source)`.
Scenario steps are `step("Declare ranked lock scopes")`,
`step("Compile the acquisition sequence")`, and
`step("Check the lock-order diagnostic")`. Helpers must invoke the production
parser and checker. No source-string search or expected-answer reimplementation
is an executable oracle. Unfinished helpers fail explicitly.

## Cases and traceability

| REQ-MC-006 foundation slice | Required cases |
| --- | --- |
| Annotation contract | zero/max valid ranks; absent/negative/overflow/expression/extra/duplicate arguments; unsupported target; stacked unrelated attributes |
| Order | increasing pass; decreasing fail; equal follows documented policy; independent sibling scopes pass; restored outer rank |
| Calls | one and multiple unannotated wrappers; branching calls; recursive cycle; mutual cycle; forward declaration |
| Name resolution | shadowed function name; same-name methods; function aliases; indirect target; imported target |
| AST traversal | calls in arguments, returns, conditions, collections, match guards, loops, short-circuit branches; nested declarations and callback escape |
| No silent exemption | unsafe block; source-only purported exception; unreviewed metadata |
| Admission | actual native compile rejects invalid source; interpreter rejects before side effects; cache miss/hit parity; sequential-parse reset |
| Physical callback acquisition | actual Mutex ascending/descending nested callbacks, sibling lower-after-release, equal distinct resources, same-resource re-entry, free-wrapper parity |
| Physical boundary rejection | manual lock/try_lock/unlock, mutable/escaping alias, shadowed import/resource, unresolved receiver, callback reference, async suspension |

Executable SSpec:
`test/03_system/app/compiler/feature/static_lock_level_spec.spl`.
Mirrored manual:
`doc/06_spec/03_system/app/compiler/feature/static_lock_level_spec.md`.
These paths cover the REQ-MC-006 slices above. Record the final executed scenario
count from the runner receipt rather than inferring it from source text. The
manual must present readable visible steps and folded executable details, and
state the supported acquisition subset and explicit rejection boundaries.

The helper's production parser/checker invocation proves static admission.
It does not itself execute a Mutex callback or run the native CLI. Preserve
separate evidence for compiled SSpec execution, actual native compile refusal,
and interpreter refusal before side effects. Cache tests must include a stale
or invalid descending graph refused by cached admission, not only successful
round trips of an ascending module.

## Evidence and stop rule

Use an admitted pure-Simple self-hosted producer, record exact producer hash,
source commit, runner mode, native backend, actual executed case count and
exit status. Parser loading or scenario enumeration is not test execution.
Keep compile and execution receipts distinct. Capture diagnostics with source
locations as text/exec evidence. Run each acceptance check once after it passes;
retry only after a code change or new evidence, within the session cycle cap.

Compiler changes additionally require the repository's compiler/lib/MCP/LSP
checks and runtime/native smokes. An unavailable or unstable producer yields
BLOCKED evidence, not a passing static gate. Do not substitute the Rust seed.
