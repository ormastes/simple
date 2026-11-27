# `Option<T>` loses T for every structured, non-callable inner type

- id: option_generic_inner_collapses_below_named_base_2026_10_20
- status: open
- found: 2026-10-20, while writing the prevention spec for PR #3914
  (native_optional_fn_payload_binding_arity_mir_2026_10_20)
- owner: frontend (flat type parser)

## Defect
`parser_parse_type_impl` (`src/compiler/10.frontend/core/parser.spl`, `type_name == "Option"`
branch) registers an `Option<T>` inner tag only when
`inner_type >= TYPE_NAMED_BASE or is_function_tag(inner_type)`. Every other structured tag is
interned below `TYPE_NAMED_BASE` (10000): Dict 1000, Result 2000, Tuple 3000, array 4000,
reference 7000, pointer 8000 (`src/compiler/10.frontend/core/types.spl`). Those fall through to
bare `TYPE_OPTION`, which the bridge turns into an argless `Option` and HIR lowers to
`Optional(Any)` (`20.hir/hir_lowering/types.spl`, `name == "Option"`). The postfix spelling
`(fn(..) -> R)?` takes the named-type postfix branch and loses the callable the same way.

## Evidence (producer8, `compile --format=smf`, 2026-10-20)
- `Option<[i64]>` field, `if val xs = h.xs: for x in xs` and parameter form -> `for-in over
  non-array iterables is not supported by native codegen yet (#143) (collection mir type: Tuple`;
  `h.xs.unwrap()` then `for` -> same, `collection mir type: I64`.
- `(fn(text) -> i64)?` field, `if val f = h.cb: f("x")` -> `dynamic callable requires proven arity
  before indirect emission`.
- Pass: `[i64]?`, `Option<fn(text) -> i64>`, `Option<Dict<text, i64>>` (`.len()` is dynamic on Any),
  `Option<(i64, i64)>` (`.0` is dynamic on Any).
- Fixtures: `C:/dev/simple-bootstrap-storage/hir-specs-fx/src/app/hx/i*.spl`, runner `run.sh`.

## Fix direction
Register the inner tag for every non-primitive inner (drop the `>= TYPE_NAMED_BASE` gate, keep
the dedicated I64/F64/TEXT/BOOL tags), and route `(<type>)?` through the same registration.

## Specs
- Prevention (in-development): `test/01_unit/compiler/20.hir/bootstrap_regressions/option_generic_inner_type_gaps_spec.spl`.
- Passing sibling (#3914 reproducer + working shapes): `test/01_unit/compiler/20.hir/bootstrap_regressions/option_generic_inner_type_spec.spl`.

## 2026-10-28 attempt-5 evidence and narrow repair

The exact phase2 compiler `8d21317328ccb2b32ba707d2485c3c8ca6c4d02592952537e7754a6d006cb116` rejects the stage3 `compiler.backend.interpreter_calls` interface at `InterpreterBackendImpl::try_call_builtin`, whose source declares `Option<Result<Value, BackendError>>`. The retained HIR symbol 615 actually has `Function([Named(548), text, Array<Named(51)>], Optional<Any>)`; Value still resolves as Named(51) in the argument, and the entire nested Result is absent. The guarded RTI converter correctly reports E-RTI-007. Evidence: `/tmp/simple-luna-direct-phase3-20261028/attempt5`, frozen source `source-aeae` at aeae829519e.

A minimal no-import `nested_result.spl` compiled and printed `42` with that same compiler, but its retained symbol metadata is also Optional<Any>, rather than the declared Optional<Result<i64,text>>. Execution success does not prove signature preservation: the current ownerless-unqualified-function ABI fallback masks that metadata defect. The independent metadata assertion is RED and hash-bound in `/tmp/simple-option-composite-tdd-20261028/metadata-red.sdn`; raw executable PASS remains separate.

A separate parser-only native test driver calls the actual parser/type registry across Result, array, Dict, tuple, and working controls. Its baseline compiler crashed with SIGABRT in native codegen of `compiler.frontend.core._AstExpr.accessors` after 276 seconds; eight modules had reached the codegen queue. This is BUILD_FAIL, not a semantic RED or a passing test. Its watchdog ended quiescent with zero observer errors; logs and caches are preserved under `/tmp/simple-option-composite-tdd-20261028/red`. No identical retry or seed-tooling substitution was made.

The proposed source repair retains the four dedicated primitive Option tags and registers every other parsed inner tag, without the numeric named/callable gate. Exhaustion emits an explicit parser error rather than successful erasure. Tests extend the existing prevention owner with nominal Result payloads, postfix Result control, actual Any preservation, and registry-exhaustion rejection with shared-pool restoration. The RTI Any rejection is unchanged. Green verification remains OPEN; postfix callable gaps and general compiler admission are not claimed fixed.

## 2026-10-28 landing verification: independent LLVM route blocked

A single reserved LLVM component-build window tested source f512a01c535 without repeating the failed Cranelift invocation. It used the exact 8d phase2 compiler, AArch64 target, unchanged e43 runtime authority, one thread, isolated output/cache, an enforced 8 GiB process-tree RSS limit, and a 300-second deadline. The requested backend was LLVM in both parent and worker argv; installed LLVM tool hashes were retained. This is not a full compiler build or an ABI-equivalence claim.

The guard ended the compile with `status=rss-cap-exceeded`, exit 88, after 284.253 seconds: peak 8,418,788 KiB against 8,388,608 KiB. No binary or executed assertion exists. The receipt reports quiescent=1 and observer_errors=0; the reservation was released only after that proof. No fallback retry or cap increase was made. Machine-readable evidence and hashes are in `phase2_native_llvm_core_parser_harness_rss_cap_2026_10_28.sdn`; raw logs remain under `/tmp/simple-option-composite-tdd-20261028/llvm-green`. Bug database reconciliation is pending because no qualified bug CLI is available.

PR #5154 still cannot land: actual changed-parser GREEN, authored unit execution, generated-manual verification, and the compiler/lib/MCP runtime and smoke gates remain unrun. The expected qualified full CLI remains unavailable. Successful structural CI checks and source review cannot replace those execution gates.
