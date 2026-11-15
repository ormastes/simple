# Checked static AOP placement V1

Status: implemented; focused actual-MIR native projection passed; full compiler
import/CLI acceptance remains pending.

The frontend's `MatchedAdvice.form` previously disappeared when constructing
`AdviceCallInfo`. The MIR consumer selected insertion solely from join-point
kind, so execution after-success/error advice became an entry hook. The actual
producer now preserves a required `form: AdviceForm` third field. Repository
uses are the producer, MIR consumer, tooling reexports and tests; no persisted
wire codec was found. Source clients constructing this compiler DTO must supply
the field; there is no guessing of old positional values.

`AspectPlacementKindV1` and `StaticAspectPlacementV1` live with MIR injection;
`Placement` accepts an actual `MirFunction`. The checked API calls the existing
injectors, not a second weaver. The actual driver consumes its `Result`, emits a
compiler diagnostic on refusal and does not count failed insertion. Callers
must stop execution/publication when the compiler context contains errors;
that pipeline gate is a coordinated separate change.

| Join point | Form | Placement |
|---|---|---|
| Execution | Before | Declared entry block |
| Execution | AfterSuccess | Before ordinary `Ret` terminators |
| Execution | AfterError | Before `Abort` terminators |
| FunctionCall / VariableAssignment | Before / AfterSuccess | Before / after the original instruction |
| Instruction error, decision, condition | Any | Refused pending precise edge semantics |
| Any | Around | Refused: the retained legacy pre-hook does not implement proceed |

“After success” retains the existing ordinary-return interpretation; it does not
inspect returned error values. Instruction after-error is unavailable. Around
remains a reserved closed enum variant and a noncacheable form; dynamic around,
value capture and function replacement are not introduced.

All function-context selectors, including bare names and `*`, match Execution
only. Explicit `join:call` and `join:assignment` remain instruction selectors.
The current shared frontend token scanner is reused.

Requests are validated against the original function before rewriting. Invalid
coordinates and missing entry blocks fail explicitly. Instruction edits run in
descending original-coordinate order, after-insertion before before-insertion
at the same anchor, with reverse insertion order preserving source advice
order. Exit appends then entry prepends avoid shifting instruction coordinates.
The public placement method also checks directly constructed requests. The
compatibility `apply_weaving_result` unwraps a checked failure rather than
silently returning an uninstrumented function; compiler code uses the checked
API for an ordinary diagnostic.

Executable specs: `test/01_unit/compiler/mir/aop_static_placement_v1_spec.spl`.
Planned native projection retains actual MIR records and existing injectors,
checks producer form/kind propagation and real resulting instruction order,
and includes unsupported/invalid requests. Full compiler import/pipeline tests
remain distinct from this focused projection.

## Native evidence (2026-11-14)

`/tmp/aspect-mir-placement-probe-20261114` records a pure-Simple Stage 2/core-c
compile and run, both exit zero. The projection includes 191 actual transitively
referenced compiler/library records, including the complete actual `MirFunction`,
and exact production producer/selector/placement/injector functions. There are
no substitute MIR records or mocked injection functions. It checks execution,
bare-name and wildcard selectors on a function with instruction join points;
form propagation; real resulting MIR entry/success/abort placement; original
instruction anchors and same-slot order; four unsupported/invalid requests;
and direct forged-coordinate rejection.

The first fixture compile rejected `Ret(nil)` as an optional enum payload; the
fixture and spec now use explicit `Ret(None)`. No production workaround was
introduced. The second compile and native execution passed within the bounded
120-second/2-GiB lane. Exact sources and binary hashes are retained in the
fixture receipts. This is projected production execution, not proof of whole
compiler import closure or the complete CLI pipeline. The coordinated caller
error fences landed separately through PR #9177.
