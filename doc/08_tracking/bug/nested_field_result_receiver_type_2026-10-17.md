# Nested field method receivers lose their Result return provenance

Status: narrow source repair and regressions authored; old-producer one-module
failure reproduced. No current-source native execution, compiler admission or
release PASS.

## Original evidence and source mechanism

Frozen product/source `3636b716294` completed HIR for 117 modules under the
Hello-qualified diagnostic f612 compiler, then MIR failed in four modules.
The retained `build/smux-diagnostic-current/smux-build.stderr.log` in
`D:/dev/simple-smux-upstream-20261017` reports unresolved is_err at server line
153 for `client.stream.close().is_err()`. TcpStream.close actually returns
`Result<(), IoError>`; this is not a void-close API mismatch. Its source spelling
remains unchanged.

`enum_match_expr_type(MethodCall)` obtains an unresolved method's return type
from the declared receiver owner, but `receiver_declared_type` only admitted
Var/NamedVar. Thus the Field receiver `client.stream` had no admitted declaration
path. Generic Field recovery there covered only special Result ok/err payloads;
the chained Result fallback only prelowered map/map_err. The canonical predicate
helper correctly refused to guess Result storage from a method name.

The local-stream form at line 160 is not reported, but that absence is not a
standalone execution or MIR PASS. The helper's admitted Var/NamedVar paths
explain the source-level distinction; regression controls test both shapes.

## Repair and isolated ownership

Branch `work/mir-field-result-20261017` starts at fresh remote
`8617a98e3151078d3ad615e555494f9f9ad0340a` in the separate worktree
`D:/dev/simple-mir-receiver-20261017`. The active frozen compiler source and the
other Match/closure conversion lane are untouched.

Add one Field arm to `receiver_declared_type`, delegating to existing
`declared_field_hir_type(base, name)`. Its recursive base query strictly consumes
AST depth. It neither calls lower_expr nor executes a receiver, preserves the
registered HirType, and returns nil when the requested field is unavailable.
Existing Var/NamedVar and declared provider owner lookup remain unchanged.
This does not implement arbitrary generic owner substitution, cross-trait
casting, closure conversion or a method-name fallback.

Astra accepted this pure query plan before source handoff: preserve exact type
and missing-field nil, never double lower/evaluate, and retain the concrete
scope. Astra's final source/test review accepted the scoped patch and fixtures;
its requested HIR-error collection was added to the parsed helper. Matching
producer verification remains required.

## Regressions and qualification

The parsed SSpec at
`test/01_unit/compiler/mir/nested_field_result_receiver_spec.spl` lowers actual
fixture source, checking local/direct/nested Ok/Err predicates, exactly one
close call and Result discriminant per helper, no HIR/MIR errors on positive
controls, and unknown-field rejection.
Its authored mirrored manual is not a generated zero-stub receipt.

The one-module positive native fixture checks the actual predicate truth table,
six total global close effects and two retained effects in each rooted field.
Its expected.stdout is a golden oracle, not execution evidence. The separate
unknown-field fixture must fail compilation instead of borrowing the real
stream field's Result type.

One old-producer diagnostic attempt completed in
`build/nested-field-receiver-diagnostic/`. It uses the exact retained
Hello-qualified `simple-diagnostic.exe`, LLVM backend, one source module, one
worker, cold inventory setting, existing stage2 runtime authority and LLVM-C
import library without a tagged-print shim. Source C includes the already
merged print-alias implementation; if MIR fails, link ownership is not reached
or proven. Input hashes, exact script, logs and 180-second Job receipt are
preserved. A conditional 30-second actual run exists only if compilation succeeds.
The producer predates this compiler patch, so this attempt reproduces the
old failure but cannot validate the new type-query implementation.

Actual outcome: complete, exit 1, quiescent 1, peak RSS 2,140,812 KiB. HIR
succeeded 1/1. MIR reported the direct-field predicates at lines 26/29, nested
predicates at 32/35, and main's rooted-field predicates at 45-48. The local
control at line 23 is not among those errors; it must not be confused with
direct_err at line 29. No executable or semantic counter run was produced.
No identical build was rerun.

The retained HIR capsule key is
`491f116d652c9e2513cd83f1b916b0496388d79c9b51936d6514712e3570fff8.parser-v4.hir`.
Its generated-codec records identify close as Method symbol 10 with
Function(Named Endpoint 0) -> Result<Unit, text>, and the local stream parameter
as Named Endpoint 0. No missing/void declared close return was inferred from a
diagnostic alone. The close call records have Unresolved method resolution and
absent expression types, requiring the declared-owner query. This agrees with
the Field-only missing traversal; it is not evidence for a broader method
signature or trait-dispatch patch. The capsule SHA-256 is
`b2b76e54731868a04e05ee92b02a1a0503177d26074110dfc1afdb0662024d86`.
The observed callsite
metadata are retained in `build/nested-field-receiver-diagnostic/retained-hir-observation.txt`.

Both native backend executions of the repaired matching producer, actual
fixture semantic counts, unknown-field rejection, unit tests, compiler/lib and
MCP/LSP smoke checks and generated zero-stub documentation remain pending.
Provider input/output/cache-read/cache-create usage, comparable cohort average
and ratio: unavailable, not guessed.
