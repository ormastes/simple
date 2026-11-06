# Physical float optional normalization

Status: OPEN — source repair prepared; executable verification UNEXECUTED.

## Retained failure

Full CLI qualification attempt 3 in
`/home/yoon/dev/simple-bootstrap-qualification-next-20261106`, frozen source
`acdc14ec496`, failed in `app.office.sheets.spreadsheet._parse_f64` with
`E-BACKEND-CRANELIFT-CALL-ABI`: argument 0 to `rt_enum_id` is f64, expected i64.
The function validly returns `office_parse_signed_decimal_f64(s)` (f64) from
an f64? function. Evidence: `build/bootstrap-qualification-attempt3/full-cli.log`.
The pinned producer SHA256 is
`ffe83fd87c69573a1ca93e24134e46bbe754be7dff2de2f0eeefc4cf60c9037a`;
its authority receipt records HEAD `480622a793b67a55ac2c364b313778229c024f75`
and a dirty-source fingerprint. HEAD alone is not an exact source manifest.

## Boundary and repair

`ensure_option_handle` routes values not classified as scalar to
`normalize_option_handle`, which calls the integer-carrier `rt_enum_id` ABI.
`local_is_provably_scalar_payload` previously rejected runtime/extern provenance
before inspecting physical F32/F64 types. Those physical types cannot contain
an integer handle or nil sentinel. Classify them first, allowing the existing
Some constructor to preserve float bits through its bitcast path. Do not cast
the float to an integer and then normalize: float payload bits must not be
interpreted as an absence sentinel. I64 provenance and nil handling are unchanged.

The observed invalid float-to-normalizer edge is established. Which provenance
registration caused this particular spreadsheet call to take it remains unknown.

## Regression and review

Extended `test/01_unit/compiler/mir/optional_scalar_handle_representation_spec.spl`
with actual frontend/HIR/MIR lowering of F32/F64 extern explicit and implicit
returns and ordinary scalar-call returns. Require `rt_enum_new` and `Bitcast`;
reject `rt_enum_id` and `option_norm_raw`. Existing tests retain integer unknown
carrier, nil, and already-optional controls.

Root source review accepted the physical-type invariant and regression design.
`git diff --check` passed. Compiler execution, SSpec execution, native probe,
updated-producer proof, broad runtime gates, and release admission are UNEXECUTED.
Next authorized validation must run this focused regression once, then a bounded
native float-return round trip and the required compiler/runtime gates. A source
patch does not change the currently running pinned producer. Qualification and
planner attempt caps remain in force; no retries are authorized by this note.

## Separate unresolved enum failure

`app.office.sheets.formula._a_value_of` returned i64 where f64 is required for
`CellValue.NumberVal(value: f64)`. Retained diagnostic `simple-aot-diagnostic-VFODnB`
contains only a message, not MIR/CLIF. Typed payload decoding already has an F64
bitcast; missing or incorrect metadata is a hypothesis, not a proven root cause.
No enum or spreadsheet workaround is included.

Fix `023980f9c34` postdates the producer but repairs tuple-literal local type
registration, not the traced enum declaration/payload maps. The inspected enum
summary, provider relocation, lazy declaration, and payload-registration paths do
not call that helper. It is not established that this newer fix resolves the enum
failure. Keep that cause OPEN and independent.
