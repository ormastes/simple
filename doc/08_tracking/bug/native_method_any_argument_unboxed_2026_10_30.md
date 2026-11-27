# Native method Any arguments pass raw scalar words

Status: diagnosed on a real attempt15 executable; isolated compiler repair and
regressions prepared, not executed with a repaired compiler.

The original `sspec_green_spec.spl` computes `40 + 1` and calls
`expect(actual).to_equal(41)`. Attempt15 compiles it successfully, then reports
`Expected <value:0x29>, got 41`. The run is preserved under
`/tmp/attempt15-runner-sspec-off-direct-20261030`.

LLDB evidence collected by the independent fix owner is preserved under
`/tmp/simple-sspec15-matcher-diagnosis-20261030`: `lldb.log` observes raw `0x29`
as expected at both the scalar `to_equal` and `ExpectHelper.to_equal` entries;
`equality.log` observes `rt_native_eq` arguments `0x148` (boxed 41) and `0x29`
(raw 41). The generated lambda calls the scalar matcher, which delegates to
the class matcher. The actual arithmetic and assertion are correct.

HIR `lower_param` lowers an unannotated non-default value parameter to `Any`.
Function lowering marks Any parameters as RuntimeValues. Free-function
arguments already call `box_runtime_value` for that declared type, but common
method argument lowering handles scalar Optional and scalar payload conversion
without an Any branch. Both resolved instance calls and scalar trait calls use
this helper. Consequently the literal expected value crosses the native method
boundary untagged and the callee compares/renders it as though it were tagged.

Add the existing `box_runtime_value` conversion for an admitted positional
Any parameter. Its RuntimeValue guard preserves already-tagged forwarding;
do not shift tagged input again or change comparison semantics to accept raw
and tagged words ambiguously. Typed scalar parameters remain raw.
Both canonical trailing-default lanes also box a default expression when its
admitted parameter is explicitly Any; omitted typed defaults remain raw.

Verification targets:

- `test/fixtures/compiler/native_method_any_arguments.spl`: no SSpec; free
  function controls, class and scalar trait methods, lifted callback, equal 41
  versus unequal 42, explicit/untyped Any, tagged forwarding, bool/text/float,
  omitted Any defaults and typed defaults.
  Expected exit zero and `METHOD_ANY_ARGUMENTS_PASS`.
- `test/01_unit/compiler/mir/method_call_any_arg_boxing_spec.spl`: actual
  parsed HIR/MIR in resolved and unresolved instance lanes; one integer/float
  boxing call and zero extra boxes for tagged forwarding or typed slots.
- `test/fixtures/compiler/method_any_sspec_equal_spec.spl`: one real native
  assertion must pass. `method_any_sspec_unequal_negative.spl` must produce
  exactly one real assertion failure, expected 42 versus actual 41.

Declaration-repository default artifact execution remains pending. The existing
`declaration_default_binding_spec.spl` harness deliberately has no final-stage
seals and tests binder mechanics; it cannot honestly qualify the actual
`pad_declaration_default_call_args_v1` artifact-loading route. The mirrored Any
conversion there is source-reviewed only until an admitted repository with a
real default artifact is available. No archive authority is manufactured for a
test. Full-HIR omitted-default lowering has the executable regression above.

## Explicit named-argument admission limit

`lower_method_call_arg` previously returned early for `arg.has_name`. Its interface receives
only positional parameter types, not admitted parameter names, and callers
walk explicit arguments in source order. This repair does not infer a declared
slot from that order for named arguments. It now rejects a named argument when
the admitted method signature contains Any, with a fatal declared-parameter-
binding diagnostic. The reordered named fixture
`test/fixtures/compiler/native_method_any_named_negative.spl` and parsed MIR
regression require that refusal. This avoids silently emitting an unsafe raw
Any word or boxing a typed parameter based on the wrong source-order index. A proper
follow-up must bind names to the exact method declaration, reject duplicates or
unknown names, preserve evaluation order, then apply slot coercion. This is a
concrete remaining compiler gap; this repair qualifies refusal, not named-
argument support. Existing named typed-only behavior remains outside this fix. Do not
silently annotate user tests or box their expected values as a workaround.

Unknown signatures also remain outside this qualification: the legacy
trait-object `lower_trait_receiver_method_call` path lowers arguments with an
empty parameter list before choosing an implementation. It needs a separate
declaration-first ABI repair. The scalar trait path exercised here selects its
actual implementation and declared parameter types before argument lowering.
