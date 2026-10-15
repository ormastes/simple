# Runner function-field call workaround

Tracked compiler defect: https://github.com/ormastes/simple/issues/2980 (open).

C35 source `ea9224a83a64cd20e21d013cf1c2652f891999c4`, producer
`96d356291fb75d4d81ff72df901fe3328e9e4bbabd4f4e5317382766b7261c4c`,
attempted all 251 runner MIR modules and failed with 15 unresolved callback
field calls plus two downstream `substring` calls. The exact ledger is
`build/native_probe/phase3-whole-20261011-c06/c35-producer-c35-runner/normalized-mir-errors.json`
in the preserved C06 evidence tree. No runner object or executable was produced.

The affected fields are actual function-valued ports, not methods. The MIR
unresolved-method path changes a struct's layout spelling (`module::Struct`)
to its method identity (`module.Struct`), then the callable-field fallback
looks up `struct_field_order` using the method identity. Layout registration
uses the former spelling. This is a static causal lead; the compiler repair
and regression verification remain separate work.

The source workaround explicitly calls each supplied field value as
`(receiver.callback)(arguments)`. The flat parser emits `Call(Field(...))`
instead of `MethodCall(...)` for this spelling. All callback receivers,
arguments, conditions, and invocation counts are retained. No provider is
substituted. The hardware probe result is explicitly typed `EnvAccessRawResult`
so its text fields retain their declared owner after the callback call; both
existing substring operations remain unchanged.

`test/fixtures/compiler/callback_field_explicit_call/main.spl` exercises two
different runtime-selected ports, true and false bool returns, different
integer results, record returns followed by substring, array-held ports, and
all four arena-join fields, and ten callback side effects. Required ARM result: exit 0 and exact stdout
`callback-field-explicit-call: pass\n`. Any unresolved/placeholder diagnostic
disqualifies the artifact before execution. The same fixture can qualify the
later genuine LLVM18 RISC-V object, but that is not claimed here.

The first ARM probe built and linked without placeholders, then exited 14:
bool/integer callbacks and record.status passed, but record text consumption
failed. `arm/check-port.disasm` in C06's `c35-callback-field-workaround` evidence
shows both text fields loaded from field zero at 0x129b58. The record pointer
survives; generic indirect-call lowering loses its declared aggregate owner.
The typed binding alone did not restore it. `lower_call`'s indirect path at
switch_operators_calls.spl:6599 lacks the direct path's return provenance.

A narrow typed identity-return helper now wraps the hardware probe's record
result. It preserves the value and callback count/order, while a direct call
supplies the compiler with the declared result owner. The fixture mirrors that
boundary. This adds temporary call/copy overhead; no performance equivalence
is claimed. Remove the helper when the permanent indirect-call result typing
and layout regression passes. The first typed-boundary fixture at `83ec8208a4e`
passed ARM build/runtime (exit 0, exact expected stdout, six effects) under the
same C35 producer. Evidence is `arm-owner-bound` beside the failed `arm` receipt.

The actual callback-return audit also found two `RtHalArenaJoin` results in
`parallel_executor.spl` whose outcome/trace/error fields are read directly.
Both now use the same narrow typed identity-return boundary. The final fixture
adds two arena callbacks and checks every field, increasing effects to ten.
The `RtHalExactJoin` callbacks in `exact_boundary.spl` and
`process_task_arena.spl` directly inspect only `completed` (field zero); their
remaining aggregate consumption already crosses a declared typed argument or
the enclosing function's declared return boundary. Integer and bool callbacks
remain plain explicit field calls. Final expanded-fixture ARM/RISC-V evidence
is pending; the earlier six-effect PASS does not cover these added cases.
Keep issue
#2980 open until the compiler repair passes its original direct-field-call
regression and affected runner modules.
