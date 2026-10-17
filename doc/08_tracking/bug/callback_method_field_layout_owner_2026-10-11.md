# Callable field fallback must use the declaration layout

Compiler defect: https://github.com/ormastes/simple/issues/2980 (open).

C35 `ea9224a83a64cd20e21d013cf1c2652f891999c4` runner MIR reports fifteen
unresolved calls to declared function-valued fields. The method recovery path
in `method_calls_literals.spl` normalizes its receiver to a method identity
(`module.Record`), but the late callable-field fallback used that same string
to query `struct_field_order`, registered under `module::Record`. The failure
affects real environment and runtime-HAL callback ports; two downstream text
method failures follow a lost callback return type.

The repair retains method/trait/custom-owner precedence and separately recovers
the declaration's field layout. It accepts only a declared Function field,
projects it from the already-lowered receiver, and routes it through the shared
`lower_call_with_value` argument/indirect-call path. Receiver effects occur once;
argument coercion, closure dispatch, and result metadata remain shared with
ordinary function-valued calls. An exact declared owner with missing metadata
does not borrow another provider's bare-name layout.

Dependency: this source patch requires the companion generic indirect-call
repair exposing `lower_call_with_value(callee, args, prelowered_callee)` and
rebinding imported Function return owners. It is not a standalone buildable
compiler change until that companion is integrated.

`test/fixtures/compiler/callback_method_field_owner/main.spl` preserves original
direct method syntax on effectful receiver factories. Two imported provider
types share the name Port but place their function fields at different offsets.
Distinct integer results and per-provider receiver/callback counters reject
wrong-owner dispatch, duplicate receiver evaluation, and missing invocation.
Required native result: exit 0 and exact stdout
`callback-method-field-owner: pass\n`. ARM execution and genuine LLVM18 RISC-V
object qualification remain pending a coordinated corrected producer.

The application-level workaround in the separate callback-workaround branch
remains temporary. Its typed identity helpers address the additional generic
indirect-return provenance defect, not this layout lookup alone. Do not close
#2980 solely on source review or object emission.
