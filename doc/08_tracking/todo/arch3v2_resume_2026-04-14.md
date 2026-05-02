# ARCH3v2 Resume — Task #38 (2026-04-14)

## Status: BLOCKED — premise mismatch

## Task as given
Fix interpreter regression where `Architecture.X86_64` works in struct-field-init
but `Architecture.X86_64().some_method()` (method-call-receiver position) fails,
mirroring "ARCH2's fix" to `interpreter/expr/field.rs` or `struct_init.rs`.

## Findings
1. **No prior ARCH2 fix found.** `git log --oneline -20` shows no commit
   referencing `Architecture`, `static_fn`, struct-field-init, or ARCH2.
   No log file at `doc/08_tracking/agent_logs/arch2*`.

2. **Grep for `static_fn|Architecture|X86_64` in
   `src/compiler_rust/compiler/src/interpreter/` returned 0 matches.**
   The interpreter never references an `Architecture` type by that name.

3. **No existing spec** at
   `test/unit/compiler/interpreter/architecture_static_accessor_spec.spl`
   (the file the task says to mirror).

4. **Existing spec** `test/feature/usage/architecture_spec.spl` uses
   `TargetArch.AVR` / `TargetArch.X86_64` (enum variants, not static
   functions). It already has an explicit NOTE:

   > parse tests use parse_target_arch() free function wrapper
   > instead of TargetArch.parse() static method (not supported in interpreter)

   i.e. static method calls on type identifiers (`TargetArch.parse()`) are
   **documented as unsupported** in the interpreter. That is the regression
   area, not a recent regression introduced by ARCH2.

5. **Relevant interpreter code** still lives at
   `src/compiler_rust/compiler/src/interpreter/expr/calls.rs:37` (MethodCall
   arm) and `:378` (EnumType field-access arm). EnumType handles
   unit-variant construction and enum methods, but there is no pathway that
   resolves `EnumName.Variant()` as "call a static fn named `Variant` on
   impl EnumName" — consistent with the documented limitation.

## What a real fix would need
- Locate (or add) an `impl Enum { static fn Variant(...) -> Self }` registry
  lookup in `calls.rs` when the method-call receiver is `EnumType`.
- Alternatively, in the MethodCall arm, evaluate the receiver; if result is
  `Value::EnumType { enum_name }` and the *method* being called is a static
  fn in `impl_methods[enum_name]`, dispatch it with no `self`.

## Suggested next-agent steps
1. Confirm with user whether the target enum is truly named `Architecture`
   or `TargetArch`, and whether `Architecture.X86_64()` is expected to call
   a static fn or construct a unit variant.
2. If static-fn-on-enum semantics are desired, extend the `EnumType`
   handling in `calls.rs` MethodCall arm (~line 37) to look up
   `impl_methods.get(enum_name)` and dispatch matching-name static fns.
3. Add spec first: `test/unit/compiler/interpreter/architecture_method_call_spec.spl`.

## No files modified in this session.
