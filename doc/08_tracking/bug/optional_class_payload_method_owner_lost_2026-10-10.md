# Optional class payload loses MIR method owner

`test/fixtures/compiler/optional_class_payload_method.spl` constructs an
Envelope containing a Reading with value 42 and calls
`envelope.reading.?.read()`. Before the repair, HIR passes but MIR fails with
`unresolved method call: read`. The `ExistsCheck` MIR lowering recovers the
declared optional payload owner for structs only; classes fall through and
lose the identity used by method dispatch.

The candidate uses `mir_class_identity` for class payloads alongside the
existing struct path. The unchanged fixture compiles and executes on ARM with
exit 0 and exactly `OPTIONAL_CLASS_PAYLOAD_METHOD_PASS\n`. Evidence is
`build/native_probe/explicit-call-types/optional-class-repair-result.json`.
The same fixture emits a valid EM_RISCV (243) object with the repaired
producer (`optional-class-riscv.o`); no RISC-V runtime claim is made.

The real MC/DC closure now passes HIR, monomorphization and MIR across 13
modules. Cranelift AOT then rejects four modules because imported global
declarations and non-scalar static initializers are unsupported. Evidence is
`mcdc-class-arm.log`. This is not full native MC/DC or bootstrap admission.
The LLVM route also rejects the closure: it emits pointer-typed integer nil
constants such as `%l22 = add ptr 3, 0`, which `llc` rejects. The retained
diagnostics in `mcdc-llvm-arm.log` identify the affected modules and `.ll`
files. The class-owner repair does not solve this separate representation bug.
