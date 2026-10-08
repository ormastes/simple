# Native trait signature admission: retain exact rejection reason

Source-only diagnostic successor; native execution UNRUN. The cycle-2 LLVM
`native_trait_struct_copy_borrow.spl` build recognizes both canonical owners but
rejects `NativeCounterProbe` for `NativeValueCounterProbe` with a generic
`incompatible native trait object signature` message. Retained evidence:
`build/item5-trait-enum-layout-cycle2-20261008/qualification/llvm/trait-struct/build.log`.
Constructor owner recovery and Optional payload metadata are separate repairs.

Bounded source trace: `_FlatAstBridge/module_assembly.spl` reconstructs both trait
methods and implementation methods through `convert_decl_method_fn`, retaining
instance/static and fn/me mutability mode. `trait_impl_lowering.spl` supplies the
trait/concrete `current_method_self_type`; `declaration_lowering.spl` supplies the
receiver parameter and preserves explicit return annotations. MIR registration
relocates each parameter/result into the consumer symbol table and retains
per-parameter mutability. That trace alone does not establish which actual
retained HIR field differs; do not infer a particular mismatch or relax admission.

The predicate now reports its first exact failure: object safety, method/signature
counts, missing callable/receiver, receiver owner/mutability, parameter metadata,
resource boundaries, return or argument type keys. Every former rejection remains
a rejection. The boolean helper delegates to the same reason function; conversion
adds the reason to the existing diagnostic prefix, preserving negative-test matching.

The next bounded qualified generation must run the existing positive struct
fixture and signature/mutability negatives. A negative pass requires the expected
method/property reason, not merely an arbitrary compiler failure. No parser,
constructor, vtable layout or callable ABI change is made by this diagnostic patch.
