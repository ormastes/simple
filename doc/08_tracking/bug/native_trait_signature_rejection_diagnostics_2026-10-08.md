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

Read-only retained-HIR follow-up: cache file `8d9e73b2d1f4ba51865c675a010014298d5709d56d90911d63e0aeab3d0a3130.hir`
has SHA256 `02a5df935c51c9ec9d83902dd3de6c318a95d14d1585c397456014d8788ae391`
and names actual frontend `ec7f0118a19e2703e3b092ac775237cd93491271cca26ca4724259a8aa082019`.
The bounded read copy and codec-derived decoder live under `build/review/` as
`item5-trait-struct-retained.hir`, `item5-trait-cache-signatures-20261008.py`, and
`item5-trait-retained-signatures-20261008.json`.

Actual method headers agree: trait receiver Named(4), concrete Named(2), both
with empty generic arguments; `current_probe_v1` has one parameter and immutable
receiver, `increment_probe_v1` has receiver plus signed-i64 amount and mutable
receiver. All return signed i64, all nonreceiver parameter mutability is false,
all four are nonstatic instance methods. Symbol 4 is the trait, symbol 2 the
concrete struct, both with the same nonempty module owner. Impl callable IDs
11/12 match the retained functions. This rules out guessing an authored fn/me,
parameter-count or integer-type mismatch from the opaque error. It does not prove
subsequent MIR registration/transport preserved these fields. No unproven ABI
relaxation or speculative registration rewrite is included.
