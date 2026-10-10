# If-val drops declared Optional trait payload identity

Source-only successor to `64b928640387b9ba95f8cc73e2a431ef0ab1f6f5`; native tests
UNRUN. The retained cycle-2 LLVM trait-class and trait-struct logs report unresolved
`parse_probe_v1` / `current_probe_v1` on Optional payload bindings, independently
of constructor-owner and signature-admission failures.

Parser if-val lowering uses ExistsCheck followed by a nil condition. ExistsCheck
already retrieves the exact Optional inner HIR type, but only retains Float/Bool
metadata on the merged raw payload-or-nil local. Named struct field provenance is
separate; a nominal trait has no concrete field layout to recover from that path.
The binder therefore loses the trait owner needed for an indirect slot call.

Retain Named/DynTrait metadata only when `native_trait_owner_for_type` proves the
declared type is a nominal trait. Keep the raw sentinel representation,
Some/None branching and scalar decode unchanged. No method-name, raw integer or
single-implementation inference is introduced. Isolated wrappers remain outside
this admission. Ordinary let binding already copies the local type metadata.

`native_trait_optional_owner.spl` requires real native two-owner parameter/field
unwrap and nil-branch checks. Existing negative signature/mutability/missing-impl
fixtures remain unchanged. No compiler generation or execution was performed for
this source-only fix; constructor/signature causes must be qualified together in
the parent's bounded generation after review.
