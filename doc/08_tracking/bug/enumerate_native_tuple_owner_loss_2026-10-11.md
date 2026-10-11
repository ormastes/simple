# Native tuple projection loses record and container ownership

Status: source repair candidate; native qualification pending. This change is
not included in the running bootstrap source 0e0287094ba.

The tuple-layout repair a94873fdac9 converts runtime tuple objects into native
tuple aggregates. It rejects every nonprimitive enumerate element because a
fresh tuple-field local has no `struct_value_syms` record owner. Removing only
that rejection is unsafe: `item.hi` can fall through to field zero. Actual
compiler callers include linker/link.spl (SmfReaderImpl), linker/mold.spl
(ResolvedObject), and variance_types.spl (type arguments).

## Repair contract

The native tuple field retains its actual MIR representation. For enumerate,
an existing array element's name-keyed owner is retained as the existing
Opaque(owner) record-handle type; this avoids transporting module-local symbol
identities across an array/tuple boundary. Primitive representations remain
unchanged. Runtime handle fields pass through without integer/float decoding.

At native tuple projection, recover record names from Opaque(owner) or the
canonical Struct symbol resolver. Restore runtime-array and runtime-dictionary
markers for container fields; retain nested array record-element ownership.
Use the native tuple's stored MIR field type even when an HIR annotation exists:
the HIR text lowering may have a different ABI. Do not decode fields twice.

No new mutable provenance map is introduced: the tuple's existing MIR field
types carry the owner, and established per-local maps are populated at the
projection. Their current function reset/transient ownership lifecycle applies.

## Required evidence

The updated MIR spec requires zero fatal diagnostics, field indices [0,1,1]
for enumerated and dictionary-valued two-field records, and runtime-array
dispatch for nested arrays. It replaces the unsupported-struct expectation;
rejecting legitimate records no longer counts as passing.

Native fixture: test/fixtures/bootstrap/enumerate_record_owners/main.spl.
Expected stdout is the adjacent main.expected and exit must be zero. The
record first fields deliberately differ from the second fields so selecting
field zero cannot accidentally pass. Require strict LLVM and Cranelift
build/execute from a compiler containing this repair. Primitive tuple fixtures
must continue passing. Imported/generic record method dispatch and aliasing
remain explicit review/qualification cases; no complete-feature claim yet.

Source whitespace checks passed during preparation. No self-hosted source
regression or native product test has run for this candidate. Existing seed
MIR checks on the predecessor are not acceptance evidence for these edits.

Canonical bug database reconciliation remains pending until a qualified
runtime is available. This report contains no runtime-workaround claim.
