# C37 monomorphization metadata serialization API repair

Issue: https://github.com/ormastes/simple/issues/3048

Base: `c9cb8d6ac95ab64c95dc74c46772d2c60002271e`.
Retained evidence:
`/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-sdn-frontend/mono-deferred/error-groups.json`.
The twelve serialization MIR errors name metadata.spl:406-408,519,534,537,
540-544,574: one unresolved to_bytes call and eleven unresolved concat calls.

## Owner/API diagnosis

The actual text-byte MIR builtin is `.bytes()` in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1977+`.
`std.common.base_encoding.utilities.text_to_bytes_linear` is the existing
pure-Simple byte-copy API at utilities.spl:176-184. It allocates the UTF-8 byte
length and copies `byte_at`, preserving all bytes including embedded NUL.
There is no `.to_bytes` receiver path in this current MIR owner.

The array library declares free `array_concat<T>(arrays: [[T]])`, not the
receiver-style `buf.concat(other)` used here. MIR documents a generated merge
path; it does not dispatch the unresolved concat calls in this evidence.
This is an API mismatch, not justification for a fabricated clone intrinsic
or dropping serialized metadata.

## Narrow source repair

Metadata serialization imports the canonical text converter. A typed local
`meta_append_bytes([u8], [u8]) -> [u8]` appends in input order with explicit
`out = out.push(byte)` and replaces the eleven unresolved concat calls.
Existing serializer push calls already use this returned-array convention.
Four type-string component accumulators now likewise rebind push results, so
tuple/function/union/specialized payload text retains every component under
native value semantics.

No format version, integer width, text representation, category traversal,
dictionary traversal, field order or serializer signature changes. The source
edits are the additional import and serialization section after line 390.
SpecializationEntry.from_key and deferred.spl remain parent-owned and untouched.

## Authored evidence and limits

`test/01_unit/compiler/mono/monomorphize/fixtures/metadata_serialization_probe.spl`
calls production functions and compares every byte to fixed independent META
v1 goldens: 26-byte empty metadata, 155-byte complete five-category metadata,
36-byte specialization entry, 28-byte trait implementation entry. Additional
checks cover u32 little-endian values including all high bits, byte append
with NUL/high bytes, existing prefix bytes, empty text, ASCII/2/3/4-byte UTF-8
plus embedded NUL, type-string component ordering and pointer spelling.
One key per metadata category makes the fixed output independent of dictionary
iteration order while asserting category and field ordering.

`metadata_serialization_bytes_spec.spl` invokes that standalone probe through
`bin/simple`, requiring exit zero, no stderr, and its final success marker.
The golden arrays are literal data, not computed by the serializer under test.

All regressions remain unexecuted. This lane runs no compiler, native build,
or runtime test due the parent disk-space admission gate. Independent source
review and parent pinned affected-file compilation remain required; no runtime
PASS, performance measurement, or production-readiness claim is made here.

Independent reviewer `mono_adapter_review` completed source review against the
exact base with SOURCE-ONLY PASS and no blocker. The reviewer checked the
canonical API definition, byte append semantics, four accumulator rebindings,
and every golden segment (full length 26 + 51 + 10 + 15 + 10 + 43 = 155).
No build/test or native-performance inference follows from that review.
