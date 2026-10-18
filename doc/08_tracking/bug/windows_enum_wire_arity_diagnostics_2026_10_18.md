# Windows enum-wire rejects seed-produced Array payloads

Status: rebuilt-producer diagnostic and exact linked-owner attribution observed;
narrow Pure-Simple repair authored. Rebuilt-producer, native-control and full
core verification of the repair remain pending.

## Observed failure

The frozen bf2 Windows bootstrap linked producer SHA256
`ec76686e5b93e67a0b7b68024f1787924c60d4b63fa3d3997a1d6b507e9ec02e`
after compiling 3 modules and reusing 1359. Its normal-cache, BOOTSTRAP0
`p2_add` gate failed with `RT-E-HIR-BLOB-DECODE`, with one codec-refused store
and no successful stores. This is not an admitted compiler.

One bounded Hello diagnostic using the supported
`SIMPLE_HIR_CODEC_ROUNDTRIP=1` returned exit 1, quiescent 1, peak RSS
2564528 KiB, and `ok=false stable=false bytes=0` with reason
`enum wire tuple arity mismatch`. Retained evidence is under
`D:/dev/simple-smux-next-20261017/build/smux-astra-ec766-hello-trace/`:
`hello-build.stdout.log`, `hello-build.stderr.log`, and `hello-build.job.env`.
The diagnostic flag changes the successful roundtrip path; this attempt is
not normal-profile Hello qualification. Its terminal shard row was
`PASS/UNCACHED`, recording the codec-refused cache contract rather than a
successful cache store.

## Attribution and diagnostic change

The diagnostic source was frozen as `58c2a34b106af1ab0abbf5e2c353845805f9e951`.
Its producer `b09cd33730f1fca82bc6440cd59883a11bbaa3dd6a0f79a2347d6a0bb89ece88`
linked after 3 compiled / 1359 cached modules, then failed normal `p2_add`
admission. One new-producer ROUNDTRIP1 Hello diagnostic returned exit 1,
quiescent 1 and peak RSS 2937828 KiB. Its encode refusal reports:
`owner=1050503435 variant=2375492728 expected_arity=2 index=1 actual_arity=-1`.
Logs, receipt and an immutable rejected executable are retained under
`build/smux-astra-enum7-hello-trace` in the NEXT worktree.

Astra and root independently reproduced the declared emitter hashes: the
qualified name `compiler.20.hir.hir_types.HirTypeKind` yields owner 1050503435,
and the Rust string hash of `Int` yields discriminator 2375492728. Provenance:
`native_project/imports.rs` and `mangle.rs` preserve the numbered declaring
namespace; `codegen/shared.rs:21` derives the owner; `llvm/functions.rs` derives
the low-32-bit variant hash. This identifies `HirTypeKind.Int`, whose generated
scalar-boolean encoder expects arity 2 / slot 1. Runtime tuple inspection returns
-1, meaning its payload is not recognized as a tuple by that linked owner.
The exact linked-owner analysis below subsequently established the
constructor/validator contract mismatch. Removing the arity check is not a
repair. No normal Hello or product executable passed with this producer.

`hir_codec_roundtrip_selfcheck` returns before decode when encoding yields an
empty blob; it obtains the reason from a second encode pass. The observed
reason therefore comes from `enum_wire_nil_slot`, not nil restoration.
Generated `HirTypeKind.Int` uses arity 2 / boolean slot 1, while
`HirExprKind.StringLit` uses arity 2 / text slot 0. Hello contains both an
explicit `i64` return type and a string literal; types can be visited before
the body. These were the initial candidates before the richer diagnostic
identified `HirTypeKind.Int`. The `Call` variant itself does not use this boundary.

The encode-side mismatch now retains its prefix and appends the validated
enum owner/discriminant, caller-declared arity/index, and observed runtime
tuple length. Each metadata value is read once. Formatting occurs only on
the refusal path. Existing identity, range, exact arity, and restoration
allocation checks remain in force; there are no new raw casts.
Enum IDs are runtime identities, not a promise of human-readable schema
names. The observed identifiers above were mapped through the declared
emitter algorithms before attributing the failure to `HirTypeKind.Int`.

## Exact linked-owner proof and repair

The immutable b09 PE matches retained native cache object
`629c6e5d98b0a390.o`: all 1180 section bytes outside relocation slots match
at RVA `0xE796F0`. Older object `c3e1e2e4e5bee71e.o` does not match.
The encode-side `rt_enum_payload` call at RVA `0xE79735` resolves to
`0x102BEE8`, matching the Rust runtime cgu.05 archive member. The
`rt_tuple_len` call at `0xE79794` resolves to Rust cgu.12 code at `0xFE9D27`.
Its typed-pointer helper at `0xFDE03F` checks heap type 4 (Tuple), excluding
the otherwise identical String/Dict length routines. Restoration calls the
same tuple-length owner. Rust `rt_array_len` matches RVA `0xFE399F` and its
helper at `0xFDE02E` checks heap type 2 (Array).

The archive is the matched retention5 stage3
`stage2-runtime-authority/simple_native_all.lib`. Its SHA256 and binary
SHA256 are pinned in `build/smux-astra-enum7-hello-trace/linked-owner-proof.json`
in NEXT. `enum-wire-linked-calls.json`, `enum-wire-object-index.json`, and
`linked-owner-review.md` retain the caller mapping and method. No compiler
execution or live payload-memory inspection was used for this proof.

At frozen source `58c2a34b106af1ab0abbf5e2c353845805f9e951`, Rust seed MIR
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs:720-811`
builds multi-field enum payloads with `rt_array_new`/`rt_array_push`.
Rust runtime `collections.rs:2664-2665` permits Array payload reads through
`rt_tuple_get`, while `rt_tuple_len` at2692 requires Tuple. The new boundary's
tuple-only length check therefore rejects a supported constructor representation.
This identifies a contract defect without claiming all unrelated aggregate
corruption is resolved. Remote `cea4130f2f8` still has the same boundary;
its refused-validation-blob workaround does not repair this representation.

The private Pure-Simple `enum_wire_multi_payload_len` now tries tuple length,
then runtime-validated array length only after tuple rejection. Encode and
restoration's original prototype use it only for declared arity greater than
one and still require an exact length match. Rust array validation proves
registered ownership and Array kind; wrong kinds return -1 and small sentinel
words return 0. C `rt_array_len` validates registered ownership, Array kind,
and len/cap bounds through `rt_core_as_array`, returning 0 on rejection.
Neither rejection result can satisfy arity >=2. Global tuple APIs are unchanged.

Restoration still allocates a private tuple, checks it strictly with
`rt_tuple_len`, copies through the existing `rt_tuple_get`, and replaces only
validated slots. Original enum identity and payload remain immutable.
Arity-one payloads, including a tuple as one field, bypass collection-length
inspection. No shape casts, forged enum identity, or host-access APIs were added.

## Focused control and pending verification

`test/04_smoke/enum_wire_boundary_native.spl` uses a real three-field `Row`
constructor and deliberately declares arity 2 to the encode boundary. It
requires refusal with the original prefix, owner and discriminant obtained
from runtime introspection of that typed constructor, expected arity 2,
index 1, and actual arity 3. It does not assume ordinal variant tags.
A new real two-field
`Pair(text, bool)` checks both slots with false and true, and pattern-matches
the original text and boolean values. Existing restoration, invalid-index,
single-payload, and tuple-as-one-payload controls remain. `IntFields(64, true)`
checks the actual integer and boolean values, restored tuple length, nil slot,
unchanged original, and preserved runtime enum identity. Scalar-payload
negative controls reject a false multi-field schema; encode controls also
reject negative/out-of-range indices. Row restoration checks tuple length 3.

These controls use the actual constructor representation of their selected
producer. Pure-Simple `switch_operators_calls.spl:4810` emits multi-field
tuples; the Rust bootstrap seed emits arrays. Therefore a native fixture run
must not be labeled Array-to-Tuple proof merely because it constructs Row.
The rebuilt compiler's own canonical HIR gates exercise real seed-produced
Array-backed `HirTypeKind.Int`; record that coverage separately only after
observing the new producer's gates. No test-only raw Array clone is used.

The diagnostic compiler rebuilt and its refusal was observed as recorded
above. The native control and general tests remain unexecuted. After a rebuilt
producer passes normal Hello, compile and execute this existing native smoke
fixture with its matching runtime; require exit 0 and exactly
`ENUM_WIRE_BOUNDARY_PASS` plus newline, with empty stderr. Preserve the
producer/source/runtime identities and output. Before admission, collect the
original failing gate's richer diagnostic without weakening its refusal.
General runtime/core verification and production readiness remain pending.
