# Windows enum-wire encode refusal lacks payload context

Status: rebuilt-producer diagnostic observed; native controls and full core
verification pending. The underlying representation failure is unresolved.

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
This does not establish whether construction, transport or mixed runtime
ownership caused the incompatible representation. The next probe must compare
the actual linked enum/tuple owners and emitted constructor payload. Removing
the arity check is not a repair. No normal Hello or product executable passed.

`hir_codec_roundtrip_selfcheck` returns before decode when encoding yields an
empty blob; it obtains the reason from a second encode pass. The observed
reason therefore comes from `enum_wire_nil_slot`, not nil restoration.
Generated `HirTypeKind.Int` uses arity 2 / boolean slot 1, while
`HirExprKind.StringLit` uses arity 2 / text slot 0. Hello contains both an
explicit `i64` return type and a string literal; types can be visited before
the body. These were the initial candidates before the richer diagnostic
identified `HirTypeKind.Int`. The linked payload construction and transport
cause remain unproven. The `Call` variant itself does not use this boundary.

The encode-side mismatch now retains its prefix and appends the validated
enum owner/discriminant, caller-declared arity/index, and observed runtime
tuple length. Each metadata value is read once. Formatting occurs only on
the refusal path. Existing identity, range, tuple-shape, and restoration
checks remain in force; there are no raw casts or permissive fallback paths.
Enum IDs are runtime identities, not a promise of human-readable schema
names. The observed identifiers above were mapped through the declared
emitter algorithms before attributing the failure to `HirTypeKind.Int`.

## Focused control and pending verification

`test/04_smoke/enum_wire_boundary_native.spl` uses a real three-field `Row`
constructor and deliberately declares arity 2 to the encode boundary. It
requires refusal with the original prefix, owner and discriminant obtained
from runtime introspection of that typed constructor, expected arity 2,
index 1, and actual arity 3. It does not assume ordinal variant tags.
A new real two-field
`Pair(text, bool)` checks both slots with false and true, and pattern-matches
the original text and boolean values. Existing restoration, invalid-index,
single-payload, and tuple-as-one-payload controls remain.

The diagnostic compiler rebuilt and its refusal was observed as recorded
above. The native control and general tests remain unexecuted. After a rebuilt
producer passes normal Hello, compile and execute this existing native smoke
fixture with its matching runtime; require exit 0 and exactly
`ENUM_WIRE_BOUNDARY_PASS` plus newline, with empty stderr. Preserve the
producer/source/runtime identities and output. Before admission, collect the
original failing gate's richer diagnostic without weakening its refusal.
General runtime/core verification and production readiness remain pending.
