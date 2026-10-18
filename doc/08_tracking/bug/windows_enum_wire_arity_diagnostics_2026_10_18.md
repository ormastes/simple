# Windows enum-wire encode refusal lacks payload context

Status: diagnostic and native controls authored; execution pending a rebuilt
Pure-Simple producer. The underlying representation failure is unresolved.

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

`hir_codec_roundtrip_selfcheck` returns before decode when encoding yields an
empty blob; it obtains the reason from a second encode pass. The observed
reason therefore comes from `enum_wire_nil_slot`, not nil restoration.
Generated `HirTypeKind.Int` uses arity 2 / boolean slot 1, while
`HirExprKind.StringLit` uses arity 2 / text slot 0. Hello contains both an
explicit `i64` return type and a string literal; types can be visited before
the body. The actual failing enum and linked runtime representation remain
unproven. The `Call` variant itself does not use this scalar boundary.

The encode-side mismatch now retains its prefix and appends the validated
enum owner/discriminant, caller-declared arity/index, and observed runtime
tuple length. Each metadata value is read once. Formatting occurs only on
the refusal path. Existing identity, range, tuple-shape, and restoration
checks remain in force; there are no raw casts or permissive fallback paths.
Enum IDs are runtime identities, not a promise of human-readable schema
names. The next retained diagnostic must map them before attributing an ABI
defect to a particular enum.

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

No compiler or test execution was performed for this change. After a rebuilt
producer passes normal Hello, compile and execute this existing native smoke
fixture with its matching runtime; require exit 0 and exactly
`ENUM_WIRE_BOUNDARY_PASS` plus newline, with empty stderr. Preserve the
producer/source/runtime identities and output. Before admission, collect the
original failing gate's richer diagnostic without weakening its refusal.
General runtime/core verification and production readiness remain pending.
