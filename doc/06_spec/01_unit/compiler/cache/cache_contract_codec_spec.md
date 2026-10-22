# Canonical cache codec and original-form owner qualification

Execution status: **UNRUN**. This is a hand-authored manual for the existing SSpec plus its proposed #3054 qualification cases. No generated runtime evidence is claimed.

Executable: `test/01_unit/compiler/cache/cache_contract_codec_spec.spl`.

The existing cases cover envelope roundtrip, exact corruption/bounds errors, map ordering and duplicate rejection, logical path portability, snapshot identity, public-summary ordering and input isolation, and semantic-read ordering/provider conflict rejection. These remain unchanged.

The additional cases qualify the source forms hidden by #3054 consumer workarounds. They read the actual production `snapshot_contract_v1.spl`, `canonical_cache_codec_v1.spl` and `physical_tld_v1.spl`, parse them with `parse_full_frontend`, and retain their actual parsed record/enum declarations. Unrelated function bodies are deliberately omitted. The records are not reimplemented in fixture strings.

The fixture creates production module surfaces, separately lowers providers and consumer into HIR, then uses the real shared MIR lowering in entry-first order. Every selected provider and consumer HIR diagnostic is retained. It performs no native build or substitute interpretation.

| Scenario | Observable oracle |
|---|---|
| Imported CacheObjectRefV1.schema comparison | Exactly one `Ne` with two i64 operands |
| Original decoded envelope.kind/schema comparisons | Exactly two `Ne` instructions with i64 operands after the Some-or-nil match |
| Original expected_offset != header.payload_bytes | Exactly one `Ne` with i64 operands |
| Original for section in header.sections | Array-shaped field projection at header field 5; i64 section.stored_bytes projection at section field 5; real rt_array_len/get calls |
| Wrong-owner iterable control | Actual CacheObjectRefV1 record iteration remains rejected |
| Wrong-owner scalar coercion control | Actual CacheObjectRefV1 addition remains rejected as unsupported record arithmetic |

Scalar instruction types reject a structural-equality fallback that merely silences a wrong-record diagnostic. The iteration oracle checks the first projected collection shape and the eventual element field index, rather than accepting a diagnostic-free placeholder.

This qualification remains narrower than the whole cache module. It does not prove every original entry, record-array copy receiver, summary Result traversal, native object emission, wire bytes or runtime memory bounds. The separate #3014 range lane is unchanged. Actual SSpec execution requires the root-supplied admitted full CLI; whole-entry HIR/MIR/object qualification remains pending.


## Reopened monomorphic Optional record transport

Source-only cycle 1 fixes the first missing transport boundary for actual `CanonicalCacheDecodeV1.value: CanonicalCacheEnvelopeV1?` and `PhysicalTldHeaderDecodeV1.value: PhysicalTldHeaderV1?`.

The enhanced fixture registers the actual separately parsed/lowered provider field rows with their defining symbol tables, forces distinct provider/consumer symbol IDs, and asserts that an exact payload owner key is retained. It requires the rebinder to return Optional of the exact consumer-owned record. A same-leaf wrong-provider key must return Error and record a fatal diagnostic; Optional(Error) is rejected. A parsed primitive i64? control retains its primitive shape and no nominal ownership key.

The original projection and `match decoded.value: case Some(value)` then feed actual integer comparisons and section-array traversal. Existing four cases remain: direct scalar fields, direct header section loop, true-record iteration rejection and true-record arithmetic rejection. The optional fix does not prove the independent direct-header path or the whole historical row.

No runtime was available for these cases. Metadata/source/patch checks do not establish test PASS. The original range lane, record-array copy receivers, sorting input isolation, full native entries, wire errors and bounded-body qualification remain pending.
