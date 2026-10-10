# Optional nil match arms rejected by retained producer80030

Canonical bug: `BUG-MIR-OPTION-NIL-ARM-STALE-PRODUCER-20261010`. Status: OPEN; compatibility workaround for the retained producer. Background owner: pure-Simple MIR enum-pattern lowering / bootstrap producer integration. This is distinct from the existing enum-field receiver bug and Result-versus-Option matching bug.

Producer SHA256: `80030da7da3f15174dc26285389375b19c8f090c29eedb6bded089defaa28071`. Its embedded per-owner source identity is unproven. Two scalar original nil-pattern probes and one `[u8]?` original probe failed with the actual `enum match: unsupported arm pattern` family. Full retained logs were checked; no extra error family was accepted. Do not infer that this binary contains later compiler fixes.

The pure-Simple nil-pattern repair already exists in [8df1d2dfab22df00c1a3e05adcc7f65b30f35ed0](https://github.com/ormastes/simple/commit/8df1d2dfab22df00c1a3e05adcc7f65b30f35ed0); Or-arm repair exists in [a8f778e5650f39dac4edd79552bbdee0294291f2](https://github.com/ormastes/simple/commit/a8f778e5650f39dac4edd79552bbdee0294291f2). Do not duplicate them. Rebuild/qualify the relevant producer, verify the original nil spelling, then narrowly remove the seven markers and restore nil arms in a separate linked recovery change. Actual workaround commit: [940975600b4fef247d9928f67fcf18922b73e349](https://github.com/ormastes/simple/commit/940975600b4fef247d9928f67fcf18922b73e349). This evidence commit is separate from the workaround and the earlier underlying fixes.

This patch changes only seven absence-pattern headers in `BinaryReader.read_i8/read_i16/read_i32/read_i64/read_f32/read_f64/read_string`. Each Some binding, payload expression, return, cast, order and reader-position operation stays unchanged. The first six receivers are optional unsigned integers returned by read_u8/u16/u32/u64; read_string matches read_bytes returning `[u8]?`. Nil constructors remain nil. The existing release repair replacing unresolved is_little_endian extern with a pure function is preserved. Fresh release base `7b45c1e4959bc05af01eb8b212416947195bc4ce` source SHA256 `280eadd46f5ed8219a8327d35d80e79de3f2bfc93741e914a35bb2bd0a53170c` differs from historical original6bf `a04cddb1c1734f7a76b65bd4ffe484bfb9867811a24b496ba777e1537535a6d1` only by that preexisting repair.

Three explicit-None objects were linked through canonical helper74 and ran their real authored mains directly: scalar Some(3)/Some(0)/nil, None-first ordering, and array Some(empty)/Some([0x7f,0x80,0xff])/nil with payload preservation. All three exited0 with exact expected output. This proves those authored criteria, not all reader conversions or the whole compiler. The two scalar compile audits retain their original attribution errors; a separate exact-helper reconciliation records the cause. The boxed supplemental false-missing cache observation is preserved: a274-character path needed the Windows extended-path adapter, whose exact read matched the emitted object. No audit was overwritten into PASS.

The three links used the same idle0895 runtime project/cache:39 retained runtime objects remained unchanged. No explicit cache-hit records were emitted, so actual hit count is UNOBSERVED. A private direct Windows Job collector passed normal-exit, aggregate-descendant RSS-cap and deadline controls before use. Sanity used a128MiB sampled aggregate RSS limit and15-second deadline; link cap768MiB plus256MiB observer forecast. These are sampled limits, not kernel hard-memory limits. No subsecond, native-performance, full-runtime, core-CLI or six-product qualification is claimed.

Original module0424 `src/lib/common/math/ieee754_bits.spl` completed its approved final cycle3 with exit0 and a43,214-byte combined COFF object, SHA256 `5387b85bee67915d16afbb79e885ec64cdd7c978497c9100c82752d404bd18e2`. All nine entry functions are defined. Canonical receipt/log/input audit passed, and an independent extended-path supplement bound all three actual snapshot-source fingerprints to admitted bytes and their cache objects to the combined definitions. The source projection includes the seven-arm workaround and the preexisting release endian repair. Inclusive observed time18.3741786seconds and sampled peak299540KiB are diagnostic observations, not a matched performance comparison. No executable was fabricated for this library entry. All three attempts are consumed; the original failures remain evidence, with no fourth cycle or blanket replay of103 overlapping symptoms. Whole-reader semantics and qualified compiler/core gates remain unproven.

Evidence packet: `build/native_probe/phase3-enum-nil-arm-fix-20261010` (retained local artifacts; not all tracked). SHA256 inventory:

- `request.json`: `85ce27dd6a18ba52a91d9e64d49ceb724438c7400bdf8f77659c802c0aa52aff`
- `retained-helper-and-cause-reconciliation.json`: `2293ad765954ece05e22223915f5852d722ece27629f4d6407f66384da8889b4`
- `boxed-native/request.json`: `7cece927f2ab415cf1c8e40d5793a1c3fb599f1b8e65a62bc61935dcdfcdb8f6`
- `boxed-native/independent-audit.json`: `dc8d5880a2fe3c915e510cafa525a3eb58673a71a79f79798425f558ef7bf88f`
- `boxed-native/boxed-compile-oracles.json`: `1f07bedb2f65dc649c5a1234c51a92fadb29d3ee07c57b875163128c3cbdfe2d`
- `boxed-native/retained-binding-supplement.json`: `4a28958fde1c132da4a3af0954eb52286c2e23d4263996b9350bdde9f21048ca`
- `boxed-native/longpath-cache-binding-addendum.json`: `72e7eebeca681d92d4da1ca7180fbf00f2093ba665c9a76605a012436496453f`
- `semantic-links/request.json`: `5b4180b770da31ae554bdfb01a96a84a76ddb9357707b384c0b59ca477eebf6a`
- `semantic-links/retained-semantic-audit.json`: `fc488f8b9428636fc700f8bb86980cc80cf0bfcc5ac50bdea408d2e91c5dccf5`
- `semantic-links/native-rss-collector/request.json`: `ffa56d1105c4beb020a41a508269e47d2a33593a1c20bd79c850ee73fe0d5dab`
- `semantic-links/native-rss-collector/result.json`: `9b253372d51f92ddd2f3e51382433b5b0011c8e20dd795c2285467f066486110`

Fixture source bytes:

- `test/fixtures/compiler/native_optional_nil_arm/explicit_none.spl`: `0223e2be97f4eba97cdd92ec09dccbca6bc6cef3aa8e82999b695fb081ae41b6`
- `test/fixtures/compiler/native_optional_nil_arm/explicit_none_first.spl`: `760a2f7b06750273305e4627034ad7c4723dd897616b38ea430e00040b9af2ed`
- `test/fixtures/compiler/native_optional_nil_arm/original_nil.spl`: `f87efe0749654f191a95e9bc7744ecfc12a9630cccda7e7a5fd10fe9ea2e5075`
- `test/fixtures/compiler/native_optional_nil_arm/original_nil_first.spl`: `5faa306058110fe1f09353017d7bea879b81ac385a98f9c10e1fac2667493404`
- `test/fixtures/compiler/native_optional_nil_arm/explicit_none_bytes.spl`: `d8e85bd75283904666dc875cb7fb70d8c802c0e6bc5472f402b2705f50d628df`
- `test/fixtures/compiler/native_optional_nil_arm/original_nil_bytes.spl`: `239cff24fed1371b24486a9684b845e4ad43d5ce3f96ae403c4d912754d6c07f`

Final original-module evidence (retained local artifacts):

- `original0424-final/request.json`: `ebf54574a8c4a92fae792a761882e9887c633530e37e0fbcea2097dd68c89361`
- `original0424-final/module-0424/result.json`: `f664d091f0ecf6fd62d877fcadaa500802f2e4b372b235014847740e67e91136`
- `original0424-final/independent-audit.json`: `456d101fa3b300693a3163c96de6b64e78f8535ade1b180254e4f927bd0edea0`
- `original0424-final/cache-binding-addendum.json`: `4f9e8353da71cb8c3d109f71a8a2713ec610f060233813975202c19654ad3429`
