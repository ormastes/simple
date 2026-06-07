# SFM Codec & Manifest

> `.sfm` is the primary Simple Feature Module container. It is a pure-Simple outer container that embeds an opaque SMF code payload plus a feature manifest declaring the exposed front-end / back-end layers, their security level, and the build version. This spec covers AC-1 (codec round-trip preserves manifest fields and the embedded SMF bytes) and AC-2 (the manifest declares exposed layers with name/kind/entry).

<!-- sdn-diagram:id=sfm_codec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sfm_codec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sfm_codec_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sfm_codec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SFM Codec & Manifest

`.sfm` is the primary Simple Feature Module container. It is a pure-Simple outer container that embeds an opaque SMF code payload plus a feature manifest declaring the exposed front-end / back-end layers, their security level, and the build version. This spec covers AC-1 (codec round-trip preserves manifest fields and the embedded SMF bytes) and AC-2 (the manifest declares exposed layers with name/kind/entry).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFM |
| Category | Infrastructure |
| Status | Draft |
| Requirements | doc/04_architecture/language/simple_feature_module.md |
| Design | doc/05_design/simple_feature_module.md |
| Source | `test/03_system/feature/sfm/sfm_codec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`.sfm` is the primary Simple Feature Module container. It is a pure-Simple outer
container that embeds an opaque SMF code payload plus a feature manifest declaring
the exposed front-end / back-end layers, their security level, and the build version.
This spec covers AC-1 (codec round-trip preserves manifest fields and the embedded
SMF bytes) and AC-2 (the manifest declares exposed layers with name/kind/entry).

The byte-exact round-trip is *also* asserted by a standalone runnable probe
(`sfm_roundtrip_probe.spl`), because the test runner does not execute `it` blocks —
see `## Related Specifications`.

## Key Concepts

| Concept | Description |
|---------|-------------|
| FeatureManifest | Name, version, security level, and the list of exposed layers |
| LayerDescriptor | One exposed layer: role, kind, entry symbol, privileged flag |
| LayerKind | FrontGui / FrontTui / FrontArgParser / BackDb / BackHw |
| encode_sfm | Pure byte encoder: `(manifest, smf_bytes) -> [u8]` |
| decode_sfm | Pure byte decoder: `[u8] -> Result<(manifest, smf_bytes), text>` |

## Related Specifications

- [sfm_roundtrip_probe.spl](sfm_roundtrip_probe.spl) — ground-truth AC-1 byte gate (run via `bin/simple run`)
- [sfm_di_authz_spec.spl](sfm_di_authz_spec.spl) — DI + AOP authorization (AC-3/4/5)
- [sfm_loader_profiles_spec.spl](sfm_loader_profiles_spec.spl) — profile selection (AC-6)

## Scenarios

### SFM codec

### AC-1: write -> read round-trip

<details>
<summary>Advanced: should preserve the manifest name and version</summary>

#### should preserve the manifest name and version

1. Ok
   - Binary capture: after_step
   - Evidence: binary artifact verified by 2 expected checks
   - Expected: decoded.name equals `sample-sfm`
   - Expected: decoded.version equals `1.4.2`

2. Err
   - Binary capture: after_step
   - Evidence: binary artifact verified by 1 expected check
   - Expected: "decode-failed: " + e equals `ok`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = build_manifest()
val smf = build_fake_smf_bytes()
match round_trip(m, smf):
    Ok((decoded, _)):
        expect(decoded.name).to_equal("sample-sfm")
        expect(decoded.version).to_equal("1.4.2")
    Err(e):
        expect("decode-failed: " + e).to_equal("ok")
```

</details>


</details>

<details>
<summary>Advanced: should preserve the embedded SMF bytes exactly</summary>

#### should preserve the embedded SMF bytes exactly

1. Ok
   - Binary capture: after_step
   - Evidence: binary artifact verified by 1 expected check
   - Expected: out.len() equals `smf.len()`

2. assert true
   - Binary capture: after_step

3. Err
   - Binary capture: after_step
   - Evidence: binary artifact verified by 1 expected check
   - Expected: "decode-failed: " + e equals `ok`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = build_manifest()
val smf = build_fake_smf_bytes()
match round_trip(m, smf):
    Ok((_, out)):
        expect(out.len()).to_equal(smf.len())
        assert_true(bytes_equal(out, smf))
    Err(e):
        expect("decode-failed: " + e).to_equal("ok")
```

</details>


</details>

<details>
<summary>Advanced: should be re-encode idempotent (catches symmetric codec bugs)</summary>

#### should be re-encode idempotent (catches symmetric codec bugs)

1. Ok
   - Binary capture: after_step

2. assert true
   - Binary capture: after_step

3. Err
   - Binary capture: after_step
   - Evidence: binary artifact verified by 1 expected check
   - Expected: "decode-failed: " + e equals `ok`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = build_manifest()
val smf = build_fake_smf_bytes()
val first: [u8] = encode_sfm(m, smf)
match decode_sfm(first):
    Ok((m2, smf2)):
        assert_true(reencode_matches(m2, smf2, first))
    Err(e):
        expect("decode-failed: " + e).to_equal("ok")
```

</details>


</details>

<details>
<summary>Advanced: should preserve the security level marker</summary>

#### should preserve the security level marker

1. Ok
   - Binary capture: after_step

2. Ordinary: assert true
   - Binary capture: after_step

3. Trusted:  expect
   - Binary capture: after_step

4. Err
   - Binary capture: after_step
   - Evidence: binary artifact verified by 1 expected check
   - Expected: "decode-failed: " + e equals `ok`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = build_manifest()
val smf = build_fake_smf_bytes()
match round_trip(m, smf):
    Ok((decoded, _)):
        match decoded.security_level:
            Ordinary: assert_true(true)
            Trusted:  expect("expected Ordinary").to_equal("ok")
    Err(e):
        expect("decode-failed: " + e).to_equal("ok")
```

</details>


</details>

### AC-2: exposed layer manifest fields

<details>
<summary>Advanced: should declare each layer with a role, kind and entry symbol</summary>

#### should declare each layer with a role, kind and entry symbol

1. FrontArgParser: assert true

2.  :              expect


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = build_manifest()
expect(m.layers.len()).to_equal(2)
val front = m.layers[0]
expect(front.role).to_equal("cli")
expect(front.entry_symbol).to_equal("arg_parse_main")
match front.kind:
    FrontArgParser: assert_true(true)
    _:              expect("expected FrontArgParser").to_equal("ok")
```

</details>


</details>

<details>
<summary>Advanced: should carry the layer kind through a codec round-trip</summary>

#### should carry the layer kind through a codec round-trip

1. Ok
   - Expected: decoded.layers.len() equals `2`
   - Expected: back.role equals `device`
   - Expected: back.entry_symbol equals `hw_open`

2. assert true

3. BackHw: assert true

4.  :      expect

5. Err
   - Expected: "decode-failed: " + e equals `ok`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = build_manifest()
val smf = build_fake_smf_bytes()
match round_trip(m, smf):
    Ok((decoded, _)):
        expect(decoded.layers.len()).to_equal(2)
        val back = decoded.layers[1]
        expect(back.role).to_equal("device")
        expect(back.entry_symbol).to_equal("hw_open")
        assert_true(back.privileged)
        match back.kind:
            BackHw: assert_true(true)
            _:      expect("expected BackHw").to_equal("ok")
    Err(e):
        expect("decode-failed: " + e).to_equal("ok")
```

</details>


</details>

### SFM codec edge cases

<details>
<summary>Advanced: should reject bytes too short to hold a header</summary>

#### should reject bytes too short to hold a header

1. tiny append

2. Ok

3. Err


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tiny: [u8] = []
tiny.append(83 as u8)
match decode_sfm(tiny):
    Ok(_):  expect("should have failed").to_equal("ok")
    Err(_): assert_true(true)
```

</details>


</details>

<details>
<summary>Advanced: should preserve an empty embedded SMF payload</summary>

#### should preserve an empty embedded SMF payload

1. Ok
   - Expected: out.len() equals `0`

2. Err
   - Expected: "decode-failed: " + e equals `ok`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = build_manifest()
var empty: [u8] = []
match round_trip(m, empty):
    Ok((_, out)):
        expect(out.len()).to_equal(0)
    Err(e):
        expect("decode-failed: " + e).to_equal("ok")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/04_architecture/language/simple_feature_module.md](doc/04_architecture/language/simple_feature_module.md)
- **Design:** [doc/05_design/simple_feature_module.md](doc/05_design/simple_feature_module.md)


</details>
