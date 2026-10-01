# Theme Package Wire Specification

> Tests covering theme render snapshot wire v1 round trip, theme render snapshot wire v1 precise rejection, theme package install wire v1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Theme Package Wire Specification

## Scenarios

### theme render snapshot wire v1 round trip

#### round-trips every scalar Unicode multiline NUL gradient and shadow field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = _wire_snapshot()
_decode_and_expect_equal(_snapshot_wire(), original)
```

</details>

#### emits deterministic lowercase canonical text

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = _snapshot_wire()
val second = _snapshot_wire()
expect(first).to_equal(second)
expect(first).to_contain("id=676c617373\n")
match theme_render_snapshot_wire_v1_decode(first):
    Err(_error):
        expect(false).to_equal(true)
    Ok(snapshot):
        match theme_render_snapshot_wire_v1_encode(snapshot):
            Err(_error): expect(false).to_equal(true)
            Ok(encoded): expect(encoded).to_equal(first)
```

</details>

#### round-trips zero and exact maximum active and inactive shadow counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero = _snapshot_with("zero", "family", "", "", 0, 0)
match theme_render_snapshot_wire_v1_encode(zero):
    Err(_error): expect(false).to_equal(true)
    Ok(wire): _decode_and_expect_equal(wire, zero)

val maximum = _snapshot_with("maximum", "family", "", "", 32, 32)
match theme_render_snapshot_wire_v1_encode(maximum):
    Err(_error): expect(false).to_equal(true)
    Ok(wire): _decode_and_expect_equal(wire, maximum)
```

</details>

#### round-trips an exact 262144-byte field through the linear buffer path

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maximum_css = _repeat_text("x", THEME_RENDER_SNAPSHOT_WIRE_V1_MAX_TEXT_BYTES)
val snapshot = _snapshot_with("maximum_text", "family", maximum_css, "", 0, 0)
match theme_render_snapshot_wire_v1_encode(snapshot):
    Err(_error): expect(false).to_equal(true)
    Ok(wire):
        expect(wire.len()).to_be_greater_than(THEME_RENDER_SNAPSHOT_WIRE_V1_MAX_TEXT_BYTES)
        _decode_and_expect_equal(wire, snapshot)
```

</details>

### theme render snapshot wire v1 precise rejection

#### rejects wrong magic missing final newline complete trailing and duplicate lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _snapshot_wire()
_expect_snapshot_decode_error(wire.replace(THEME_RENDER_SNAPSHOT_WIRE_V1_MAGIC, "theme-render-snapshot-wire-v2"), "wrong magic/version")
_expect_snapshot_decode_error(wire.slice(0, wire.len() - 1), "missing final newline")
_expect_snapshot_decode_error(wire + "extra=0\n", "trailing or duplicate field")
_expect_snapshot_decode_error(wire.replace("id=676c617373\n", "id=676c617373\nid=676c617373\n"), "expected field family_id")
```

</details>

#### accepts lowercase hex and rejects odd uppercase malformed and invalid UTF-8 hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _snapshot_wire()
_decode_and_expect_equal(wire, _wire_snapshot())
_expect_snapshot_decode_error(wire.replace("id=676c617373", "id=676c61737"), "odd length")
_expect_snapshot_decode_error(wire.replace("id=676c617373", "id=676C617373"), "malformed or noncanonical")
_expect_snapshot_decode_error(wire.replace("id=676c617373", "id=0g"), "malformed or noncanonical")
_expect_snapshot_decode_error(wire.replace("id=676c617373", "id=ff"), "does not decode to UTF-8")
```

</details>

#### rejects bool and every signed or unsigned canonical range branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _snapshot_wire()
_expect_snapshot_decode_error(wire.replace("window_gradient_available=1", "window_gradient_available=2"), "bool must be 0 or 1")
_expect_snapshot_decode_error(wire.replace("background_rgba=4278190081", "background_rgba=04278190081"), "unsigned number is noncanonical")
_expect_snapshot_decode_error(wire.replace("background_rgba=4278190081", "background_rgba=4294967296"), "overflows u32")
_expect_snapshot_decode_error(wire.replace("surface_alpha_milli=875", "surface_alpha_milli=-0"), "negative zero")
_expect_snapshot_decode_error(wire.replace("backdrop_blur_px=30", "backdrop_blur_px=2147483648"), "overflows i32")
_expect_snapshot_decode_error(wire.replace("corner_radius_px=18", "corner_radius_px=-2147483649"), "overflows i32")
```

</details>

#### rejects malformed and short source and material hashes independently

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _snapshot_wire()
_expect_snapshot_decode_error(wire.replace(SOURCE_HASH, "Aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"), "source_manifest_sha256 is malformed")
_expect_snapshot_decode_error(wire.replace(SOURCE_HASH, "aaaa"), "source_manifest_sha256 is malformed")
val snapshot = _wire_snapshot()
val material_hash = snapshot.material_sha256
val material_hash_line = "material_sha256={material_hash}"
val material_hash_tail = material_hash.slice(1, material_hash.len())
_expect_snapshot_decode_error(wire.replace(material_hash_line, "material_sha256=Z{material_hash_tail}"), "material_sha256 is malformed")
_expect_snapshot_decode_error(wire.replace(material_hash_line, "material_sha256=bbbb"), "material_sha256 is malformed")
```

</details>

#### rejects material mismatch inactive count overflow and count body mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _snapshot_wire()
_expect_snapshot_decode_error(wire.replace("font_weight=650", "font_weight=651"), "does not match material")
_expect_snapshot_decode_error(wire.replace("inactive_shadow_count=2", "inactive_shadow_count=33"), "shadow count exceeds limit")
_expect_snapshot_decode_error(wire.replace("active_shadow_count=2", "active_shadow_count=1"), "expected field inactive_shadow_count")
```

</details>

#### rejects empty required snapshot ids and fields over 262144 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_expect_snapshot_encode_error(_snapshot_with("", "family", "", "", 0, 0), "snapshot id and family_id are required")
_expect_snapshot_encode_error(_snapshot_with("id", "", "", "", 0, 0), "snapshot id and family_id are required")
val too_large = _repeat_text("x", THEME_RENDER_SNAPSHOT_WIRE_V1_MAX_TEXT_BYTES + 1)
_expect_snapshot_encode_error(_snapshot_with("id", "family", too_large, "", 0, 0), "text field exceeds byte limit")
```

</details>

#### rejects snapshot and install envelopes over 1 MiB before parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snapshot_body = _repeat_text("x", THEME_RENDER_SNAPSHOT_WIRE_V1_MAX_BYTES)
val oversized_snapshot = "{THEME_RENDER_SNAPSHOT_WIRE_V1_MAGIC}\n{snapshot_body}"
_expect_snapshot_decode_error(oversized_snapshot, "wire size is invalid")
val install_body = _repeat_text("x", THEME_PACKAGE_INSTALL_WIRE_V1_MAX_UTF8_BYTES)
val oversized_install = "{THEME_PACKAGE_INSTALL_WIRE_V1_MAGIC}\n{install_body}"
_expect_install_decode_error(oversized_install, "wire size is invalid")
```

</details>

#### rejects an encoded snapshot whose two exact-max text fields exceed 1 MiB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maximum_text = _repeat_text("x", THEME_RENDER_SNAPSHOT_WIRE_V1_MAX_TEXT_BYTES)
_expect_snapshot_encode_error(_snapshot_with("id", "family", maximum_text, maximum_text, 0, 0), "encoded snapshot exceeds wire limit")
```

</details>

### theme package install wire v1

#### round-trips immutable install metadata and canonical snapshot text

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snapshot = _wire_snapshot()
match theme_package_install_wire_v1_encode("glass", "aetheric_dark", "config/themes/theme.sdn", snapshot):
    Err(_error): expect(false).to_equal(true)
    Ok(wire):
        expect(theme_package_install_wire_v1_utf8_byte_len(wire)).to_equal(wire.len())
        expect(theme_package_install_wire_v1_within_bound(wire)).to_equal(true)
        match theme_package_install_wire_v1_decode(wire):
            Err(_error): expect(false).to_equal(true)
            Ok(projection):
                expect(projection.requested_id).to_equal("glass")
                expect(projection.default_id).to_equal("aetheric_dark")
                expect(projection.registry_path).to_equal("config/themes/theme.sdn")
                _expect_snapshot_equal(projection.snapshot, snapshot)
                match theme_package_install_wire_v1_encode(projection.requested_id, projection.default_id, projection.registry_path, projection.snapshot):
                    Err(_error): expect(false).to_equal(true)
                    Ok(reencoded): expect(reencoded).to_equal(wire)
```

</details>

#### accepts exact 4096-byte metadata and rejects the next byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exact = _repeat_text("m", THEME_PACKAGE_INSTALL_WIRE_V1_MAX_METADATA_BYTES)
val snapshot = _wire_snapshot()
match theme_package_install_wire_v1_encode(exact, exact, exact, snapshot):
    Err(_error): expect(false).to_equal(true)
    Ok(wire):
        match theme_package_install_wire_v1_decode(wire):
            Err(_error): expect(false).to_equal(true)
            Ok(projection): expect(projection.requested_id).to_equal(exact)
_expect_install_encode_error("{exact}x", "default", "registry", snapshot, "install metadata exceeds byte limit")
```

</details>

#### rejects empty metadata nested snapshot overflow and malformed nested wire

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snapshot = _wire_snapshot()
_expect_install_encode_error("", "default", "registry", snapshot, "install metadata is required")
_expect_install_encode_error("requested", "", "registry", snapshot, "install metadata is required")
_expect_install_encode_error("requested", "default", "", snapshot, "install metadata is required")
val nested_too_large = _snapshot_with("large", "family", _repeat_text("x", 131072), "", 0, 0)
_expect_install_encode_error("requested", "default", "registry", nested_too_large, "snapshot is too large for install wire")

match theme_package_install_wire_v1_encode("glass", "aetheric_dark", "config/themes/theme.sdn", snapshot):
    Err(_error): expect(false).to_equal(true)
    Ok(wire):
        _expect_install_decode_error(wire.replace("snapshot_wire=7468656d", "snapshot_wire=7568656d"), "wrong magic/version")
```

</details>

#### reports empty and over-1-MiB install texts outside the shared bound

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(theme_package_install_wire_v1_within_bound("")).to_equal(false)
val oversized = _repeat_text("x", THEME_PACKAGE_INSTALL_WIRE_V1_MAX_UTF8_BYTES + 1)
expect(theme_package_install_wire_v1_utf8_byte_len(oversized)).to_equal(THEME_PACKAGE_INSTALL_WIRE_V1_MAX_UTF8_BYTES + 1)
expect(theme_package_install_wire_v1_within_bound(oversized)).to_equal(false)
```

</details>

#### rejects complete trailing duplicate odd and uppercase install fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snapshot = _wire_snapshot()
match theme_package_install_wire_v1_encode("glass", "aetheric_dark", "config/themes/theme.sdn", snapshot):
    Err(_error): expect(false).to_equal(true)
    Ok(wire):
        _expect_install_decode_error(wire + "extra=0\n", "trailing or duplicate field")
        _expect_install_decode_error(wire.replace("requested_id=676c617373\n", "requested_id=676c617373\nrequested_id=676c617373\n"), "expected field default_id")
        _expect_install_decode_error(wire.replace("requested_id=676c617373", "requested_id=676c61737"), "odd length")
        _expect_install_decode_error(wire.replace("requested_id=676c617373", "requested_id=676C617373"), "malformed or noncanonical")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/theme_package_wire_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering theme render snapshot wire v1 round trip, theme render snapshot wire v1 precise rejection, theme package install wire v1.
- theme render snapshot wire v1 round trip
- theme render snapshot wire v1 precise rejection
- theme package install wire v1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `04e5275c3f95e7172f393c7bdd92a62e443298eaba49873f6403175443d8f7fc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `04e5275c3f95e7172f393c7bdd92a62e443298eaba49873f6403175443d8f7fc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `04e5275c3f95e7172f393c7bdd92a62e443298eaba49873f6403175443d8f7fc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/lib/common/ui/theme_package_wire_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/theme_package_wire_spec.md (current)
findings: 10 blockers: 0
  narrative=80 structure=60 oracle=100
  traceability=80 evidence=100 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/theme_package_wire_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/theme_package_wire_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/theme_package_wire_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/common/ui/theme_package_wire_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/lib/common/ui/theme_package_wire_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/01_unit/lib/common/ui/theme_package_wire_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/01_unit/lib/common/ui/theme_package_wire_spec.spl:192:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'round-trips every scalar Unicode multiline NUL gradient and shadow field' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/ui/theme_package_wire_spec.spl:196:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'emits deterministic lowercase canonical text' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/ui/theme_package_wire_spec.spl:209:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'round-trips zero and exact maximum active and inactive shadow counts' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/ui/theme_package_wire_spec.spl:220:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'round-trips an exact 262144-byte field through the linear buffer path' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
