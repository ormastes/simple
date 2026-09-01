# Composition Codec Specification

> Tests covering SimpleCompositionImageV1 source and codec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Composition Codec Specification

## Scenarios

### SimpleCompositionImageV1 source and codec

#### REQ-001 canonicalizes semantically reordered application source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-001 canonicalizes semantically reordered application source
   - Expected: first.len() > 148 is true
   - Expected: first equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-001 canonicalizes semantically reordered application source")
val first = _encoded(SOURCE_AB)
val second = _encoded(SOURCE_BA)
expect(first.len() > 148).to_equal(true)
expect(first).to_equal(second)
```

</details>

#### REQ-001 round-trips the immutable application projection

- REQ-001 round-trips the immutable application projection
   - Expected: encoded[12] equals `96`
   - Expected: encoded[96] equals `8`
   - Expected: decoded.ok is true
   - Expected: decoded.image.schema equals `simple.composition/1`
   - Expected: decoded.image.profile equals `dev`
   - Expected: decoded.image.apps.len() equals `2`
   - Expected: decoded.image.apps[0].app_id equals `alpha`
   - Expected: decoded.image.apps[0].associations.len() equals `2`
   - Expected: decoded.image.composition_digest.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-001 round-trips the immutable application projection")
val encoded = _encoded(SOURCE_AB)
val decoded = decode_composition_image_v1(encoded)
expect(encoded[12]).to_equal(96)
expect(encoded[96]).to_equal(8)
expect(decoded.ok).to_equal(true)
expect(decoded.image.schema).to_equal("simple.composition/1")
expect(decoded.image.profile).to_equal("dev")
expect(decoded.image.apps.len()).to_equal(2)
expect(decoded.image.apps[0].app_id).to_equal("alpha")
expect(decoded.image.apps[0].associations.len()).to_equal(2)
expect(decoded.image.composition_digest.len()).to_equal(64)
```

</details>

#### REQ-002 rejects an invalid magic

- REQ-002 rejects an invalid magic
   - Expected: decoded.ok is false
   - Expected: decoded.diagnostic.code equals `SCI_MAGIC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-002 rejects an invalid magic")
var bad = _encoded(SOURCE_AB)
bad[0] = 0
val decoded = decode_composition_image_v1(bad)
expect(decoded.ok).to_equal(false)
expect(decoded.diagnostic.code).to_equal("SCI_MAGIC")
```

</details>

#### REQ-002 rejects a section whose bounds exceed the image

- REQ-002 rejects a section whose bounds exceed the image
   - Expected: decoded.ok is false
   - Expected: decoded.diagnostic.code equals `SCI_BOUNDS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-002 rejects a section whose bounds exceed the image")
var bad = _encoded(SOURCE_AB)
bad[104] = 255
bad[105] = 255
bad[106] = 255
bad[107] = 127
val decoded = decode_composition_image_v1(bad)
expect(decoded.ok).to_equal(false)
expect(decoded.diagnostic.code).to_equal("SCI_BOUNDS")
```

</details>

#### REQ-002 rejects a changed section payload digest

- REQ-002 rejects a changed section payload digest
   - Expected: decoded.ok is false
   - Expected: decoded.diagnostic.code equals `SCI_DIGEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-002 rejects a changed section payload digest")
var bad = _encoded(SOURCE_AB)
bad[bad.len() - 1] = bad[bad.len() - 1] ^ 1
val decoded = decode_composition_image_v1(bad)
expect(decoded.ok).to_equal(false)
expect(decoded.diagnostic.code).to_equal("SCI_DIGEST")
```

</details>

#### REQ-001 rejects non-canonical reserved header bytes

- REQ-001 rejects non-canonical reserved header bytes
   - Expected: decoded.ok is false
   - Expected: decoded.diagnostic.code equals `SCI_NON_CANONICAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-001 rejects non-canonical reserved header bytes")
var bad = _encoded(SOURCE_AB)
bad[92] = 1
val decoded = decode_composition_image_v1(bad)
expect(decoded.ok).to_equal(false)
expect(decoded.diagnostic.code).to_equal("SCI_NON_CANONICAL")
```

</details>

#### REQ-002 rejects duplicate application identities

- REQ-002 rejects duplicate application identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-002 rejects duplicate application identities")
val source = "schema: simple.composition/1\napps:\n  - id: editor\n    name: Editor\n    artifact: /sys/apps/editor.smf\n  - id: editor\n    name: Other\n    artifact: /sys/apps/other.smf\n"
match parse_composition_source_v1(source):
    case Err(e): expect(e).to_contain("duplicate-app-id: editor")
    case Ok(_): expect(false).to_equal(true)
```

</details>

#### REQ-002 rejects unsafe artifact paths

- REQ-002 rejects unsafe artifact paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-002 rejects unsafe artifact paths")
val source = "schema: simple.composition/1\napps:\n  - id: editor\n    name: Editor\n    artifact: ../editor.smf\n"
match parse_composition_source_v1(source):
    case Err(e): expect(e).to_contain("unsafe-artifact-path")
    case Ok(_): expect(false).to_equal(true)
```

</details>

#### REQ-003 round-trips provider binding and CLI command records

- REQ-003 round-trips provider binding and CLI command records
   - Expected: decoded.ok is true
   - Expected: encoded[16] equals `2`
   - Expected: decoded.image.interface_groups[0].group_id equals `cli.command`
   - Expected: decoded.image.providers[0].artifact_digest equals `DIGEST_A`
   - Expected: decoded.image.providers[0].required_capability_bits equals `4`
   - Expected: decoded.image.bindings[0].provider_id equals `cli.formatter`
   - Expected: decoded.image.commands[0].command_name equals `fmt`
   - Expected: decoded.image.commands[0].aliases[0] equals `format`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-003 round-trips provider binding and CLI command records")
val encoded = _encoded(SOURCE_PROVIDER)
val decoded = decode_composition_image_v1(encoded)
expect(decoded.ok).to_equal(true)
expect(encoded[16]).to_equal(2)
expect(decoded.image.interface_groups[0].group_id).to_equal("cli.command")
expect(decoded.image.providers[0].artifact_digest).to_equal(DIGEST_A)
expect(decoded.image.providers[0].required_capability_bits).to_equal(4)
expect(decoded.image.bindings[0].provider_id).to_equal("cli.formatter")
expect(decoded.image.commands[0].command_name).to_equal("fmt")
expect(decoded.image.commands[0].aliases[0]).to_equal("format")
```

</details>

#### REQ-003 rejects duplicate command aliases

- REQ-003 rejects duplicate command aliases


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-003 rejects duplicate command aliases")
val source = SOURCE_PROVIDER + "  - name: format\n    aliases: []\n    summary: Duplicate alias\n    binding: cli.format\n    interface_group: cli.command\n"
match parse_composition_source_v1(source):
    case Err(e): expect(e).to_contain("duplicate-command")
    case Ok(_): expect(false).to_equal(true)
```

</details>

#### REQ-003 rejects unresolved provider interface groups

- REQ-003 rejects unresolved provider interface groups


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-003 rejects unresolved provider interface groups")
val source = SOURCE_PROVIDER.replace("interface_groups: [cli.command]", "interface_groups: [cli.missing]")
match parse_composition_source_v1(source):
    case Err(e): expect(e).to_contain("unknown-interface-group")
    case Ok(_): expect(false).to_equal(true)
```

</details>

#### REQ-003 rejects unsafe provider artifacts and non-exact digests

- REQ-003 rejects unsafe provider artifacts and non-exact digests


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-003 rejects unsafe provider artifacts and non-exact digests")
val unsafe_source = SOURCE_PROVIDER.replace("/sys/providers/fmt.smf", "../fmt.smf")
match parse_composition_source_v1(unsafe_source):
    case Err(e): expect(e).to_contain("unsafe-provider-path")
    case Ok(_): expect(false).to_equal(true)
val digest_source = SOURCE_PROVIDER.replace(DIGEST_A, "abcd")
match parse_composition_source_v1(digest_source):
    case Err(e): expect(e).to_contain("invalid-artifact-digest")
    case Ok(_): expect(false).to_equal(true)
```

</details>

#### REQ-003 skips unknown optional sections and rejects unknown required sections

- REQ-003 skips unknown optional sections and rejects unknown required sections
   - Expected: skipped.ok is true
   - Expected: skipped.image.apps.len() equals `0`
   - Expected: rejected.ok is false
   - Expected: rejected.diagnostic.code equals `SCI_REQUIRED_SECTION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-003 skips unknown optional sections and rejects unknown required sections")
var optional = _encoded(SOURCE_PROVIDER)
optional[144] = 77
optional[145] = 0
optional[146] = 0
optional[147] = 0
optional[150] = 0
optional[151] = 0
_refresh_multi_section_digest(optional)
val skipped = decode_composition_image_v1(optional)
expect(skipped.ok).to_equal(true)
expect(skipped.image.apps.len()).to_equal(0)
var required = optional
required[150] = 1
_refresh_multi_section_digest(required)
val rejected = decode_composition_image_v1(required)
expect(rejected.ok).to_equal(false)
expect(rejected.diagnostic.code).to_equal("SCI_REQUIRED_SECTION")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/composition/composition_codec_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleCompositionImageV1 source and codec.
- SimpleCompositionImageV1 source and codec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `84907a98d40f94ce123fd280fd26cfc98118f28801e8ee337b02e6b2f126f351`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84907a98d40f94ce123fd280fd26cfc98118f28801e8ee337b02e6b2f126f351`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84907a98d40f94ce123fd280fd26cfc98118f28801e8ee337b02e6b2f126f351`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/composition/composition_codec_spec.spl
mirror: doc/06_spec/01_unit/lib/composition/composition_codec_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/composition/composition_codec_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/composition/composition_codec_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/composition/composition_codec_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/composition/composition_codec_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-001 canonicalizes semantically reordered application source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/composition/composition_codec_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-001 round-trips the immutable application projection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/composition/composition_codec_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-002 rejects an invalid magic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
