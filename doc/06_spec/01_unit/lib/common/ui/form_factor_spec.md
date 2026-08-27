# form_factor_spec

> Purpose: Prove that detect_device_class.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# form_factor_spec

Purpose: Prove that detect_device_class.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/form_factor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that detect_device_class.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### detect_device_class

#### macos no-touch wide → Desktop

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- macos no-touch wide → Desktop
- Verify: macos no-touch wide → Desktop
   - Expected: detect_device_class("macos", false, 900) equals `DeviceClass.Desktop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("macos no-touch wide → Desktop")
step("Verify: macos no-touch wide → Desktop")
# @req: REQ-LIB-COMMON-001
expect(detect_device_class("macos", false, 900)).to_equal(DeviceClass.Desktop)
```

</details>

#### android touch narrow → Phone

- android touch narrow → Phone
- Verify: android touch narrow → Phone
   - Expected: detect_device_class("android", true, 411) equals `DeviceClass.Phone`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("android touch narrow → Phone")
step("Verify: android touch narrow → Phone")
expect(detect_device_class("android", true, 411)).to_equal(DeviceClass.Phone)
```

</details>

#### android touch 600 → Tablet (boundary: >=600 Tablet)

- android touch 600 → Tablet (boundary: >=600 Tablet)
- Verify: android touch 600 → Tablet (boundary: >=600 Tablet)
   - Expected: detect_device_class("android", true, 600) equals `DeviceClass.Tablet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("android touch 600 → Tablet (boundary: >=600 Tablet)")
step("Verify: android touch 600 → Tablet (boundary: >=600 Tablet)")
expect(detect_device_class("android", true, 600)).to_equal(DeviceClass.Tablet)
```

</details>

#### ios touch 599 → Phone

- ios touch 599 → Phone
- Verify: ios touch 599 → Phone
   - Expected: detect_device_class("ios", true, 599) equals `DeviceClass.Phone`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ios touch 599 → Phone")
step("Verify: ios touch 599 → Phone")
expect(detect_device_class("ios", true, 599)).to_equal(DeviceClass.Phone)
```

</details>

#### ipados touch 768 → Tablet

- ipados touch 768 → Tablet
- Verify: ipados touch 768 → Tablet
   - Expected: detect_device_class("ipados", true, 768) equals `DeviceClass.Tablet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ipados touch 768 → Tablet")
step("Verify: ipados touch 768 → Tablet")
expect(detect_device_class("ipados", true, 768)).to_equal(DeviceClass.Tablet)
```

</details>

#### empty platform no-touch 500 → Desktop (unknown+no-touch)

- empty platform no-touch 500 → Desktop (unknown+no-touch)
- Verify: empty platform no-touch 500 → Desktop (unknown+no-touch)
   - Expected: detect_device_class("", false, 500) equals `DeviceClass.Desktop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty platform no-touch 500 → Desktop (unknown+no-touch)")
step("Verify: empty platform no-touch 500 → Desktop (unknown+no-touch)")
expect(detect_device_class("", false, 500)).to_equal(DeviceClass.Desktop)
```

</details>

#### windows touch 1000 → Tablet (touch-first windows tablet)

- windows touch 1000 → Tablet (touch-first windows tablet)
- Verify: windows touch 1000 → Tablet (touch-first windows tablet)
   - Expected: detect_device_class("windows", true, 1000) equals `DeviceClass.Tablet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("windows touch 1000 → Tablet (touch-first windows tablet)")
step("Verify: windows touch 1000 → Tablet (touch-first windows tablet)")
expect(detect_device_class("windows", true, 1000)).to_equal(DeviceClass.Tablet)
```

</details>

### DeviceClass.to_wire

#### Phone → phone

- Phone → phone
- Verify: Phone → phone
   - Expected: DeviceClass.Phone.to_wire() equals `phone`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Phone → phone")
step("Verify: Phone → phone")
expect(DeviceClass.Phone.to_wire()).to_equal("phone")
```

</details>

#### Tablet → tablet

- Tablet → tablet
- Verify: Tablet → tablet
   - Expected: DeviceClass.Tablet.to_wire() equals `tablet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Tablet → tablet")
step("Verify: Tablet → tablet")
expect(DeviceClass.Tablet.to_wire()).to_equal("tablet")
```

</details>

#### Desktop → desktop

- Desktop → desktop
- Verify: Desktop → desktop
   - Expected: DeviceClass.Desktop.to_wire() equals `desktop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Desktop → desktop")
step("Verify: Desktop → desktop")
expect(DeviceClass.Desktop.to_wire()).to_equal("desktop")
```

</details>

### compute_form_factor

#### 390x844 ios touch → Phone, horizontal Compact, Portrait

- 390x844 ios touch → Phone, horizontal Compact, Portrait
- Verify: 390x844 ios touch → Phone, horizontal Compact, Portrait
   - Expected: ff.device equals `DeviceClass.Phone`
   - Expected: ff.layout.horizontal equals `SizeClass.Compact`
   - Expected: ff.layout.orientation equals `Orientation.Portrait`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("390x844 ios touch → Phone, horizontal Compact, Portrait")
step("Verify: 390x844 ios touch → Phone, horizontal Compact, Portrait")
val vp = new_viewport(390, 844, "gui")
val ff = compute_form_factor(vp, "ios", true)
expect(ff.device).to_equal(DeviceClass.Phone)
expect(ff.layout.horizontal).to_equal(SizeClass.Compact)
expect(ff.layout.orientation).to_equal(Orientation.Portrait)
```

</details>

#### 1024x768 ipados touch → Tablet, horizontal Expanded

- 1024x768 ipados touch → Tablet, horizontal Expanded
- Verify: 1024x768 ipados touch → Tablet, horizontal Expanded
   - Expected: ff.device equals `DeviceClass.Tablet`
   - Expected: ff.layout.horizontal equals `SizeClass.Expanded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("1024x768 ipados touch → Tablet, horizontal Expanded")
step("Verify: 1024x768 ipados touch → Tablet, horizontal Expanded")
val vp = new_viewport(1024, 768, "gui")
val ff = compute_form_factor(vp, "ipados", true)
expect(ff.device).to_equal(DeviceClass.Tablet)
expect(ff.layout.horizontal).to_equal(SizeClass.Expanded)
```

</details>

#### 1440x900 macos no-touch → Desktop, horizontal Expanded

- 1440x900 macos no-touch → Desktop, horizontal Expanded
- Verify: 1440x900 macos no-touch → Desktop, horizontal Expanded
   - Expected: ff.device equals `DeviceClass.Desktop`
   - Expected: ff.layout.horizontal equals `SizeClass.Expanded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("1440x900 macos no-touch → Desktop, horizontal Expanded")
step("Verify: 1440x900 macos no-touch → Desktop, horizontal Expanded")
val vp = new_viewport(1440, 900, "gui")
val ff = compute_form_factor(vp, "macos", false)
expect(ff.device).to_equal(DeviceClass.Desktop)
expect(ff.layout.horizontal).to_equal(SizeClass.Expanded)
```

</details>

#### 844x390 ios touch landscape phone → Phone, vertical Compact

- 844x390 ios touch landscape phone → Phone, vertical Compact
- Verify: 844x390 ios touch landscape phone → Phone, vertical Compact
   - Expected: ff.device equals `DeviceClass.Phone`
   - Expected: ff.layout.vertical equals `SizeClass.Compact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("844x390 ios touch landscape phone → Phone, vertical Compact")
step("Verify: 844x390 ios touch landscape phone → Phone, vertical Compact")
val vp = new_viewport(844, 390, "gui")
val ff = compute_form_factor(vp, "ios", true)
expect(ff.device).to_equal(DeviceClass.Phone)
expect(ff.layout.vertical).to_equal(SizeClass.Compact)
```

</details>

### default_breakpoints width boundaries

#### classify(599) = Compact

- classify(599) = Compact
- Verify: classify(599) = Compact
   - Expected: classify(599, bp) equals `SizeClass.Compact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classify(599) = Compact")
step("Verify: classify(599) = Compact")
val bp = default_breakpoints()
expect(classify(599, bp)).to_equal(SizeClass.Compact)
```

</details>

#### classify(600) = Regular

- classify(600) = Regular
- Verify: classify(600) = Regular
   - Expected: classify(600, bp) equals `SizeClass.Regular`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classify(600) = Regular")
step("Verify: classify(600) = Regular")
val bp = default_breakpoints()
expect(classify(600, bp)).to_equal(SizeClass.Regular)
```

</details>

#### classify(839) = Regular

- classify(839) = Regular
- Verify: classify(839) = Regular
   - Expected: classify(839, bp) equals `SizeClass.Regular`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classify(839) = Regular")
step("Verify: classify(839) = Regular")
val bp = default_breakpoints()
expect(classify(839, bp)).to_equal(SizeClass.Regular)
```

</details>

#### classify(840) = Expanded

- classify(840) = Expanded
- Verify: classify(840) = Expanded
   - Expected: classify(840, bp) equals `SizeClass.Expanded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classify(840) = Expanded")
step("Verify: classify(840) = Expanded")
val bp = default_breakpoints()
expect(classify(840, bp)).to_equal(SizeClass.Expanded)
```

</details>

### height_breakpoints boundaries

#### classify(479) = Compact

- classify(479) = Compact
- Verify: classify(479) = Compact
   - Expected: classify(479, bp) equals `SizeClass.Compact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classify(479) = Compact")
step("Verify: classify(479) = Compact")
val bp = height_breakpoints()
expect(classify(479, bp)).to_equal(SizeClass.Compact)
```

</details>

#### classify(480) = Regular

- classify(480) = Regular
- Verify: classify(480) = Regular
   - Expected: classify(480, bp) equals `SizeClass.Regular`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classify(480) = Regular")
step("Verify: classify(480) = Regular")
val bp = height_breakpoints()
expect(classify(480, bp)).to_equal(SizeClass.Regular)
```

</details>

#### classify(899) = Regular

- classify(899) = Regular
- Verify: classify(899) = Regular
   - Expected: classify(899, bp) equals `SizeClass.Regular`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classify(899) = Regular")
step("Verify: classify(899) = Regular")
val bp = height_breakpoints()
expect(classify(899, bp)).to_equal(SizeClass.Regular)
```

</details>

#### classify(900) = Expanded

- classify(900) = Expanded
- Verify: classify(900) = Expanded
   - Expected: classify(900, bp) equals `SizeClass.Expanded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classify(900) = Expanded")
step("Verify: classify(900) = Expanded")
val bp = height_breakpoints()
expect(classify(900, bp)).to_equal(SizeClass.Expanded)
```

</details>

### min_touch_target

#### Phone ios → 44

- Phone ios → 44
- Verify: Phone ios → 44
   - Expected: min_touch_target(DeviceClass.Phone, "ios") equals `44`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Phone ios → 44")
step("Verify: Phone ios → 44")
expect(min_touch_target(DeviceClass.Phone, "ios")).to_equal(44)
```

</details>

#### Phone android → 48

- Phone android → 48
- Verify: Phone android → 48
   - Expected: min_touch_target(DeviceClass.Phone, "android") equals `48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Phone android → 48")
step("Verify: Phone android → 48")
expect(min_touch_target(DeviceClass.Phone, "android")).to_equal(48)
```

</details>

#### Tablet ipados → 44

- Tablet ipados → 44
- Verify: Tablet ipados → 44
   - Expected: min_touch_target(DeviceClass.Tablet, "ipados") equals `44`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Tablet ipados → 44")
step("Verify: Tablet ipados → 44")
expect(min_touch_target(DeviceClass.Tablet, "ipados")).to_equal(44)
```

</details>

#### Desktop macos → 32

- Desktop macos → 32
- Verify: Desktop macos → 32
   - Expected: min_touch_target(DeviceClass.Desktop, "macos") equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Desktop macos → 32")
step("Verify: Desktop macos → 32")
expect(min_touch_target(DeviceClass.Desktop, "macos")).to_equal(32)
```

</details>

### supports_hover

#### Desktop → true

- Desktop → true
- Verify: Desktop → true
   - Expected: supports_hover(DeviceClass.Desktop) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Desktop → true")
step("Verify: Desktop → true")
expect(supports_hover(DeviceClass.Desktop)).to_equal(true)
```

</details>

#### Phone → false

- Phone → false
- Verify: Phone → false
   - Expected: supports_hover(DeviceClass.Phone) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Phone → false")
step("Verify: Phone → false")
expect(supports_hover(DeviceClass.Phone)).to_equal(false)
```

</details>

#### Tablet → false

- Tablet → false
- Verify: Tablet → false
   - Expected: supports_hover(DeviceClass.Tablet) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Tablet → false")
step("Verify: Tablet → false")
expect(supports_hover(DeviceClass.Tablet)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `43476336a611e2fb416a497cfa306ffc7f8ae494a8a174cea8825b7c1fa79242`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `43476336a611e2fb416a497cfa306ffc7f8ae494a8a174cea8825b7c1fa79242`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `43476336a611e2fb416a497cfa306ffc7f8ae494a8a174cea8825b7c1fa79242`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/ui/form_factor_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/form_factor_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/form_factor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/form_factor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/form_factor_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/form_factor_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'macos no-touch wide → Desktop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/form_factor_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'android touch narrow → Phone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/form_factor_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'android touch 600 → Tablet (boundary: >=600 Tablet)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
