# Platform Specification

> Tests covering AppConfig platform detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Platform Specification

## Scenarios

### AppConfig platform detection

#### from_env detects current platform

#### detects a known platform

- detects a known platform
   - Expected: known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects a known platform")
val config = AppConfig.from_env("test", "1.0")
val p = config.platform
# Must be one of the known platforms
val known = p == "linux" or p == "macos" or p == "windows" or p == "freebsd"
expect(known).to_equal(true)
```

</details>

#### detects a known architecture

- detects a known architecture
   - Expected: known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects a known architecture")
val config = AppConfig.from_env("test", "1.0")
val a = config.arch
val known = a == "x86_64" or a == "aarch64" or a == "riscv64" or a == "i686"
expect(known).to_equal(true)
```

</details>

#### desktop platforms

#### linux is desktop

- linux is desktop
   - Expected: c.is_desktop() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("linux is desktop")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "linux", arch: "x86_64")
expect(c.is_desktop()).to_equal(true)
```

</details>

#### macos is desktop

- macos is desktop
   - Expected: c.is_desktop() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("macos is desktop")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "macos", arch: "aarch64")
expect(c.is_desktop()).to_equal(true)
```

</details>

#### windows is desktop

- windows is desktop
   - Expected: c.is_desktop() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("windows is desktop")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "windows", arch: "x86_64")
expect(c.is_desktop()).to_equal(true)
```

</details>

#### freebsd is desktop

- freebsd is desktop
   - Expected: c.is_desktop() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("freebsd is desktop")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "freebsd", arch: "x86_64")
expect(c.is_desktop()).to_equal(true)
```

</details>

#### mobile platforms

#### ios is mobile

- ios is mobile
   - Expected: c.is_mobile() is true
   - Expected: c.is_desktop() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ios is mobile")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "ios", arch: "aarch64")
expect(c.is_mobile()).to_equal(true)
expect(c.is_desktop()).to_equal(false)
```

</details>

#### android is mobile

- android is mobile
   - Expected: c.is_mobile() is true
   - Expected: c.is_desktop() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("android is mobile")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "android", arch: "aarch64")
expect(c.is_mobile()).to_equal(true)
expect(c.is_desktop()).to_equal(false)
```

</details>

#### wasm platforms

#### wasm32 is wasm

- wasm32 is wasm
   - Expected: c.is_wasm() is true
   - Expected: c.is_desktop() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wasm32 is wasm")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "wasi", arch: "wasm32")
expect(c.is_wasm()).to_equal(true)
expect(c.is_desktop()).to_equal(false)
```

</details>

#### wasm64 is wasm

- wasm64 is wasm
   - Expected: c.is_wasm() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wasm64 is wasm")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "wasi", arch: "wasm64")
expect(c.is_wasm()).to_equal(true)
```

</details>

#### bare-metal

#### none platform is baremetal

- none platform is baremetal
   - Expected: c.is_baremetal() is true
   - Expected: c.is_desktop() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("none platform is baremetal")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "none", arch: "riscv32")
expect(c.is_baremetal()).to_equal(true)
expect(c.is_desktop()).to_equal(false)
```

</details>

#### bitness

#### x86_64 is 64-bit

- x86_64 is 64-bit
   - Expected: c.is_64bit() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86_64 is 64-bit")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "linux", arch: "x86_64")
expect(c.is_64bit()).to_equal(true)
```

</details>

#### aarch64 is 64-bit

- aarch64 is 64-bit
   - Expected: c.is_64bit() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aarch64 is 64-bit")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "ios", arch: "aarch64")
expect(c.is_64bit()).to_equal(true)
```

</details>

#### riscv64 is 64-bit

- riscv64 is 64-bit
   - Expected: c.is_64bit() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv64 is 64-bit")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "linux", arch: "riscv64")
expect(c.is_64bit()).to_equal(true)
```

</details>

#### wasm32 is not 64-bit

- wasm32 is not 64-bit
   - Expected: c.is_64bit() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wasm32 is not 64-bit")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "wasi", arch: "wasm32")
expect(c.is_64bit()).to_equal(false)
```

</details>

#### riscv32 is not 64-bit

- riscv32 is not 64-bit
   - Expected: c.is_64bit() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv32 is not 64-bit")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "none", arch: "riscv32")
expect(c.is_64bit()).to_equal(false)
```

</details>

#### platform exclusivity

#### desktop is not mobile, wasm, or baremetal

- desktop is not mobile, wasm, or baremetal
   - Expected: c.is_desktop() is true
   - Expected: c.is_mobile() is false
   - Expected: c.is_wasm() is false
   - Expected: c.is_baremetal() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("desktop is not mobile, wasm, or baremetal")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "linux", arch: "x86_64")
expect(c.is_desktop()).to_equal(true)
expect(c.is_mobile()).to_equal(false)
expect(c.is_wasm()).to_equal(false)
expect(c.is_baremetal()).to_equal(false)
```

</details>

#### mobile is not desktop, wasm, or baremetal

- mobile is not desktop, wasm, or baremetal
   - Expected: c.is_mobile() is true
   - Expected: c.is_desktop() is false
   - Expected: c.is_wasm() is false
   - Expected: c.is_baremetal() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mobile is not desktop, wasm, or baremetal")
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "android", arch: "aarch64")
expect(c.is_mobile()).to_equal(true)
expect(c.is_desktop()).to_equal(false)
expect(c.is_wasm()).to_equal(false)
expect(c.is_baremetal()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/platform_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AppConfig platform detection.
- AppConfig platform detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c151f691ebcb70dbf8f1de811dfaa7354b96049211df06ace9de86a357dbf340`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c151f691ebcb70dbf8f1de811dfaa7354b96049211df06ace9de86a357dbf340`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c151f691ebcb70dbf8f1de811dfaa7354b96049211df06ace9de86a357dbf340`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/platform_spec.spl
mirror: doc/06_spec/unit/app/platform_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/platform_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/platform_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/platform_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects a known platform' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/platform_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects a known architecture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/platform_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'linux is desktop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
