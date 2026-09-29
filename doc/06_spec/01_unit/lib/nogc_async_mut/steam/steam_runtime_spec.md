# Steam Runtime Specification

> Tests covering Steam runtime detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Steam Runtime Specification

## Scenarios

### Steam runtime detection

#### detect with full soldier evidence returns is_ok=true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detect with full soldier evidence returns is_ok=true
   - Expected: info.is_ok is true
   - Expected: info.generation equals `soldier`
   - Expected: info.abi equals `x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detect with full soldier evidence returns is_ok=true")
val info = steam_runtime_detect("steam-runtime abi-x86_64 soldier")
expect(info.is_ok).to_equal(true)
expect(info.generation).to_equal("soldier")
expect(info.abi).to_equal("x86_64")
```

</details>

#### detect with sniper generation returns is_ok=true

- detect with sniper generation returns is_ok=true
   - Expected: info.is_ok is true
   - Expected: info.generation equals `sniper`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detect with sniper generation returns is_ok=true")
val info = steam_runtime_detect("steam-runtime abi-x86_64 sniper")
expect(info.is_ok).to_equal(true)
expect(info.generation).to_equal("sniper")
```

</details>

#### detect without steam-runtime token returns error

- detect without steam-runtime token returns error
   - Expected: info.is_ok is false
   - Expected: info.error equals `missing-steam-runtime`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detect without steam-runtime token returns error")
val info = steam_runtime_detect("abi-x86_64 soldier")
expect(info.is_ok).to_equal(false)
expect(info.error).to_equal("missing-steam-runtime")
```

</details>

#### detect without abi-x86_64 token returns error

- detect without abi-x86_64 token returns error
   - Expected: info.is_ok is false
   - Expected: info.error equals `missing-abi-x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detect without abi-x86_64 token returns error")
val info = steam_runtime_detect("steam-runtime soldier")
expect(info.is_ok).to_equal(false)
expect(info.error).to_equal("missing-abi-x86_64")
```

</details>

#### detect without generation token returns error

- detect without generation token returns error
   - Expected: info.is_ok is false
   - Expected: info.error equals `missing-steam-linux-runtime-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detect without generation token returns error")
val info = steam_runtime_detect("steam-runtime abi-x86_64")
expect(info.is_ok).to_equal(false)
expect(info.error).to_equal("missing-steam-linux-runtime-generation")
```

</details>

#### library_path is non-empty for valid info

- library_path is non-empty for valid info


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("library_path is non-empty for valid info")
val info = steam_runtime_detect("steam-runtime abi-x86_64 soldier")
val path = steam_runtime_library_path(info)
expect(path).to_contain("soldier")
```

</details>

#### library_path is empty for invalid info

- library_path is empty for invalid info
   - Expected: path equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("library_path is empty for invalid info")
val info = steam_runtime_detect("")
val path = steam_runtime_library_path(info)
expect(path).to_equal("")
```

</details>

#### rootfs_mount returns non-empty path for valid info

- rootfs_mount returns non-empty path for valid info


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rootfs_mount returns non-empty path for valid info")
val info = steam_runtime_detect("steam-runtime abi-x86_64 soldier")
val mount = steam_runtime_rootfs_mount(info)
expect(mount).to_contain("pressure-vessel")
```

</details>

#### rootfs_mount returns empty string for invalid info

- rootfs_mount returns empty string for invalid info
   - Expected: steam_runtime_rootfs_mount(info) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rootfs_mount returns empty string for invalid info")
val info = steam_runtime_detect("")
expect(steam_runtime_rootfs_mount(info)).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/steam/steam_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Steam runtime detection.
- Steam runtime detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `f112d052ad8f2a44a6075a4721fd570d050df81933a37d9f78c017a36ff30c0c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f112d052ad8f2a44a6075a4721fd570d050df81933a37d9f78c017a36ff30c0c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f112d052ad8f2a44a6075a4721fd570d050df81933a37d9f78c017a36ff30c0c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/steam/steam_runtime_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/steam/steam_runtime_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/steam/steam_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/steam/steam_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/steam/steam_runtime_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detect with full soldier evidence returns is_ok=true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/steam/steam_runtime_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detect with sniper generation returns is_ok=true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/steam/steam_runtime_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detect without steam-runtime token returns error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
