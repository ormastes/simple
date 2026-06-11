# Target Spec Specification

> <details>

<!-- sdn-diagram:id=target_spec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=target_spec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

target_spec_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=target_spec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Target Spec Specification

## Scenarios

### Target Spec Architecture Matching

#### matches exact arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], false, "", false, "", false, "",
    [], [],
    "x86_64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.Matched: check(true)
    case _: check(false)
```

</details>

#### does not match different arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["aarch64"], false, "", false, "", false, "",
    [], [],
    "x86_64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.NotMatched: check(true)
    case _: check(false)
```

</details>

#### matches with pipe group

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64", "x86"], false, "", false, "", false, "",
    [], [],
    "x86", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.Matched: check(true)
    case _: check(false)
```

</details>

#### normalizes arch aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["amd64"], false, "", false, "", false, "",
    [], [],
    "x86_64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.Matched: check(true)
    case _: check(false)
```

</details>

#### normalizes arm64 alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["arm64"], false, "", false, "", false, "",
    [], [],
    "aarch64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.Matched: check(true)
    case _: check(false)
```

</details>

### Target Spec OS Matching

#### matches with OS specified

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], true, "linux", false, "", false, "",
    [], [],
    "x86_64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.Matched: check(true)
    case _: check(false)
```

</details>

#### does not match wrong OS

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], true, "windows", false, "", false, "",
    [], [],
    "x86_64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.NotMatched: check(true)
    case _: check(false)
```

</details>

#### wildcard OS matches any

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], true, "_", false, "", false, "",
    [], [],
    "x86_64", "freebsd", "gnu", "llvm", 15
)
match result:
    case MatchResult.Matched: check(true)
    case _: check(false)
```

</details>

#### omitted OS matches any

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], false, "", false, "", false, "",
    [], [],
    "x86_64", "windows", "msvc", "llvm", 15
)
match result:
    case MatchResult.Matched: check(true)
    case _: check(false)
```

</details>

### Target Spec ABI and Backend Matching

#### matches with ABI specified

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], true, "linux", true, "gnu", false, "",
    [], [],
    "x86_64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.Matched: check(true)
    case _: check(false)
```

</details>

#### does not match wrong ABI

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], true, "windows", true, "msvc", false, "",
    [], [],
    "x86_64", "windows", "gnu", "llvm", 15
)
match result:
    case MatchResult.NotMatched: check(true)
    case _: check(false)
```

</details>

#### matches with backend specified

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], false, "", false, "", true, "llvm",
    [], [],
    "x86_64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.Matched: check(true)
    case _: check(false)
```

</details>

#### does not match wrong backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], false, "", false, "", true, "cranelift",
    [], [],
    "x86_64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.NotMatched: check(true)
    case _: check(false)
```

</details>

### Target Spec Version Constraints

#### matches >= constraint

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], false, "", false, "", true, "llvm",
    [">="], [15],
    "x86_64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.Matched: check(true)
    case _: check(false)
```

</details>

#### fails >= constraint when too low

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], false, "", false, "", true, "llvm",
    [">="], [16],
    "x86_64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.NotMatched: check(true)
    case _: check(false)
```

</details>

#### matches == constraint

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], false, "", false, "", true, "llvm",
    ["=="], [17],
    "x86_64", "linux", "gnu", "llvm", 17
)
match result:
    case MatchResult.Matched: check(true)
    case _: check(false)
```

</details>

#### fails == constraint when different

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], false, "", false, "", true, "llvm",
    ["=="], [17],
    "x86_64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.NotMatched: check(true)
    case _: check(false)
```

</details>

#### matches < constraint

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], false, "", false, "", true, "llvm",
    ["<"], [18],
    "x86_64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.Matched: check(true)
    case _: check(false)
```

</details>

#### returns note for ~= constraint with different version

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], false, "", false, "", true, "llvm",
    ["~="], [17],
    "x86_64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.MatchedWithNote(msg):
        check(msg.contains("recommended"))
    case _: check(false)
```

</details>

#### returns Matched for ~= constraint with matching version

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], false, "", false, "", true, "llvm",
    ["~="], [17],
    "x86_64", "linux", "gnu", "llvm", 17
)
match result:
    case MatchResult.Matched: check(true)
    case _: check(false)
```

</details>

#### matches range constraint >= and <

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = match_target_spec(
    ["x86_64"], false, "", false, "", true, "llvm",
    [">=", "<"], [14, 18],
    "x86_64", "linux", "gnu", "llvm", 15
)
match result:
    case MatchResult.Matched: check(true)
    case _: check(false)
```

</details>

### Target Spec Exhaustiveness

#### reports missing archs when no wildcard

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arms_archs = [["x86_64"], ["aarch64"]]
val arms_is_wildcard = [false, false]
val all = all_target_archs()
val missing = check_exhaustiveness(arms_archs, arms_is_wildcard, all)
check(missing.len() > 0)
# x86_64 and aarch64 are covered, others should be missing
check(missing.contains("arm"))
check(missing.contains("riscv64"))
```

</details>

#### reports no missing archs when wildcard present

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arms_archs = [["x86_64"], []]
val arms_is_wildcard = [false, true]
val all = all_target_archs()
val missing = check_exhaustiveness(arms_archs, arms_is_wildcard, all)
check(missing.len() == 0)
```

</details>

#### reports all archs missing when no arms

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arms_archs: [[text]] = []
val arms_is_wildcard: [bool] = []
val all = all_target_archs()
val missing = check_exhaustiveness(arms_archs, arms_is_wildcard, all)
check(missing.len() == all.len())
```

</details>

#### handles pipe groups in exhaustiveness

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arms_archs = [["x86_64", "x86"], ["aarch64", "arm"], ["riscv32", "riscv64"], ["wasm32", "wasm64"], ["avr"], ["mcs51"], ["msp430"]]
val arms_is_wildcard = [false, false, false, false, false, false, false]
val all = all_target_archs()
val missing = check_exhaustiveness(arms_archs, arms_is_wildcard, all)
check(missing.len() == 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/target_spec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Target Spec Architecture Matching
- Target Spec OS Matching
- Target Spec ABI and Backend Matching
- Target Spec Version Constraints
- Target Spec Exhaustiveness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
