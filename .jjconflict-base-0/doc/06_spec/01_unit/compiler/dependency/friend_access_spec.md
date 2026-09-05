# Friend Access Specification

> Tests covering Extended Visibility Enum, DirManifest Friend Declarations, Friend Access Checking.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Friend Access Specification

## Scenarios

### Extended Visibility Enum

#### Public has rank 3

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Public has rank 3
   - Expected: rank equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Public has rank 3")
# Public = highest visibility
val rank = 3
expect(rank).to_equal(3)
```

</details>

#### Internal has rank 2

- Internal has rank 2
   - Expected: rank equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Internal has rank 2")
# Internal = friend-visible
val rank = 2
expect(rank).to_equal(2)
```

</details>

#### Package has rank 1

- Package has rank 1
   - Expected: rank equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Package has rank 1")
# Package = same-package only
val rank = 1
expect(rank).to_equal(1)
```

</details>

#### Private has rank 0

- Private has rank 0
   - Expected: rank equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Private has rank 0")
# Private = same-file only
val rank = 0
expect(rank).to_equal(0)
```

</details>

#### visibility_meet returns more restrictive

- visibility_meet returns more restrictive
   - Expected: meet equals `2`
   - Expected: meet2 equals `0`
   - Expected: meet3 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("visibility_meet returns more restrictive")
# Public meet Internal = Internal (min rank)
val r1 = 3
val r2 = 2
var meet = r1
if r2 < meet:
    meet = r2
expect(meet).to_equal(2)

# Internal meet Private = Private
val r3 = 2
val r4 = 0
var meet2 = r3
if r4 < meet2:
    meet2 = r4
expect(meet2).to_equal(0)

# Package meet Package = Package
val r5 = 1
val r6 = 1
var meet3 = r5
if r6 < meet3:
    meet3 = r6
expect(meet3).to_equal(1)
```

</details>

#### marker returns correct single character

- marker returns correct single character
   - Expected: markers[0] equals `P`
   - Expected: markers[1] equals `F`
   - Expected: markers[2] equals `I`
   - Expected: markers[3] equals `-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("marker returns correct single character")
# Visibility markers: P=Public, F=Friend, I=Internal, -=Private
val markers = ["P", "F", "I", "-"]
expect(markers[0]).to_equal("P")
expect(markers[1]).to_equal("F")
expect(markers[2]).to_equal("I")
expect(markers[3]).to_equal("-")
```

</details>

### DirManifest Friend Declarations

#### new manifest has no friends

- new manifest has no friends
   - Expected: friends.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("new manifest has no friends")
var friends: [text] = []
expect(friends.len()).to_equal(0)
```

</details>

#### can add friend packages

- can add friend packages
   - Expected: friends.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("can add friend packages")
var friends: [text] = []
friends.push("types")
friends.push("mir")
expect(friends.len()).to_equal(2)
```

</details>

#### is_friend returns true for declared friend

- is_friend returns true for declared friend
   - Expected: found_types is true
   - Expected: found_mir is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is_friend returns true for declared friend")
var friends: [text] = ["types", "mir"]
var found_types = false
var found_mir = false
for f in friends:
    if f == "types":
        found_types = true
    if f == "mir":
        found_mir = true
expect(found_types).to_equal(true)
expect(found_mir).to_equal(true)
```

</details>

#### is_friend returns false for non-friend

- is_friend returns false for non-friend
   - Expected: found_backend is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is_friend returns false for non-friend")
var friends: [text] = ["types"]
var found_backend = false
for f in friends:
    if f == "backend":
        found_backend = true
expect(found_backend).to_equal(false)
```

</details>

#### can add internal exports

- can add internal exports
   - Expected: internal_exports.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("can add internal exports")
var internal_exports: [text] = []
internal_exports.push("HirLowering")
internal_exports.push("HirBuilder")
expect(internal_exports.len()).to_equal(2)
```

</details>

#### is_internal_export checks correctly

- is_internal_export checks correctly
   - Expected: found_lowering is true
   - Expected: found_other is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is_internal_export checks correctly")
var internal_exports: [text] = ["HirLowering"]
var found_lowering = false
var found_other = false
for e in internal_exports:
    if e == "HirLowering":
        found_lowering = true
    if e == "NotExported":
        found_other = true
expect(found_lowering).to_equal(true)
expect(found_other).to_equal(false)
```

</details>

### Friend Access Checking

#### public symbols are always accessible

- public symbols are always accessible
   - Expected: visibility_rank >= 3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("public symbols are always accessible")
# Public = rank 3, always accessible
val visibility_rank = 3
expect(visibility_rank >= 3).to_equal(true)
```

</details>

#### internal symbols accessible by friends

- internal symbols accessible by friends
   - Expected: accessible is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("internal symbols accessible by friends")
var friends: [text] = ["mir"]
val caller = "mir"
var is_friend = false
for f in friends:
    if f == caller:
        is_friend = true
val visibility_rank = 2  # Internal
val accessible = visibility_rank >= 3 or is_friend
expect(accessible).to_equal(true)
```

</details>

#### internal symbols not accessible by non-friends

- internal symbols not accessible by non-friends
   - Expected: accessible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("internal symbols not accessible by non-friends")
var friends: [text] = ["mir"]
val caller = "backend"
var is_friend = false
for f in friends:
    if f == caller:
        is_friend = true
val visibility_rank = 2  # Internal
val accessible = visibility_rank >= 3 or is_friend
expect(accessible).to_equal(false)
```

</details>

#### package symbols accessible within same package

- package symbols accessible within same package
   - Expected: accessible is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("package symbols accessible within same package")
val owner_pkg = "hir"
val caller_pkg = "hir"
val visibility_rank = 1  # Package
val accessible = caller_pkg == owner_pkg
expect(accessible).to_equal(true)
```

</details>

#### package symbols not accessible from other packages

- package symbols not accessible from other packages
   - Expected: accessible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("package symbols not accessible from other packages")
val owner_pkg = "hir"
val caller_pkg = "mir"
val visibility_rank = 1  # Package
val accessible = caller_pkg == owner_pkg
expect(accessible).to_equal(false)
```

</details>

#### private symbols never accessible from outside

- private symbols never accessible from outside
   - Expected: accessible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("private symbols never accessible from outside")
var friends: [text] = ["mir"]
val caller = "mir"
val visibility_rank = 0  # Private
# Private is never accessible from outside, even for friends
val accessible = visibility_rank >= 1
expect(accessible).to_equal(false)
```

</details>

#### friend access is non-transitive

- friend access is non-transitive
   - Expected: is_friend is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("friend access is non-transitive")
# hir friends mir, mir friends backend
# backend should NOT have access to hir internals
var hir_friends: [text] = ["mir"]
val caller = "backend"
var is_friend = false
for f in hir_friends:
    if f == caller:
        is_friend = true
# backend is NOT a friend of hir
expect(is_friend).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/dependency/friend_access_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Extended Visibility Enum, DirManifest Friend Declarations, Friend Access Checking.
- Extended Visibility Enum
- DirManifest Friend Declarations
- Friend Access Checking

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f36d1eafad6328b5642bbd8aa9ced1b5b5bf6ef5afe6e226139935e1ede4f81c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f36d1eafad6328b5642bbd8aa9ced1b5b5bf6ef5afe6e226139935e1ede4f81c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f36d1eafad6328b5642bbd8aa9ced1b5b5bf6ef5afe6e226139935e1ede4f81c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/compiler/dependency/friend_access_spec.spl
mirror: doc/06_spec/01_unit/compiler/dependency/friend_access_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/dependency/friend_access_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/dependency/friend_access_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/dependency/friend_access_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/dependency/friend_access_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Public has rank 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/dependency/friend_access_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Internal has rank 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/dependency/friend_access_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Package has rank 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/dependency/friend_access_spec.spl:122:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can add friend packages' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/dependency/friend_access_spec.spl:154:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can add internal exports' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
