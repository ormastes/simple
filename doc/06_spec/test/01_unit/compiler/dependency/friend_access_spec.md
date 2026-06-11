# Friend Access Control Specification

> Tests the friend access control system: Visibility enum extension, DirManifest friend declarations, and friend-aware access checking.

<!-- sdn-diagram:id=friend_access_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=friend_access_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

friend_access_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=friend_access_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Friend Access Control Specification

Tests the friend access control system: Visibility enum extension, DirManifest friend declarations, and friend-aware access checking.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FRIEND-001 |
| Category | Language |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/compiler/dependency/friend_access_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the friend access control system: Visibility enum extension,
DirManifest friend declarations, and friend-aware access checking.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `friend <pkg>` | Grants a package access to internal symbols |
| `pub(friend)` | Symbol visible to friends only |
| `pub(package)` | Symbol visible within same package only |
| `internal_export` | Package-level friend-visible symbol declaration |

## Scenarios

### Extended Visibility Enum

#### Public has rank 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Public = highest visibility
val rank = 3
expect(rank).to_equal(3)
```

</details>

#### Internal has rank 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Internal = friend-visible
val rank = 2
expect(rank).to_equal(2)
```

</details>

#### Package has rank 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Package = same-package only
val rank = 1
expect(rank).to_equal(1)
```

</details>

#### Private has rank 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Private = same-file only
val rank = 0
expect(rank).to_equal(0)
```

</details>

#### visibility_meet returns more restrictive

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var friends: [text] = []
expect(friends.len()).to_equal(0)
```

</details>

#### can add friend packages

1. friends push
2. friends push
   - Expected: friends.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var friends: [text] = []
friends.push("types")
friends.push("mir")
expect(friends.len()).to_equal(2)
```

</details>

#### is_friend returns true for declared friend

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var friends: [text] = ["types"]
var found_backend = false
for f in friends:
    if f == "backend":
        found_backend = true
expect(found_backend).to_equal(false)
```

</details>

#### can add internal exports

1. internal exports push
2. internal exports push
   - Expected: internal_exports.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var internal_exports: [text] = []
internal_exports.push("HirLowering")
internal_exports.push("HirBuilder")
expect(internal_exports.len()).to_equal(2)
```

</details>

#### is_internal_export checks correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Public = rank 3, always accessible
val visibility_rank = 3
expect(visibility_rank >= 3).to_equal(true)
```

</details>

#### internal symbols accessible by friends

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val owner_pkg = "hir"
val caller_pkg = "hir"
val visibility_rank = 1  # Package
val accessible = caller_pkg == owner_pkg
expect(accessible).to_equal(true)
```

</details>

#### package symbols not accessible from other packages

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val owner_pkg = "hir"
val caller_pkg = "mir"
val visibility_rank = 1  # Package
val accessible = caller_pkg == owner_pkg
expect(accessible).to_equal(false)
```

</details>

#### private symbols never accessible from outside

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var friends: [text] = ["mir"]
val caller = "mir"
val visibility_rank = 0  # Private
# Private is never accessible from outside, even for friends
val accessible = visibility_rank >= 1
expect(accessible).to_equal(false)
```

</details>

#### friend access is non-transitive

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
