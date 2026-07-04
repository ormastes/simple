# Capability Revoke Depth Specification (E3/E4)

> Regression spec for E3 (transitive revoke) and E4 (delegation depth).

<!-- sdn-diagram:id=capability_revoke_depth_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=capability_revoke_depth_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

capability_revoke_depth_spec -> std
capability_revoke_depth_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=capability_revoke_depth_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capability Revoke Depth Specification (E3/E4)

Regression spec for E3 (transitive revoke) and E4 (delegation depth).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-E3 #OS-E4 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/runtime/escalation_fixes_2026-06-11.md |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/kernel/ipc/capability/capability_revoke_depth_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression spec for E3 (transitive revoke) and E4 (delegation depth).

E3: grants carry provenance (token_id + parent_token_id). revoke_transitive
    on a root token also revokes every grant derived from it.

E4: CapabilityToken.depth is the remaining delegation budget. grant()
    decrements depth; at depth=0 further delegation is DENIED.
    Default depth for fresh grants is 2.

## Scenarios

### CapabilityManager revoke_transitive E3
_Transitive revocation walks the delegation ancestry._

#### grant builds provenance chain: child parent_token_id links to root

- var mgr = CapabilityManager new
- mgr init task record
   - Expected: ok is true
   - Expected: child.parent_token_id equals `root_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val t1 = TaskId(id: 1)
val t2 = TaskId(id: 2)
mgr.init_task_record(t1, true)
# Grab the root token (FileRead) from t1's record
val rec1_opt = mgr._find_record(t1)
val rec1 = rec1_opt
val root_tok = rec1.caps.caps[0]
val root_id = root_tok.token_id
# Grant to t2
val ok = mgr.grant(t1, t2, root_tok)
expect(ok).to_equal(true)
# Find the child token in t2
val rec2_opt = mgr._find_record(t2)
val rec2 = rec2_opt
val child = rec2.caps.caps[0]
expect(child.parent_token_id).to_equal(root_id)
```

</details>

#### revoke_transitive removes child token from delegate after revoking root

- var mgr = CapabilityManager new
- mgr init task record
   - Expected: before is true
- mgr grant
   - Expected: t2_before is true
   - Expected: t2_after is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val t1 = TaskId(id: 10)
val t2 = TaskId(id: 20)
mgr.init_task_record(t1, true)
val rec1_opt = mgr._find_record(t1)
val rec1 = rec1_opt
val root_tok = rec1.caps.caps[0]
val root_id = root_tok.token_id
# Confirm t1 can check FileRead before anything
val before = mgr.check(t1, CapabilityKind.FileRead(path_prefix: ""))
expect(before).to_equal(true)
# Grant to t2
mgr.grant(t1, t2, root_tok)
# Confirm t2 has FileRead
val t2_before = mgr.check(t2, CapabilityKind.FileRead(path_prefix: ""))
expect(t2_before).to_equal(true)
# Transitive revoke from root
val count = mgr.revoke_transitive(root_id)
# At least the root token was revoked
expect(count).to_be_greater_than(0)
# t2 must no longer pass the check
val t2_after = mgr.check(t2, CapabilityKind.FileRead(path_prefix: ""))
expect(t2_after).to_equal(false)
```

</details>

#### revoke_transitive returns count of tokens removed

- var mgr = CapabilityManager new
- mgr init task record
- mgr grant
- mgr grant
   - Expected: count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val t1 = TaskId(id: 1)
val t2 = TaskId(id: 2)
val t3 = TaskId(id: 3)
mgr.init_task_record(t1, true)
val rec_opt = mgr._find_record(t1)
val rec = rec_opt
val root_tok = rec.caps.caps[0]
val root_id = root_tok.token_id
mgr.grant(t1, t2, root_tok)
# Re-read root token (same root, depth still > 0 for t1)
val rec_again_opt = mgr._find_record(t1)
val rec_again = rec_again_opt
val root_tok2 = rec_again.caps.caps[0]
mgr.grant(t1, t3, root_tok2)
val count = mgr.revoke_transitive(root_id)
# root + 2 derived = 3
expect(count).to_equal(3)
```

</details>

#### _ensure_record deny-all default still holds for unknown principal

- var mgr = CapabilityManager new
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val unknown = TaskId(id: 999)
val result = mgr.check(unknown, CapabilityKind.FileRead(path_prefix: ""))
expect(result).to_equal(false)
```

</details>

#### revoke_transitive of last unpledged token stays deny-all

- var mgr = CapabilityManager new
- mgr init task
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is true
   - Expected: count equals `1`
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val task = TaskId(id: 77)
val token = CapabilityToken(
    kind: CapabilityKind.ProcessSpawn,
    generation: 1u64,
    owner: 77u64,
    token_id: 9u64,
    parent_token_id: 0u64,
    depth: 1
)
mgr.init_task(task, CapabilitySet(caps: [token], is_pledged: false))
expect(mgr.check(task, CapabilityKind.ProcessSpawn)).to_equal(true)
val count = mgr.revoke_transitive(9u64)
expect(count).to_equal(1)
expect(mgr.check(task, CapabilityKind.ProcessSpawn)).to_equal(false)
```

</details>

### CapabilityManager delegation depth E4
_Delegation depth is decremented on grant; exhausted depth is denied._

#### fresh grant has default depth 2

- var mgr = CapabilityManager new
- mgr init task record
   - Expected: tok.depth equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val t1 = TaskId(id: 1)
mgr.init_task_record(t1, true)
val rec_opt = mgr._find_record(t1)
val rec = rec_opt
val tok = rec.caps.caps[0]
expect(tok.depth).to_equal(2)
```

</details>

#### depth decrements by 1 on each delegation

- var mgr = CapabilityManager new
- mgr init task record
   - Expected: root_tok.depth equals `2`
- mgr grant
   - Expected: child.depth equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val t1 = TaskId(id: 1)
val t2 = TaskId(id: 2)
mgr.init_task_record(t1, true)
val rec_opt = mgr._find_record(t1)
val rec = rec_opt
val root_tok = rec.caps.caps[0]
expect(root_tok.depth).to_equal(2)
mgr.grant(t1, t2, root_tok)
val rec2_opt = mgr._find_record(t2)
val rec2 = rec2_opt
val child = rec2.caps.caps[0]
expect(child.depth).to_equal(1)
```

</details>

#### depth-2 chain: root→t2→t3 works (depth reaches 0 at t3)

- var mgr = CapabilityManager new
- mgr init task record
   - Expected: ok1 is true
   - Expected: child.depth equals `1`
   - Expected: ok2 is true
   - Expected: grandchild.depth equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val t1 = TaskId(id: 1)
val t2 = TaskId(id: 2)
val t3 = TaskId(id: 3)
mgr.init_task_record(t1, true)
val rec1_opt = mgr._find_record(t1)
val rec1 = rec1_opt
val root = rec1.caps.caps[0]
# First hop: t1→t2
val ok1 = mgr.grant(t1, t2, root)
expect(ok1).to_equal(true)
# Second hop: t2→t3 using t2's child token
val rec2_opt = mgr._find_record(t2)
val rec2 = rec2_opt
val child = rec2.caps.caps[0]
expect(child.depth).to_equal(1)
val ok2 = mgr.grant(t2, t3, child)
expect(ok2).to_equal(true)
# t3 gets depth=0
val rec3_opt = mgr._find_record(t3)
val rec3 = rec3_opt
val grandchild = rec3.caps.caps[0]
expect(grandchild.depth).to_equal(0)
```

</details>

#### delegation denied when depth is 0

- var mgr = CapabilityManager new
- mgr init task record
- mgr grant
- mgr grant
   - Expected: grandchild.depth equals `0`
   - Expected: denied is false
   - Expected: t4_check is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val t1 = TaskId(id: 1)
val t2 = TaskId(id: 2)
val t3 = TaskId(id: 3)
val t4 = TaskId(id: 4)
mgr.init_task_record(t1, true)
val rec1_opt = mgr._find_record(t1)
val rec1 = rec1_opt
val root = rec1.caps.caps[0]
# t1→t2 (depth 2→1)
mgr.grant(t1, t2, root)
val rec2_opt = mgr._find_record(t2)
val rec2 = rec2_opt
val child = rec2.caps.caps[0]
# t2→t3 (depth 1→0)
mgr.grant(t2, t3, child)
val rec3_opt = mgr._find_record(t3)
val rec3 = rec3_opt
val grandchild = rec3.caps.caps[0]
expect(grandchild.depth).to_equal(0)
# t3→t4 must FAIL: depth=0
val denied = mgr.grant(t3, t4, grandchild)
expect(denied).to_equal(false)
# t4 must have no capability
val t4_check = mgr.check(t4, CapabilityKind.FileRead(path_prefix: ""))
expect(t4_check).to_equal(false)
```

</details>

#### full revoke after delegation chain: all principals denied

- var mgr = CapabilityManager new
- mgr init task record
- mgr grant
- mgr grant
- mgr revoke transitive
   - Expected: t2_check is false
   - Expected: t3_check is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CapabilityManager.new()
val t1 = TaskId(id: 1)
val t2 = TaskId(id: 2)
val t3 = TaskId(id: 3)
mgr.init_task_record(t1, true)
val rec1_opt = mgr._find_record(t1)
val rec1 = rec1_opt
val root = rec1.caps.caps[0]
val root_id = root.token_id
mgr.grant(t1, t2, root)
val rec2_opt = mgr._find_record(t2)
val rec2 = rec2_opt
val child = rec2.caps.caps[0]
mgr.grant(t2, t3, child)
# Revoke transitively from root
mgr.revoke_transitive(root_id)
# Both t2 and t3 must fail
val t2_check = mgr.check(t2, CapabilityKind.FileRead(path_prefix: ""))
val t3_check = mgr.check(t3, CapabilityKind.FileRead(path_prefix: ""))
expect(t2_check).to_equal(false)
expect(t3_check).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/runtime/escalation_fixes_2026-06-11.md](doc/03_plan/runtime/escalation_fixes_2026-06-11.md)


</details>
