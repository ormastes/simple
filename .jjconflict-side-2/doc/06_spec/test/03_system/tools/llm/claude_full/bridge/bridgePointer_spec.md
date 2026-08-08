# Claude Full Bridge Pointer

> Mirrors crash-recovery bridge pointer path, validation, TTL, clearing, and worktree fanout behavior.

<!-- sdn-diagram:id=bridgePointer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bridgePointer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bridgePointer_spec -> std
bridgePointer_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bridgePointer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Pointer

Mirrors crash-recovery bridge pointer path, validation, TTL, clearing, and worktree fanout behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/bridgePointer_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors crash-recovery bridge pointer path, validation, TTL, clearing, and worktree fanout behavior.

## Scenarios

### Claude full bridge pointer

#### builds sanitized per-directory pointer paths

- Derive the projects-dir path used for crash recovery
   - Expected: bridgePointerFileName() equals `bridge-pointer.json`
   - Expected: getBridgePointerPath("/projects/", "/repo/main") equals `/projects/-repo-main/bridge-pointer.json`
   - Expected: sanitizeBridgePointerPath("C:\\repo work") equals `C-repo-work`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Derive the projects-dir path used for crash recovery")
expect(bridgePointerFileName()).to_equal("bridge-pointer.json")
expect(getBridgePointerPath("/projects/", "/repo/main")).to_equal("/projects/-repo-main/bridge-pointer.json")
expect(sanitizeBridgePointerPath("C:\\repo work")).to_equal("C-repo-work")
```

</details>

#### writes and reads a fresh pointer with age

- Persist a standalone pointer and read it before TTL expiry
- store write
   - Expected: read.found is true
   - Expected: read.pointer.sessionId equals `cse_1`
   - Expected: read.pointer.environmentId equals `env_1`
   - Expected: read.pointer.sourceStandalone() is true
   - Expected: read.ageMs equals `500`
   - Expected: store.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Persist a standalone pointer and read it before TTL expiry")
val store = BridgePointerStore.new("/projects")
store.write("/repo", BridgePointer.new("cse_1", "env_1", "standalone"), 1000)
val read = store.read("/repo", 1500)
expect(read.found).to_equal(true)
expect(read.pointer.sessionId).to_equal("cse_1")
expect(read.pointer.environmentId).to_equal("env_1")
expect(read.pointer.sourceStandalone()).to_equal(true)
expect(read.ageMs).to_equal(500)
expect(store.count()).to_equal(1)
```

</details>

#### clears corrupt, invalid, and stale pointers

- Reject pointers that would keep re-prompting after backend GC
- store writeCorrupt
   - Expected: corrupt.found is false
   - Expected: corrupt.cleared is true
   - Expected: corrupt.reason equals `invalid-json`
- store writeInvalidSchema
   - Expected: invalid.cleared is true
   - Expected: invalid.reason equals `invalid-schema`
- store write
   - Expected: stale.cleared is true
   - Expected: stale.reason equals `stale`
   - Expected: store.count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject pointers that would keep re-prompting after backend GC")
val store = BridgePointerStore.new("/projects")
store.writeCorrupt("/corrupt", 1000)
val corrupt = store.read("/corrupt", 1100)
expect(corrupt.found).to_equal(false)
expect(corrupt.cleared).to_equal(true)
expect(corrupt.reason).to_equal("invalid-json")
store.writeInvalidSchema("/invalid", BridgePointer.new("cse_2", "env_2", "other"), 1000)
val invalid = store.read("/invalid", 1100)
expect(invalid.cleared).to_equal(true)
expect(invalid.reason).to_equal("invalid-schema")
store.write("/stale", BridgePointer.new("cse_3", "env_3", "repl"), 0)
val stale = store.read("/stale", bridgePointerTtlMs() + 1)
expect(stale.cleared).to_equal(true)
expect(stale.reason).to_equal("stale")
expect(store.count()).to_equal(0)
```

</details>

#### uses current directory fast path before worktree fanout

- Return the current directory pointer without scanning siblings
- store write
- store write
   - Expected: result.found is true
   - Expected: result.dir equals `/repo`
   - Expected: result.pointer.sessionId equals `cse_here`
   - Expected: result.ageMs equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Return the current directory pointer without scanning siblings")
val store = BridgePointerStore.new("/projects")
store.write("/repo", BridgePointer.new("cse_here", "env_here", "standalone"), 1000)
store.write("/repo-wt", BridgePointer.new("cse_other", "env_other", "repl"), 1400)
val result = store.readAcrossWorktrees("/repo", ["/repo", "/repo-wt"], 1500)
expect(result.found).to_equal(true)
expect(result.dir).to_equal("/repo")
expect(result.pointer.sessionId).to_equal("cse_here")
expect(result.ageMs).to_equal(500)
```

</details>

#### selects the freshest pointer across worktrees and caps fanout

- Fan out only when current directory misses
- store write
- store write
   - Expected: found.found is true
   - Expected: found.dir equals `/fresh`
   - Expected: found.pointer.sessionId equals `cse_fresh`
   - Expected: found.ageMs equals `100`
   - Expected: tooMany.found is false
   - Expected: tooMany.skippedFanout is true
   - Expected: maxWorktreeFanout() equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fan out only when current directory misses")
val store = BridgePointerStore.new("/projects")
store.write("/old", BridgePointer.new("cse_old", "env_old", "repl"), 1000)
store.write("/fresh", BridgePointer.new("cse_fresh", "env_fresh", "repl"), 1900)
val found = store.readAcrossWorktrees("/missing", ["/missing", "/old", "/fresh"], 2000)
expect(found.found).to_equal(true)
expect(found.dir).to_equal("/fresh")
expect(found.pointer.sessionId).to_equal("cse_fresh")
expect(found.ageMs).to_equal(100)
val tooMany = store.readAcrossWorktrees("/missing", manyWorktrees(51), 2000)
expect(tooMany.found).to_equal(false)
expect(tooMany.skippedFanout).to_equal(true)
expect(maxWorktreeFanout()).to_equal(50)
```

</details>

#### validates source values and age calculation

- Expose small pure helpers used by read validation
   - Expected: bridgePointerSourceValid("standalone") is true
   - Expected: bridgePointerSourceValid("repl") is true
   - Expected: bridgePointerSourceValid("other") is false
   - Expected: nonNegativeAge(100, 200) equals `0`
   - Expected: nonNegativeAge(300, 200) equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expose small pure helpers used by read validation")
expect(bridgePointerSourceValid("standalone")).to_equal(true)
expect(bridgePointerSourceValid("repl")).to_equal(true)
expect(bridgePointerSourceValid("other")).to_equal(false)
expect(nonNegativeAge(100, 200)).to_equal(0)
expect(nonNegativeAge(300, 200)).to_equal(100)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
