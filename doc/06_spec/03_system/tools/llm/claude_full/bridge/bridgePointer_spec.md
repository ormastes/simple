# Claude Full Bridge Pointer

> Mirrors crash-recovery bridge pointer path, validation, TTL, clearing, and worktree fanout behavior.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors crash-recovery bridge pointer path, validation, TTL, clearing, and worktree fanout behavior.

## Scenarios

### Claude full bridge pointer

#### builds sanitized per-directory pointer paths

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds sanitized per-directory pointer paths
- Derive the projects-dir path used for crash recovery
   - Expected: bridgePointerFileName() equals `bridge-pointer.json`
   - Expected: getBridgePointerPath("/projects/", "/repo/main") equals `/projects/-repo-main/bridge-pointer.json`
   - Expected: sanitizeBridgePointerPath("C:\\repo work") equals `C-repo-work`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds sanitized per-directory pointer paths")
step("Derive the projects-dir path used for crash recovery")
expect(bridgePointerFileName()).to_equal("bridge-pointer.json")
expect(getBridgePointerPath("/projects/", "/repo/main")).to_equal("/projects/-repo-main/bridge-pointer.json")
expect(sanitizeBridgePointerPath("C:\\repo work")).to_equal("C-repo-work")
```

</details>

#### writes and reads a fresh pointer with age

- writes and reads a fresh pointer with age
- Persist a standalone pointer and read it before TTL expiry
   - Expected: read.found is true
   - Expected: read.pointer.sessionId equals `cse_1`
   - Expected: read.pointer.environmentId equals `env_1`
   - Expected: read.pointer.sourceStandalone() is true
   - Expected: read.ageMs equals `500`
   - Expected: store.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes and reads a fresh pointer with age")
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

- clears corrupt, invalid, and stale pointers
- Reject pointers that would keep re-prompting after backend GC
   - Expected: corrupt.found is false
   - Expected: corrupt.cleared is true
   - Expected: corrupt.reason equals `invalid-json`
   - Expected: invalid.cleared is true
   - Expected: invalid.reason equals `invalid-schema`
   - Expected: stale.cleared is true
   - Expected: stale.reason equals `stale`
   - Expected: store.count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clears corrupt, invalid, and stale pointers")
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

- uses current directory fast path before worktree fanout
- Return the current directory pointer without scanning siblings
   - Expected: result.found is true
   - Expected: result.dir equals `/repo`
   - Expected: result.pointer.sessionId equals `cse_here`
   - Expected: result.ageMs equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses current directory fast path before worktree fanout")
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

- selects the freshest pointer across worktrees and caps fanout
- Fan out only when current directory misses
   - Expected: found.found is true
   - Expected: found.dir equals `/fresh`
   - Expected: found.pointer.sessionId equals `cse_fresh`
   - Expected: found.ageMs equals `100`
   - Expected: tooMany.found is false
   - Expected: tooMany.skippedFanout is true
   - Expected: maxWorktreeFanout() equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects the freshest pointer across worktrees and caps fanout")
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

- validates source values and age calculation
- Expose small pure helpers used by read validation
   - Expected: bridgePointerSourceValid("standalone") is true
   - Expected: bridgePointerSourceValid("repl") is true
   - Expected: bridgePointerSourceValid("other") is false
   - Expected: nonNegativeAge(100, 200) equals `0`
   - Expected: nonNegativeAge(300, 200) equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates source values and age calculation")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1c92ca9023a8abee440591745d967b77e2a92353b4f416f3dc41cfac28f1027c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c92ca9023a8abee440591745d967b77e2a92353b4f416f3dc41cfac28f1027c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c92ca9023a8abee440591745d967b77e2a92353b4f416f3dc41cfac28f1027c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/bridge/bridgePointer_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/bridge/bridgePointer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/bridge/bridgePointer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/bridge/bridgePointer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/bridge/bridgePointer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/bridge/bridgePointer_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds sanitized per-directory pointer paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/bridgePointer_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes and reads a fresh pointer with age' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/bridgePointer_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears corrupt, invalid, and stale pointers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
