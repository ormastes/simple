# dbfs_capability_spec

> DBFS Capability Extension Probe Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_capability_spec

DBFS Capability Extension Probe Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/dbfs_capability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Capability Extension Probe Specification

Verifies DbFsDriver reports capabilities correctly:
  Positive: POSIX-shim, xattr, ACL, snapshot, COW, LargeFiles
  Negative: no dedup, no hard-links, no DirectIo

## Scenarios

### DBFS Capability — positive probes

#### PosixCompat capability is present

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- PosixCompat capability is present
   - Expected: d.probe(Capability.PosixCompat) == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PosixCompat capability is present")
val d = make_driver()
expect(d.probe(Capability.PosixCompat) == nil).to_equal(false)
```

</details>

#### Xattr capability is present

- Xattr capability is present
   - Expected: d.probe(Capability.Xattr) == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Xattr capability is present")
val d = make_driver()
expect(d.probe(Capability.Xattr) == nil).to_equal(false)
```

</details>

#### Acl capability is present

- Acl capability is present
   - Expected: d.probe(Capability.Acl) == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Acl capability is present")
val d = make_driver()
expect(d.probe(Capability.Acl) == nil).to_equal(false)
```

</details>

#### Snapshot capability is present

- Snapshot capability is present
   - Expected: d.probe(Capability.Snapshot) == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Snapshot capability is present")
val d = make_driver()
expect(d.probe(Capability.Snapshot) == nil).to_equal(false)
```

</details>

#### COW capability is present

- COW capability is present
   - Expected: d.probe(Capability.COW) == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("COW capability is present")
val d = make_driver()
expect(d.probe(Capability.COW) == nil).to_equal(false)
```

</details>

#### LargeFiles capability is present

- LargeFiles capability is present
   - Expected: d.probe(Capability.LargeFiles) == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("LargeFiles capability is present")
val d = make_driver()
expect(d.probe(Capability.LargeFiles) == nil).to_equal(false)
```

</details>

### DBFS Capability — negative probes (out-of-scope ops)

#### Dedup capability is absent

- Dedup capability is absent
   - Expected: d.probe(Capability.Dedup) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Dedup capability is absent")
val d = make_driver()
expect(d.probe(Capability.Dedup) == nil).to_equal(true)
```

</details>

#### Hardlinks capability is absent

- Hardlinks capability is absent
   - Expected: d.probe(Capability.Hardlinks) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Hardlinks capability is absent")
val d = make_driver()
expect(d.probe(Capability.Hardlinks) == nil).to_equal(true)
```

</details>

#### DirectIo capability is absent

- DirectIo capability is absent
   - Expected: d.probe(Capability.DirectIo) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("DirectIo capability is absent")
val d = make_driver()
expect(d.probe(Capability.DirectIo) == nil).to_equal(true)
```

</details>

### DBFS Capability — capabilities() set

#### capabilities() returns a FsCapabilitySet containing PosixCompat

- capabilities() returns a FsCapabilitySet containing PosixCompat
   - Expected: caps.has(Capability.PosixCompat) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("capabilities() returns a FsCapabilitySet containing PosixCompat")
val d = make_driver()
val caps = d.capabilities()
expect(caps.has(Capability.PosixCompat)).to_equal(true)
```

</details>

#### capabilities() does not contain Dedup

- capabilities() does not contain Dedup
   - Expected: caps.has(Capability.Dedup) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("capabilities() does not contain Dedup")
val d = make_driver()
val caps = d.capabilities()
expect(caps.has(Capability.Dedup)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `18941f7e53bd9cdb24e7d6c8a389a378137cf14f93c6bd3ee50687521d98476d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `18941f7e53bd9cdb24e7d6c8a389a378137cf14f93c6bd3ee50687521d98476d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `18941f7e53bd9cdb24e7d6c8a389a378137cf14f93c6bd3ee50687521d98476d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/storage/dbfs/dbfs_capability_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/dbfs_capability_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/dbfs_capability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/dbfs_capability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/dbfs_capability_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PosixCompat capability is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_capability_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Xattr capability is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_capability_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Acl capability is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
