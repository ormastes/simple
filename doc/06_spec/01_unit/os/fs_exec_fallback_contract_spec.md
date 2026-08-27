# fs_exec_fallback_contract_spec

> FS-Exec Fallback Contract — per-arch rejection specs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fs_exec_fallback_contract_spec

FS-Exec Fallback Contract — per-arch rejection specs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FS-EXEC-MULTIARCH-AC2 |
| Category | OS serial acceptance |
| Status | Active |
| Source | `test/01_unit/os/fs_exec_fallback_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

FS-Exec Fallback Contract — per-arch rejection specs.
Verifies that the shared fs_exec_fallback_contract correctly detects
resident-manifest fallback patterns, and that all five architecture lanes
(x86_64, riscv64, riscv32, arm64, arm32) would reject serial output
containing those patterns as completion evidence.

No QEMU needed — pure contract functions on text input.

## Scenarios

### fs_exec_fallback_contract — detection

#### clean serial has no fallback

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- clean serial has no fallback
   - Expected: fs_exec_serial_has_fallback(_clean_serial()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clean serial has no fallback")
expect(fs_exec_serial_has_fallback(_clean_serial())).to_equal(false)
```

</details>

#### clean serial passes rejects_fallback

- clean serial passes rejects_fallback
   - Expected: fs_exec_serial_rejects_fallback(_clean_serial()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clean serial passes rejects_fallback")
expect(fs_exec_serial_rejects_fallback(_clean_serial())).to_equal(true)
```

</details>

#### detects resident-fallback:active pattern alone

- detects resident-fallback:active pattern alone
   - Expected: fs_exec_serial_has_fallback(_fallback_serial_resident_active_only()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects resident-fallback:active pattern alone")
expect(fs_exec_serial_has_fallback(_fallback_serial_resident_active_only())).to_equal(true)
```

</details>

#### detects launcher fallback=resident-manifest pattern alone

- detects launcher fallback=resident-manifest pattern alone
   - Expected: fs_exec_serial_has_fallback(_fallback_serial_launcher_only()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects launcher fallback=resident-manifest pattern alone")
expect(fs_exec_serial_has_fallback(_fallback_serial_launcher_only())).to_equal(true)
```

</details>

#### detects both patterns together

- detects both patterns together
   - Expected: fs_exec_serial_has_fallback(_fallback_serial_both_patterns()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects both patterns together")
expect(fs_exec_serial_has_fallback(_fallback_serial_both_patterns())).to_equal(true)
```

</details>

#### rejects_fallback is false when fallback detected (both patterns)

- rejects_fallback is false when fallback detected (both patterns)
   - Expected: fs_exec_serial_rejects_fallback(_fallback_serial_both_patterns()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects_fallback is false when fallback detected (both patterns)")
expect(fs_exec_serial_rejects_fallback(_fallback_serial_both_patterns())).to_equal(false)
```

</details>

#### rejects_fallback is false for resident-active-only serial

- rejects_fallback is false for resident-active-only serial
   - Expected: fs_exec_serial_rejects_fallback(_fallback_serial_resident_active_only()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects_fallback is false for resident-active-only serial")
expect(fs_exec_serial_rejects_fallback(_fallback_serial_resident_active_only())).to_equal(false)
```

</details>

#### rejects_fallback is false for launcher-only serial

- rejects_fallback is false for launcher-only serial
   - Expected: fs_exec_serial_rejects_fallback(_fallback_serial_launcher_only()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects_fallback is false for launcher-only serial")
expect(fs_exec_serial_rejects_fallback(_fallback_serial_launcher_only())).to_equal(false)
```

</details>

#### pattern constants match expected strings

- pattern constants match expected strings
   - Expected: FS_EXEC_FALLBACK_PATTERN_RESIDENT_ACTIVE equals `[desktop-e2e] resident-fallback:active`
   - Expected: FS_EXEC_FALLBACK_PATTERN_LAUNCHER equals `[launcher] fallback=resident-manifest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pattern constants match expected strings")
expect(FS_EXEC_FALLBACK_PATTERN_RESIDENT_ACTIVE).to_equal("[desktop-e2e] resident-fallback:active")
expect(FS_EXEC_FALLBACK_PATTERN_LAUNCHER).to_equal("[launcher] fallback=resident-manifest")
```

</details>

### fs_exec fallback rejection — x86_64 lane

#### x86_64: resident-fallback:active pattern is rejected

- x86_64: resident-fallback:active pattern is rejected
   - Expected: fs_exec_serial_rejects_fallback(serial) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86_64: resident-fallback:active pattern is rejected")
val serial = _fallback_serial_resident_active_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### x86_64: launcher fallback=resident-manifest pattern is rejected

- x86_64: launcher fallback=resident-manifest pattern is rejected
   - Expected: fs_exec_serial_rejects_fallback(serial) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86_64: launcher fallback=resident-manifest pattern is rejected")
val serial = _fallback_serial_launcher_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### x86_64: clean serial is accepted (not a fallback)

- x86_64: clean serial is accepted (not a fallback)
   - Expected: fs_exec_serial_rejects_fallback(serial) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86_64: clean serial is accepted (not a fallback)")
val serial = _clean_serial()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(true)
```

</details>

### fs_exec fallback rejection — riscv64 lane

#### riscv64: resident-fallback:active pattern is rejected

- riscv64: resident-fallback:active pattern is rejected
   - Expected: fs_exec_serial_rejects_fallback(serial) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv64: resident-fallback:active pattern is rejected")
val serial = _fallback_serial_resident_active_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### riscv64: launcher fallback=resident-manifest pattern is rejected

- riscv64: launcher fallback=resident-manifest pattern is rejected
   - Expected: fs_exec_serial_rejects_fallback(serial) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv64: launcher fallback=resident-manifest pattern is rejected")
val serial = _fallback_serial_launcher_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### riscv64: clean serial is accepted

- riscv64: clean serial is accepted
   - Expected: fs_exec_serial_rejects_fallback(serial) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv64: clean serial is accepted")
val serial = _clean_serial()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(true)
```

</details>

### fs_exec fallback rejection — riscv32 lane

#### riscv32: resident-fallback:active pattern is rejected

- riscv32: resident-fallback:active pattern is rejected
   - Expected: fs_exec_serial_rejects_fallback(serial) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv32: resident-fallback:active pattern is rejected")
val serial = _fallback_serial_resident_active_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### riscv32: launcher fallback=resident-manifest pattern is rejected

- riscv32: launcher fallback=resident-manifest pattern is rejected
   - Expected: fs_exec_serial_rejects_fallback(serial) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv32: launcher fallback=resident-manifest pattern is rejected")
val serial = _fallback_serial_launcher_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### riscv32: clean serial is accepted

- riscv32: clean serial is accepted
   - Expected: fs_exec_serial_rejects_fallback(serial) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv32: clean serial is accepted")
val serial = _clean_serial()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(true)
```

</details>

### fs_exec fallback rejection — arm64 lane

#### arm64: resident-fallback:active pattern is rejected

- arm64: resident-fallback:active pattern is rejected
   - Expected: fs_exec_serial_rejects_fallback(serial) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm64: resident-fallback:active pattern is rejected")
val serial = _fallback_serial_resident_active_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### arm64: launcher fallback=resident-manifest pattern is rejected

- arm64: launcher fallback=resident-manifest pattern is rejected
   - Expected: fs_exec_serial_rejects_fallback(serial) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm64: launcher fallback=resident-manifest pattern is rejected")
val serial = _fallback_serial_launcher_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### arm64: clean serial is accepted

- arm64: clean serial is accepted
   - Expected: fs_exec_serial_rejects_fallback(serial) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm64: clean serial is accepted")
val serial = _clean_serial()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(true)
```

</details>

### fs_exec fallback rejection — arm32 lane

#### arm32: resident-fallback:active pattern is rejected

- arm32: resident-fallback:active pattern is rejected
   - Expected: fs_exec_serial_rejects_fallback(serial) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm32: resident-fallback:active pattern is rejected")
val serial = _fallback_serial_resident_active_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### arm32: launcher fallback=resident-manifest pattern is rejected

- arm32: launcher fallback=resident-manifest pattern is rejected
   - Expected: fs_exec_serial_rejects_fallback(serial) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm32: launcher fallback=resident-manifest pattern is rejected")
val serial = _fallback_serial_launcher_only()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(false)
```

</details>

#### arm32: clean serial is accepted

- arm32: clean serial is accepted
   - Expected: fs_exec_serial_rejects_fallback(serial) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm32: clean serial is accepted")
val serial = _clean_serial()
expect(fs_exec_serial_rejects_fallback(serial)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `b93ce93958d42234aea4d8d160e0d1e8ef36afccbfe089bc8fbe2b3b0467df0b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b93ce93958d42234aea4d8d160e0d1e8ef36afccbfe089bc8fbe2b3b0467df0b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b93ce93958d42234aea4d8d160e0d1e8ef36afccbfe089bc8fbe2b3b0467df0b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/fs_exec_fallback_contract_spec.spl
mirror: doc/06_spec/01_unit/os/fs_exec_fallback_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/fs_exec_fallback_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/fs_exec_fallback_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/fs_exec_fallback_contract_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clean serial has no fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/fs_exec_fallback_contract_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clean serial passes rejects_fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/fs_exec_fallback_contract_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects resident-fallback:active pattern alone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
