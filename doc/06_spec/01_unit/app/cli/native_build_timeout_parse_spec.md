# native_build_timeout_parse_spec

> Purpose: Prove that native-build --timeout is accounted in the seconds the user asked for.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_build_timeout_parse_spec

Purpose: Prove that native-build --timeout is accounted in the seconds the user asked for.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/native_build_timeout_parse_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that native-build --timeout is accounted in the seconds the user asked for.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### native-build --timeout is accounted in the seconds the user asked for

#### parses a single digit as its VALUE, not its character code

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a single digit as its VALUE, not its character code
- Verify: parses a single digit as its VALUE, not its character code
   - Expected: native_build_parse_secs("7") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses a single digit as its VALUE, not its character code")
step("Verify: parses a single digit as its VALUE, not its character code")
# @req: REQ-APP-CLI-001
# Pre-fix this returned 55 (the ASCII code of "7").
expect(native_build_parse_secs("7")).to_equal(7)
```

</details>

#### parses a multi-digit budget without character-code contamination

- parses a multi-digit budget without character-code contamination
- Verify: parses a multi-digit budget without character-code contamination
   - Expected: native_build_parse_secs("600") equals `600`
   - Expected: native_build_parse_secs("7200") equals `7200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses a multi-digit budget without character-code contamination")
step("Verify: parses a multi-digit budget without character-code contamination")
# Pre-fix "600" accumulated to 5928.
expect(native_build_parse_secs("600")).to_equal(600)
expect(native_build_parse_secs("7200")).to_equal(7200)
```

</details>

#### still rejects a non-numeric budget

- still rejects a non-numeric budget
- Verify: still rejects a non-numeric budget
   - Expected: native_build_parse_secs("nope") equals `-1`
   - Expected: native_build_parse_secs("-1") equals `-1`
   - Expected: native_build_parse_secs("12x") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("still rejects a non-numeric budget")
step("Verify: still rejects a non-numeric budget")
expect(native_build_parse_secs("nope")).to_equal(-1)
expect(native_build_parse_secs("-1")).to_equal(-1)
expect(native_build_parse_secs("12x")).to_equal(-1)
```

</details>

#### converts the separated --timeout form to the right millisecond budget

- converts the separated --timeout form to the right millisecond budget
- Verify: converts the separated --timeout form to the right millisecond budget
   - Expected: native_build_timeout_ms(["--timeout", "7"]) equals `7000`
   - Expected: native_build_timeout_ms(["--timeout", "600"]) equals `600000`
   - Expected: native_build_timeout_ms(["--timeout", "7200"]) equals `7200000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("converts the separated --timeout form to the right millisecond budget")
step("Verify: converts the separated --timeout form to the right millisecond budget")
expect(native_build_timeout_ms(["--timeout", "7"])).to_equal(7000)
expect(native_build_timeout_ms(["--timeout", "600"])).to_equal(600000)
expect(native_build_timeout_ms(["--timeout", "7200"])).to_equal(7200000)
```

</details>

#### converts the inline --timeout= form to the right millisecond budget

- converts the inline --timeout= form to the right millisecond budget
- Verify: converts the inline --timeout= form to the right millisecond budget
   - Expected: native_build_timeout_ms(["--timeout=7"]) equals `7000`
   - Expected: native_build_timeout_ms(["--timeout=600"]) equals `600000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("converts the inline --timeout= form to the right millisecond budget")
step("Verify: converts the inline --timeout= form to the right millisecond budget")
expect(native_build_timeout_ms(["--timeout=7"])).to_equal(7000)
expect(native_build_timeout_ms(["--timeout=600"])).to_equal(600000)
```

</details>

#### keeps the budget correct when --timeout follows other flags

- keeps the budget correct when --timeout follows other flags
- Verify: keeps the budget correct when --timeout follows other flags
   - Expected: native_build_timeout_ms(["--entry", "a.spl", "-o", "out", "--timeout", "90"]) equals `90000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the budget correct when --timeout follows other flags")
step("Verify: keeps the budget correct when --timeout follows other flags")
expect(native_build_timeout_ms(["--entry", "a.spl", "-o", "out", "--timeout", "90"])).to_equal(90000)
```

</details>

#### accounts a bootstrap-sized budget exactly (run6 2026-08-21 regression)

- accounts a bootstrap-sized budget exactly (run6 2026-08-21 regression)
- Verify: accounts a bootstrap-sized budget exactly (run6 2026-08-21 regression)
   - Expected: native_build_parse_secs("36000") equals `36000`
   - Expected: native_build_timeout_ms(["--timeout", "36000"]) equals `36000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accounts a bootstrap-sized budget exactly (run6 2026-08-21 regression)")
step("Verify: accounts a bootstrap-sized budget exactly (run6 2026-08-21 regression)")
# doc/08_tracking/bug/native_build_timeout_not_forwarded_to_worker_2026-08-21.md
# Pre-fix `--timeout 36000` accumulated to 569328 (6.6 days), which is
# the number the driver then printed as "timed out after 569328s".
expect(native_build_parse_secs("36000")).to_equal(36000)
expect(native_build_timeout_ms(["--timeout", "36000"])).to_equal(36000000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-APP-CLI-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b44b59e54d66080e7144bfcd91ded78a1a091c00e8637c02ecdd6a0e05d20b42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b44b59e54d66080e7144bfcd91ded78a1a091c00e8637c02ecdd6a0e05d20b42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b44b59e54d66080e7144bfcd91ded78a1a091c00e8637c02ecdd6a0e05d20b42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/cli/native_build_timeout_parse_spec.spl
mirror: doc/06_spec/01_unit/app/cli/native_build_timeout_parse_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/native_build_timeout_parse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/native_build_timeout_parse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/native_build_timeout_parse_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/cli/native_build_timeout_parse_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a single digit as its VALUE, not its character code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/native_build_timeout_parse_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a multi-digit budget without character-code contamination' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/native_build_timeout_parse_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still rejects a non-numeric budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
