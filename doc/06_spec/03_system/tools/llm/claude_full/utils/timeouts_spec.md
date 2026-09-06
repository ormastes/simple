# Claude Full timeouts

> Pure Simple coverage for bash timeout env parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full timeouts

Pure Simple coverage for bash timeout env parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/timeouts_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for bash timeout env parsing.

## Scenarios

### Claude full timeouts

#### uses default timeout when env is empty or invalid

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses default timeout when env is empty or invalid
- Check default timeout fallback
   - Expected: getDefaultBashTimeoutMs(EnvLike.new("", "")) equals `120000`
   - Expected: getDefaultBashTimeoutMs(EnvLike.new("0", "")) equals `120000`
   - Expected: getDefaultBashTimeoutMs(EnvLike.new("-5", "")) equals `120000`
   - Expected: getDefaultBashTimeoutMs(EnvLike.new("x", "")) equals `120000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses default timeout when env is empty or invalid")
step("Check default timeout fallback")
expect(getDefaultBashTimeoutMs(EnvLike.new("", ""))).to_equal(120000)
expect(getDefaultBashTimeoutMs(EnvLike.new("0", ""))).to_equal(120000)
expect(getDefaultBashTimeoutMs(EnvLike.new("-5", ""))).to_equal(120000)
expect(getDefaultBashTimeoutMs(EnvLike.new("x", ""))).to_equal(120000)
```

</details>

#### uses positive default timeout env values

- uses positive default timeout env values
- Check default timeout override
   - Expected: getDefaultBashTimeoutMs(EnvLike.new("30000", "")) equals `30000`
   - Expected: getDefaultBashTimeoutMs(EnvLike.new("+42x", "")) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses positive default timeout env values")
step("Check default timeout override")
expect(getDefaultBashTimeoutMs(EnvLike.new("30000", ""))).to_equal(30000)
expect(getDefaultBashTimeoutMs(EnvLike.new("+42x", ""))).to_equal(42)
```

</details>

#### uses max timeout env when positive

- uses max timeout env when positive
- Check max timeout override
   - Expected: getMaxBashTimeoutMs(EnvLike.new("", "900000")) equals `900000`
   - Expected: getMaxBashTimeoutMs(EnvLike.new("", "x")) equals `maxBashTimeoutMs()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses max timeout env when positive")
step("Check max timeout override")
expect(getMaxBashTimeoutMs(EnvLike.new("", "900000"))).to_equal(900000)
expect(getMaxBashTimeoutMs(EnvLike.new("", "x"))).to_equal(maxBashTimeoutMs())
```

</details>

#### keeps max timeout at least as large as default

- keeps max timeout at least as large as default
- Check max/default ordering
   - Expected: getMaxBashTimeoutMs(EnvLike.new("500000", "1000")) equals `500000`
   - Expected: getMaxBashTimeoutMs(EnvLike.new("700000", "")) equals `700000`
   - Expected: defaultBashTimeoutMs() equals `120000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps max timeout at least as large as default")
step("Check max/default ordering")
expect(getMaxBashTimeoutMs(EnvLike.new("500000", "1000"))).to_equal(500000)
expect(getMaxBashTimeoutMs(EnvLike.new("700000", ""))).to_equal(700000)
expect(defaultBashTimeoutMs()).to_equal(120000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `8a876338bbc2f34b1cd0f6a83292a62d12ecc0a4c9a7900f80ab612a3a84af78`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8a876338bbc2f34b1cd0f6a83292a62d12ecc0a4c9a7900f80ab612a3a84af78`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8a876338bbc2f34b1cd0f6a83292a62d12ecc0a4c9a7900f80ab612a3a84af78`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/timeouts_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/timeouts_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/timeouts_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/timeouts_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/timeouts_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/timeouts_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses default timeout when env is empty or invalid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/timeouts_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses positive default timeout env values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/timeouts_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses max timeout env when positive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
