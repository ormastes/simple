# Claude Full Session Env Vars

> Pure Simple coverage for session-scoped env var storage parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Session Env Vars

Pure Simple coverage for session-scoped env var storage parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/session_env_vars_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for session-scoped env var storage parity.

## Scenarios

### Claude full session env vars

#### starts empty

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts empty
- Check empty store
   - Expected: store.getSessionEnvVars().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("starts empty")
step("Check empty store")
val store = SessionEnvVars.new()
expect(store.getSessionEnvVars().len()).to_equal(0)
expect(store.getSessionEnvVar("A")).to_be_nil()
```

</details>

#### sets and replaces variables

- sets and replaces variables
- Check set and replace
   - Expected: store.getSessionEnvVars().len() equals `2`
   - Expected: store.getSessionEnvVar("A") equals `Some("3")`
   - Expected: store.getSessionEnvVar("B") equals `Some("2")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets and replaces variables")
step("Check set and replace")
var store = SessionEnvVars.new()
store.setSessionEnvVar("A", "1")
store.setSessionEnvVar("B", "2")
store.setSessionEnvVar("A", "3")
expect(store.getSessionEnvVars().len()).to_equal(2)
expect(store.getSessionEnvVar("A")).to_equal(Some("3"))
expect(store.getSessionEnvVar("B")).to_equal(Some("2"))
```

</details>

#### deletes variables

- deletes variables
- Check delete
   - Expected: store.getSessionEnvVars().len() equals `1`
   - Expected: store.getSessionEnvVar("B") equals `Some("2")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deletes variables")
step("Check delete")
var store = SessionEnvVars.new()
store.setSessionEnvVar("A", "1")
store.setSessionEnvVar("B", "2")
store.deleteSessionEnvVar("A")
expect(store.getSessionEnvVars().len()).to_equal(1)
expect(store.getSessionEnvVar("A")).to_be_nil()
expect(store.getSessionEnvVar("B")).to_equal(Some("2"))
```

</details>

#### clears variables

- clears variables
- Check clear
   - Expected: store.getSessionEnvVars().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clears variables")
step("Check clear")
var store = SessionEnvVars.new()
store.setSessionEnvVar("A", "1")
store.setSessionEnvVar("B", "2")
store.clearSessionEnvVars()
expect(store.getSessionEnvVars().len()).to_equal(0)
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

- Canonical SPipe generation for source `ca94c4e0586e8413f99767e5c6d69c404dc6a9f77f95c030f9803ba6d66864b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca94c4e0586e8413f99767e5c6d69c404dc6a9f77f95c030f9803ba6d66864b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca94c4e0586e8413f99767e5c6d69c404dc6a9f77f95c030f9803ba6d66864b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/session_env_vars_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/session_env_vars_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/session_env_vars_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/session_env_vars_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/session_env_vars_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/session_env_vars_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/session_env_vars_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets and replaces variables' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/session_env_vars_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'deletes variables' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
