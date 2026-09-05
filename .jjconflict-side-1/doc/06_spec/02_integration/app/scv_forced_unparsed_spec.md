# scv_forced_unparsed_spec

> Purpose: This spec proves SCV-IMPL-G-02 — the `forced_unparsed` escape hatch:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_forced_unparsed_spec

Purpose: This spec proves SCV-IMPL-G-02 — the `forced_unparsed` escape hatch:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_forced_unparsed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-G-02 — the `forced_unparsed` escape hatch:
`--force-unparsed` requires an explicit `--reason`, records an auditable
`forced_unparsed` state entry, commits in line mode, and is NEVER
`public_ready` by default — the audit blocks public publication.
Audience: Maintainers of the SCV commit gates.

## Scenarios

### scv forced_unparsed path + audit (G-02)

#### errors on a missing file even when forced

**Manual warnings:**
- invalid manual visibility metadata: # @manual SCV commit gates (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-FORCED-UNPARSED-001
# @req REQ-SSPEC-INTEGRATION
val root = _repo("missing")
val out = scv_commit_parse_policy_forced(root, "{root}/nope.py", "why")
expect(out.starts_with("ERROR")).to_be(true)
```

</details>

#### refuses --force-unparsed without a reason

- Attempt a forced unparsed commit with no --reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-FORCED-UNPARSED-001
step("Attempt a forced unparsed commit with no --reason")
val root = _repo("noreason")
file_write("{root}/tool.py", "print('hello')\n")
val out = scv_commit_parse_policy_forced(root, "{root}/tool.py", "")
expect(out.starts_with("ERROR")).to_be(true)
expect(out).to_contain("--reason")
```

</details>

#### refuses an unsafe reason (pipe or newline)

- Attempt a forced unparsed commit with a pipe in the reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-FORCED-UNPARSED-001
step("Attempt a forced unparsed commit with a pipe in the reason")
val root = _repo("badreason")
file_write("{root}/tool.py", "print('hello')\n")
val out = scv_commit_parse_policy_forced(root, "{root}/tool.py", "a|b")
expect(out.starts_with("ERROR")).to_be(true)
```

</details>

#### forces a supported source with no locked parser into forced_unparsed

- Without force, a supported language with no parser is an ERROR
- With force + reason it is recorded, not green-washed


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-FORCED-UNPARSED-001
step("Without force, a supported language with no parser is an ERROR")
val root = _repo("forced")
file_write("{root}/tool.py", "print('hello')\n")
val plain = scv_commit_parse_policy(root, "{root}/tool.py")
expect(plain.starts_with("ERROR")).to_be(true)
step("With force + reason it is recorded, not green-washed")
val out = scv_commit_parse_policy_forced(root, "{root}/tool.py", "vendored generated file")
expect(out).to_contain("policy: forced_unparsed")
expect(out).to_contain("state: forced_unparsed")
expect(out).to_contain("reason: vendored generated file")
expect(out).to_contain("mode: line")
expect(out).to_contain("public_ready: blocked")
```

</details>

#### records every forced commit in the audit log

- Force-commit two files and read back the audit log
- A recorded forced_unparsed entry blocks public_ready by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-FORCED-UNPARSED-001
step("Force-commit two files and read back the audit log")
val root = _repo("audit")
file_write("{root}/a.py", "a = 1\n")
file_write("{root}/b.py", "b = 2\n")
expect(scv_forced_unparsed_audit(root)).to_be("")
expect(scv_forced_unparsed_blocks_public(root)).to_be(false)
scv_commit_parse_policy_forced(root, "{root}/a.py", "reason-a")
scv_commit_parse_policy_forced(root, "{root}/b.py", "reason-b")
val audit = scv_forced_unparsed_audit(root)
expect(audit).to_contain("a.py")
expect(audit).to_contain("reason-a")
expect(audit).to_contain("b.py")
expect(audit).to_contain("reason-b")
step("A recorded forced_unparsed entry blocks public_ready by default")
expect(scv_forced_unparsed_blocks_public(root)).to_be(true)
```

</details>

#### leaves the unforced policy path unchanged

- Commit an ordinary text file without force and confirm no audit entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-FORCED-UNPARSED-001
step("Commit an ordinary text file without force and confirm no audit entry")
val root = _repo("plain")
file_write("{root}/notes.zzz", "plain notes\n")
val out = scv_commit_parse_policy(root, "{root}/notes.zzz")
expect(out).to_contain("policy: text_only")
expect(scv_forced_unparsed_blocks_public(root)).to_be(false)
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-FORCED-UNPARSED-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f3344806c7029321e254a8e3fcd624d24455190b38dc54e416a4f86999bfd763`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3344806c7029321e254a8e3fcd624d24455190b38dc54e416a4f86999bfd763`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3344806c7029321e254a8e3fcd624d24455190b38dc54e416a4f86999bfd763`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/02_integration/app/scv_forced_unparsed_spec.spl
mirror: doc/06_spec/02_integration/app/scv_forced_unparsed_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/scv_forced_unparsed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/scv_forced_unparsed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/scv_forced_unparsed_spec.spl:33:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'errors on a missing file even when forced' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_forced_unparsed_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses --force-unparsed without a reason' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_forced_unparsed_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses an unsafe reason (pipe or newline)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_forced_unparsed_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forces a supported source with no locked parser into forced_unparsed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
