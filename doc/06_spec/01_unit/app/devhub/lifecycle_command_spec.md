# lifecycle_command_spec

> DevHub lifecycle inspection is versioned, idempotency-aware, and read-only.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lifecycle_command_spec

DevHub lifecycle inspection is versioned, idempotency-aware, and read-only.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/lifecycle_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

DevHub lifecycle inspection is versioned, idempotency-aware, and read-only.

## Scenarios

### DevHub typed lifecycle inspection

#### advertises the versioned observe-only capability surface

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- advertises the versioned observe-only capability surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("advertises the versioned observe-only capability surface")
val payload = lifecycle_capabilities_json()
expect(payload).to_contain('"output_version":"devhub/v1"')
expect(payload).to_contain('"mutation":"disabled-by-default"')
```

</details>

#### retains idempotency identity and explains local inspection

- retains idempotency identity and explains local inspection
- Inspect one stable local change identity
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("retains idempotency identity and explains local inspection")
step("Inspect one stable local change identity")
val (payload, code) = lifecycle_inspect_json("change", "chg_1", "idem-1", true)
expect(code).to_equal(0)
expect(payload).to_contain('"idempotency_key":"idem-1"')
expect(payload).to_contain('"mutation":"none"')
expect(payload).to_contain('"explain":')
```

</details>

#### rejects unsupported provider-neutral domains explicitly

- rejects unsupported provider-neutral domains explicitly
   - Expected: code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects unsupported provider-neutral domains explicitly")
val (payload, code) = lifecycle_inspect_json("pull-request", "42", "idem-2", true)
expect(code).to_equal(2)
expect(payload).to_contain("DOMAIN_UNSUPPORTED")
```

</details>

#### reads the actual Simple version declaration rather than a comment substring

- reads the actual Simple version declaration rather than a comment substring
   - Expected: lifecycle_projection_version(path) equals `0.9.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reads the actual Simple version declaration rather than a comment substring")
val path = "build/test-artifacts/devhub-version-comment-trap.spl"
expect(dir_create_all("build/test-artifacts")).to_be(true)
expect(file_write(path, "# version 1.0.0-RC\nfn get_version() -> text:\n    \"0.9.0\"\n")).to_be(true)
expect(lifecycle_projection_version(path)).to_equal("0.9.0")
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

- `REQ-SSPEC-UNIT`
- `REQ-004`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4fbb7d1f75f450d128dc7421e92ffdac7d0e213e2d800f352e99728ab9f974c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4fbb7d1f75f450d128dc7421e92ffdac7d0e213e2d800f352e99728ab9f974c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4fbb7d1f75f450d128dc7421e92ffdac7d0e213e2d800f352e99728ab9f974c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/devhub/lifecycle_command_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/lifecycle_command_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/app/devhub/lifecycle_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/lifecycle_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/lifecycle_command_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/devhub/lifecycle_command_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/devhub/lifecycle_command_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'advertises the versioned observe-only capability surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/lifecycle_command_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains idempotency identity and explains local inspection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/lifecycle_command_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unsupported provider-neutral domains explicitly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
