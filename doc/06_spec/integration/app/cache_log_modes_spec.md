# cache_log_modes_spec

> Purpose: This spec proves cache log mode CLI options.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cache_log_modes_spec

Purpose: This spec proves cache log mode CLI options.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/cache_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves cache log mode CLI options.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### cache log mode CLI options

#### shows shared log options in help

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shows shared log options in help
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CACHELOGMODES-001
step("shows shared log options in help")
_setup_fixture()
val (out, err, code) = _run_cache(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports info log-mode json

- supports info log-mode json
- supports info log-mode json
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports info log-mode json")
step("supports info log-mode json")
_setup_fixture()
val (out, err, code) = _run_cache(["info", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"info\"")
expect(out).to_contain("\"exists\":true")
expect(out).to_contain("\"count\":1")
```

</details>

#### supports list log-mode json

- supports list log-mode json
- supports list log-mode json
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports list log-mode json")
step("supports list log-mode json")
_setup_fixture()
val (out, err, code) = _run_cache(["list", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"list\"")
expect(out).to_contain("\"items\":[\"alpha.spk\"]")
```

</details>

#### supports dot progress

- supports dot progress
- supports dot progress
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports dot progress")
step("supports dot progress")
_setup_fixture()
val (out, err, code) = _run_cache(["info", "--progress=dot"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Cache directory:")
```

</details>

#### rejects invalid log mode

- rejects invalid log mode
- rejects invalid log mode
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects invalid log mode")
step("rejects invalid log mode")
_setup_fixture()
val (out, err, code) = _run_cache(["info", "--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-CACHELOGMODES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a2481f0d6f68255c5b5d2a5fb8198b7a340df9e78dd3dd6d5cb342c10d43f983`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a2481f0d6f68255c5b5d2a5fb8198b7a340df9e78dd3dd6d5cb342c10d43f983`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a2481f0d6f68255c5b5d2a5fb8198b7a340df9e78dd3dd6d5cb342c10d43f983`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/cache_log_modes_spec.spl
mirror: doc/06_spec/integration/app/cache_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/cache_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/cache_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/cache_log_modes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/cache_log_modes_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows shared log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/cache_log_modes_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports info log-mode json' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/cache_log_modes_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports list log-mode json' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
