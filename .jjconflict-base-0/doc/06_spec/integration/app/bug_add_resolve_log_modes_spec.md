# bug_add_resolve_log_modes_spec

> Purpose: This spec proves bug add and resolve log mode CLI options.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bug_add_resolve_log_modes_spec

Purpose: This spec proves bug add and resolve log mode CLI options.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/bug_add_resolve_log_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves bug add and resolve log mode CLI options.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### bug add and resolve log mode CLI options

#### bug-add shows shared log options in help

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- bug-add shows shared log options in help
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BUGADDRESOLVELOGMODES-001
step("bug-add shows shared log options in help")
_setup_fixture()
val (out, err, code) = _run_bug_add(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### bug-resolve shows shared log options in help

- bug-resolve shows shared log options in help
- bug-resolve shows shared log options in help
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bug-resolve shows shared log options in help")
step("bug-resolve shows shared log options in help")
_setup_fixture()
val (out, err, code) = _run_bug_resolve(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### bug-add supports log-mode json

- bug-add supports log-mode json
- bug-add supports log-mode json
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bug-add supports log-mode json")
step("bug-add supports log-mode json")
_setup_fixture()
val (out, err, code) = _run_bug_add(["--id=log_mode_bug_001", "--severity=p2", "--title=fixture", "--file=src/main.spl", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"bug-add\"")
expect(out).to_contain("\"id\":\"log_mode_bug_001\"")
```

</details>

#### bug-resolve supports log-mode json

- bug-resolve supports log-mode json
- bug-resolve supports log-mode json
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bug-resolve supports log-mode json")
step("bug-resolve supports log-mode json")
_setup_fixture()
val (_add_out, _add_err, _add_code) = _run_bug_add(["--id=log_mode_bug_002", "--severity=p2", "--title=fixture", "--file=src/main.spl"])
val (out, err, code) = _run_bug_resolve(["--id=log_mode_bug_002", "--date=2026-05-24", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"bug-resolve\"")
expect(out).to_contain("\"id\":\"log_mode_bug_002\"")
```

</details>

#### bug-add supports dot progress

- bug-add supports dot progress
- bug-add supports dot progress
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bug-add supports dot progress")
step("bug-add supports dot progress")
_setup_fixture()
val (out, err, code) = _run_bug_add(["--id=log_mode_bug_003", "--severity=p2", "--title=fixture", "--file=src/main.spl", "--progress=dot"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Added bug log_mode_bug_003")
```

</details>

#### bug-add rejects invalid log mode

- bug-add rejects invalid log mode
- bug-add rejects invalid log mode
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bug-add rejects invalid log mode")
step("bug-add rejects invalid log mode")
_setup_fixture()
val (out, err, code) = _run_bug_add(["--id=log_mode_bug_004", "--title=fixture", "--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### bug-resolve rejects invalid log mode

- bug-resolve rejects invalid log mode
- bug-resolve rejects invalid log mode
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bug-resolve rejects invalid log mode")
step("bug-resolve rejects invalid log mode")
_setup_fixture()
val (out, err, code) = _run_bug_resolve(["--id=log_mode_bug_004", "--log-mode=noisy"])
expect(code).to_equal(1)
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-BUGADDRESOLVELOGMODES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0a51392768a97cb219721e906aa94455c28ceecd9e05d9c3f8f597280e4b7547`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a51392768a97cb219721e906aa94455c28ceecd9e05d9c3f8f597280e4b7547`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a51392768a97cb219721e906aa94455c28ceecd9e05d9c3f8f597280e4b7547`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/bug_add_resolve_log_modes_spec.spl
mirror: doc/06_spec/integration/app/bug_add_resolve_log_modes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/bug_add_resolve_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/bug_add_resolve_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/bug_add_resolve_log_modes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/bug_add_resolve_log_modes_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bug-add shows shared log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/bug_add_resolve_log_modes_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bug-resolve shows shared log options in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/bug_add_resolve_log_modes_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bug-add supports log-mode json' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
