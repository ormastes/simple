# CLI Wrapper Error Detail Regression Spec

> Regression guard for the release-binary error wrapper. The release binary

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Wrapper Error Detail Regression Spec

Regression guard for the release-binary error wrapper. The release binary

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling / Error Reporting |
| Status | Active |
| Source | `test/unit/app/cli_wrapper_error_detail_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Bug ID:** B1 (compiler_bugs_for_crypto_2026-04-25.md)
**Memory:** feedback_simple_run_wrapper_broken.md
Regression guard for the release-binary error wrapper. The release binary
captures the bootstrap subprocess's stderr and re-emits it; the wrapper
must route through real stderr (not stdout with a "[STDERR]" prefix).

Acceptance per plan:
- stderr length > 50 bytes on a parse error
- stdout length == 0 on a parse error
- "[STDERR]" literal must NOT appear in stdout (across all error modes)

## Scenarios

### CLI wrapper error detail (B1)

#### parse error: stderr > 50 bytes, stdout == 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parse error: stderr > 50 bytes, stdout == 0
   - Expected: stdout.len() equals `0`
   - Expected: stderr.len() > 50 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse error: stderr > 50 bytes, stdout == 0")
val script = _write_temp("parse", "fn main():\n    val x = {\n")
val (stdout, stderr, code) = _run_simple(script)
val _ = rt_file_delete(script)
expect(code).to_not_equal(0)
expect(stdout.len()).to_equal(0)
expect(stderr.len() > 50).to_equal(true)
```

</details>

#### parse error: '[STDERR]' literal must NOT appear in stdout

- parse error: '[STDERR]' literal must NOT appear in stdout
   - Expected: stdout does not contain `[STDERR]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse error: '[STDERR]' literal must NOT appear in stdout")
val script = _write_temp("parse_no_prefix", "fn main():\n    val x = {\n")
val (stdout, _, _) = _run_simple(script)
val _ = rt_file_delete(script)
expect(stdout.contains("[STDERR]")).to_equal(false)
```

</details>

#### runtime error: real message reaches stderr

- runtime error: real message reaches stderr
   - Expected: stdout does not contain `[STDERR]`
   - Expected: stderr.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runtime error: real message reaches stderr")
val script = _write_temp("runtime", "fn main():\n    val x = 10\n    val y = 0\n    print x / y\n")
val (stdout, stderr, code) = _run_simple(script)
val _ = rt_file_delete(script)
expect(code).to_not_equal(0)
expect(stdout.contains("[STDERR]")).to_equal(false)
expect(stderr.len() > 0).to_equal(true)
```

</details>

#### semantic error: stderr carries the message; stdout has no '[STDERR]'

- semantic error: stderr carries the message; stdout has no '[STDERR]'
   - Expected: stdout does not contain `[STDERR]`
   - Expected: stderr.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("semantic error: stderr carries the message; stdout has no '[STDERR]'")
# Avoid f-string interpolation by using an unresolved function call
# rather than a `use foo.{bar}` import (the spec body is itself an
# interpolating string literal).
val script = _write_temp("semres", "fn main():\n    nonexistent_function_xyz()\n")
val (stdout, stderr, code) = _run_simple(script)
val _ = rt_file_delete(script)
expect(code).to_not_equal(0)
expect(stdout.contains("[STDERR]")).to_equal(false)
expect(stderr.len() > 0).to_equal(true)
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b8c961bfa396c54ca311fe9c7e802b986c7864ef30856cbab51a924d829eef57`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8c961bfa396c54ca311fe9c7e802b986c7864ef30856cbab51a924d829eef57`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8c961bfa396c54ca311fe9c7e802b986c7864ef30856cbab51a924d829eef57`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/cli_wrapper_error_detail_spec.spl
mirror: doc/06_spec/unit/app/cli_wrapper_error_detail_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli_wrapper_error_detail_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli_wrapper_error_detail_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli_wrapper_error_detail_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/cli_wrapper_error_detail_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse error: stderr > 50 bytes, stdout == 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli_wrapper_error_detail_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse error: '[STDERR]' literal must NOT appear in stdout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli_wrapper_error_detail_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runtime error: real message reaches stderr' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
