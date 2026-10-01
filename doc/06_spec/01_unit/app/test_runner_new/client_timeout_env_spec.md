# @req REQ-TESTRUNNER-TIMEOUT-BUDGET

> Test-runner client timeout budget — where it comes from, and in what order.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @req REQ-TESTRUNNER-TIMEOUT-BUDGET

Test-runner client timeout budget — where it comes from, and in what order.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/client_timeout_env_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Test-runner client timeout budget — where it comes from, and in what order.

Audience: anyone who exports SIMPLE_TIMEOUT_SECONDS before a `bin/simple test`
run and expects the budget to change, and anyone editing
`src/app/test_runner_new/timeout_budget.spl`.

Why this spec exists: SIMPLE_TIMEOUT_SECONDS was read by NOTHING on the client
path. `parse_client_run` hardcoded 120, and `run.timeout_secs` is what feeds
both the light-daemon request budget and the direct-child `--timeout` argument —
so every session exporting the variable silently got 120s, and healthy specs
that needed longer were recorded as `failed=1 reason=daemon-no-response
budget_ms=120000`. That is a false RED, the worst kind of wrong verdict: it
looks like a defect in the code under test.
Bug: doc/08_tracking/bug/simple_timeout_seconds_ignored_by_light_daemon_budget_2026-08-17.md

The similar-problem generalisation is the PRECEDENCE LADDER, not the single env
read: a budget has three possible sources (explicit flag, environment, built-in
default) and the class of defect is any source being silently dropped, or a less
specific source silently winning. Each rung the library owns is pinned below,
including the malformed-value rung — a budget that parses junk as 0 expires
instantly and reports every spec as a timeout, which is strictly worse than
ignoring the variable. The remaining rung (an explicit `--timeout` beating the
environment) lives in `parse_client_run`, which cannot be imported here: that
file is a standalone script with a bare `fn main` and importing it trips the
documented fn-main collision that flips green specs to FAIL. It is covered by
the command-line evidence recorded in the bug doc instead.

## Scenarios

### Where the test-runner client gets its default timeout budget

#### falls back to the built-in default when the environment says nothing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- falls back to the built-in default when the environment says nothing
- Clear SIMPLE_TIMEOUT_SECONDS and ask for the default budget
   - Expected: CLIENT_DEFAULT_TIMEOUT_SECS equals `900`
   - Expected: client_default_timeout_secs() equals `900`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("falls back to the built-in default when the environment says nothing")
"""With no override exported, the client uses its documented
900-second default (raised from 120, which was below the floor
cost of running any spec at all)."""

step("Clear SIMPLE_TIMEOUT_SECONDS and ask for the default budget")
env_set("SIMPLE_TIMEOUT_SECONDS", "")
expect(CLIENT_DEFAULT_TIMEOUT_SECS).to_equal(900)
expect(client_default_timeout_secs()).to_equal(900)
```

</details>

#### honours SIMPLE_TIMEOUT_SECONDS when it is set

- honours SIMPLE_TIMEOUT_SECONDS when it is set
- Export a budget far above the default and read it back
   - Expected: client_default_timeout_secs() equals `800`
- Confirm a different value is not cached from the previous read
   - Expected: client_default_timeout_secs() equals `1800`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("honours SIMPLE_TIMEOUT_SECONDS when it is set")
"""This is the reproducing case. Before the fix this returned 120 — the
exported value was read by nothing on this path — and any spec needing
more than two minutes was reported as a daemon timeout rather than run
to a verdict."""

step("Export a budget far above the default and read it back")
env_set("SIMPLE_TIMEOUT_SECONDS", "800")
expect(client_default_timeout_secs()).to_equal(800)

step("Confirm a different value is not cached from the previous read")
env_set("SIMPLE_TIMEOUT_SECONDS", "1800")
expect(client_default_timeout_secs()).to_equal(1800)
```

</details>

#### ignores a malformed value instead of expiring instantly

- ignores a malformed value instead of expiring instantly
- Try each shape of unusable value in turn
   - Expected: client_default_timeout_secs() equals `900`
   - Expected: client_default_timeout_secs() equals `900`
   - Expected: client_default_timeout_secs() equals `900`
- Leave the environment clean for any later example


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("ignores a malformed value instead of expiring instantly")
"""A budget parsed as 0 is worse than an ignored one: every spec would
time out immediately and the whole suite would read RED for a reason
having nothing to do with the code under test."""

step("Try each shape of unusable value in turn")
env_set("SIMPLE_TIMEOUT_SECONDS", "abc")
expect(client_default_timeout_secs()).to_equal(900)

env_set("SIMPLE_TIMEOUT_SECONDS", "800s")
expect(client_default_timeout_secs()).to_equal(900)

env_set("SIMPLE_TIMEOUT_SECONDS", "-5")
expect(client_default_timeout_secs()).to_equal(900)

step("Leave the environment clean for any later example")
env_set("SIMPLE_TIMEOUT_SECONDS", "")
```

</details>

### The environment-value parser, in isolation

#### accepts a run of decimal digits and rejects everything else

- accepts a run of decimal digits and rejects everything else
- Accept well-formed positive budgets
   - Expected: parse_env_timeout_secs("800") equals `800`
   - Expected: parse_env_timeout_secs("1") equals `1`
   - Expected: parse_env_timeout_secs("1800") equals `1800`
- Reject empty, non-numeric, suffixed, signed, and spaced values
   - Expected: parse_env_timeout_secs("") equals `0`
   - Expected: parse_env_timeout_secs("abc") equals `0`
   - Expected: parse_env_timeout_secs("800s") equals `0`
   - Expected: parse_env_timeout_secs("-5") equals `0`
   - Expected: parse_env_timeout_secs(" 800") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts a run of decimal digits and rejects everything else")
"""Pinned separately from the ladder above so a parser regression names
itself rather than surfacing as a mysterious 120 somewhere else."""

step("Accept well-formed positive budgets")
expect(parse_env_timeout_secs("800")).to_equal(800)
expect(parse_env_timeout_secs("1")).to_equal(1)
expect(parse_env_timeout_secs("1800")).to_equal(1800)

step("Reject empty, non-numeric, suffixed, signed, and spaced values")
expect(parse_env_timeout_secs("")).to_equal(0)
expect(parse_env_timeout_secs("abc")).to_equal(0)
expect(parse_env_timeout_secs("800s")).to_equal(0)
expect(parse_env_timeout_secs("-5")).to_equal(0)
expect(parse_env_timeout_secs(" 800")).to_equal(0)
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

- `REQ-SSPEC-APP`
- `REQ-TESTRUNNER-TIMEOUT-BUDGET`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b851894997d897a106dbccd5ab3c1d86f3a7c9a5cea2934456c06cac259eea8f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b851894997d897a106dbccd5ab3c1d86f3a7c9a5cea2934456c06cac259eea8f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b851894997d897a106dbccd5ab3c1d86f3a7c9a5cea2934456c06cac259eea8f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/test_runner_new/client_timeout_env_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner_new/client_timeout_env_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/test_runner_new/client_timeout_env_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner_new/client_timeout_env_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner_new/client_timeout_env_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/test_runner_new/client_timeout_env_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to the built-in default when the environment says nothing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_new/client_timeout_env_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'honours SIMPLE_TIMEOUT_SECONDS when it is set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_new/client_timeout_env_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores a malformed value instead of expiring instantly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
