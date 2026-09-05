# Counterpart Conformance — SHA-256 vs OpenSSL vs NIST Vectors

> Proves Simple's own SHA-256 implementation (`src/lib/common/crypto/sha256.spl`)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Counterpart Conformance — SHA-256 vs OpenSSL vs NIST Vectors

Proves Simple's own SHA-256 implementation (`src/lib/common/crypto/sha256.spl`)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | In Progress |
| Plan | doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md (Wave 2 P4, Wave 5 K1/K2) |
| Source | `test/01_unit/infra/counterpart/cipher_counterpart_compare_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Proves Simple's own SHA-256 implementation (`src/lib/common/crypto/sha256.spl`)
against a genuinely-executed real OpenSSL CLI process and hardcoded published
FIPS 180-4 / NIST known-answer vectors, through the shared counterpart matrix
engine. The audience is an engineer deciding whether Simple's digest can be
trusted without re-deriving SHA-256 by hand.

## Scope and Preconditions

Three sources over one boundary (`cipher.digest.sha256@1`): Simple's native
implementation, the real `/usr/bin/openssl` CLI invoked as a process bridge,
and a hardcoded normative vector. All three comparisons use `byte_exact` —
never a tolerant relation for a cryptographic digest.

## Primary Workflow

Build the plan (`cipher_sha256_plan`), collect one `SourceResult` per source,
run `evaluate_matrix`, and assert `matrix_run_accepted`.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Oracle authority | A `normative_vector` source outranks agreement between two implementations — this is a ranking, not a majority vote |
| Process bridge | OpenSSL is invoked as a real subprocess via `process_run_bounded`, never faked |
| Vacuity | An openssl binary that cannot be found is `unavailable`, never a false pass or an ordinary crash |

## Related Specifications

- [Relation and matrix engine](relation_matrix_spec.spl)

## Evidence and Provenance

Executable against `src/lib/nogc_sync_mut/spec/evidence/counterpart/cipher_sha256_provider.spl`.

## Recovery and Troubleshooting

A rejection naming "normative" means the NIST vector disagreed with at least
one implementation — never relax this to a majority vote of the two
implementations.

## Compatibility and Limitations

Requires `/usr/bin/openssl` (OpenSSL 3.0.13 verified) on the host running the
spec. The unavailable-provider scenario below proves the framework reacts
correctly when that binary is absent, rather than skipping silently.

## Scenarios

### SHA-256 counterpart run: Simple vs OpenSSL vs NIST vectors

#### accepts a run where Simple, OpenSSL and the NIST vector all agree on the empty string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a run where Simple, OpenSSL and the NIST vector all agree on the empty string
- Build the plan and collect all three sources for the empty message
- Evaluate the matrix
- Confirm the run is accepted with zero rejections


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("accepts a run where Simple, OpenSSL and the NIST vector all agree on the empty string")
step("Build the plan and collect all three sources for the empty message")
val plan = cipher_sha256_plan("cipher-sha256-empty", "empty")
val results = [
    simple_sha256_source("simple", "", "empty"),
    openssl_sha256_source("openssl", OPENSSL_DEFAULT_PATH, "", "empty", 15000),
    nist_sha256_vector_source("nist", NIST_SHA256_EMPTY, "empty")
]
step("Evaluate the matrix")
val run = evaluate_matrix(plan, results)
step("Confirm the run is accepted with zero rejections")
assert_true(matrix_run_accepted(run))
assert_equal(run.rejections.len(), 0)
```

</details>

#### accepts a run where Simple, OpenSSL and the NIST vector all agree on 'abc'

- accepts a run where Simple, OpenSSL and the NIST vector all agree on 'abc'
- Build the plan and collect all three sources for 'abc'
- Evaluate the matrix
- Confirm the run is accepted, and OpenSSL genuinely executed (not unavailable)


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("accepts a run where Simple, OpenSSL and the NIST vector all agree on 'abc'")
step("Build the plan and collect all three sources for 'abc'")
val plan = cipher_sha256_plan("cipher-sha256-abc", "abc")
val results = [
    simple_sha256_source("simple", "abc", "abc"),
    openssl_sha256_source("openssl", OPENSSL_DEFAULT_PATH, "abc", "abc", 15000),
    nist_sha256_vector_source("nist", NIST_SHA256_ABC, "abc")
]
step("Evaluate the matrix")
val run = evaluate_matrix(plan, results)
step("Confirm the run is accepted, and OpenSSL genuinely executed (not unavailable)")
assert_true(matrix_run_accepted(run))
assert_equal(run.rejections.len(), 0)
```

</details>

#### reports Simple's real digest matches the real OpenSSL digest for 'abc'

- reports Simple's real digest matches the real OpenSSL digest for 'abc'
- Collect the OpenSSL and Simple sources independently
- Confirm OpenSSL genuinely executed and both hex digests are byte-identical


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports Simple's real digest matches the real OpenSSL digest for 'abc'")
step("Collect the OpenSSL and Simple sources independently")
val simple_result = simple_sha256_source("simple", "abc", "abc")
val openssl_result = openssl_sha256_source("openssl", OPENSSL_DEFAULT_PATH, "abc", "abc", 15000)
step("Confirm OpenSSL genuinely executed and both hex digests are byte-identical")
assert_true(openssl_result.diagnostics[0].contains(NIST_SHA256_ABC))
assert_equal(simple_result.artifact.canonical_hash, openssl_result.artifact.canonical_hash)
assert_equal(simple_result.artifact.canonical_hash, NIST_SHA256_ABC)
```

</details>

#### rejects the run when the OpenSSL binary is unavailable, never as a silent pass

- rejects the run when the OpenSSL binary is unavailable, never as a silent pass
- Point the process bridge at a path that does not exist
- Evaluate the matrix
- Confirm the run is rejected and the openssl source is reported unavailable, not skipped


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("rejects the run when the OpenSSL binary is unavailable, never as a silent pass")
step("Point the process bridge at a path that does not exist")
val plan = cipher_sha256_plan("cipher-sha256-unavailable", "abc")
val results = [
    simple_sha256_source("simple", "abc", "abc"),
    openssl_sha256_source("openssl", "/nonexistent/bin/openssl-does-not-exist", "abc", "abc", 15000),
    nist_sha256_vector_source("nist", NIST_SHA256_ABC, "abc")
]
step("Evaluate the matrix")
val run = evaluate_matrix(plan, results)
step("Confirm the run is rejected and the openssl source is reported unavailable, not skipped")
assert_false(matrix_run_accepted(run))
assert_equal(results[1].diagnostics[0].contains("not found"), true)
assert_true(matrix_run_has_rejection_containing(run, "openssl"))
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


## Related Documentation

- **Plan:** `doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md (Wave 2 P4, Wave 5 K1/K2)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COUNTERPART-K1-001`
- `REQ-COUNTERPART-K2-001`
- `REQ-SSPEC-INFRA`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a211e9b29d56f14b42d8433bf2572559cc8c9ff04e2a6073f6c403ee6e632b99`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a211e9b29d56f14b42d8433bf2572559cc8c9ff04e2a6073f6c403ee6e632b99`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a211e9b29d56f14b42d8433bf2572559cc8c9ff04e2a6073f6c403ee6e632b99`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/infra/counterpart/cipher_counterpart_compare_spec.spl
mirror: doc/06_spec/01_unit/infra/counterpart/cipher_counterpart_compare_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/infra/counterpart/cipher_counterpart_compare_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/infra/counterpart/cipher_counterpart_compare_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/infra/counterpart/cipher_counterpart_compare_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a run where Simple, OpenSSL and the NIST vector all agree on the empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/cipher_counterpart_compare_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a run where Simple, OpenSSL and the NIST vector all agree on 'abc'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/cipher_counterpart_compare_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports Simple's real digest matches the real OpenSSL digest for 'abc'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
