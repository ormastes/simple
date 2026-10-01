# SSpec Count Truthfulness — Authored System Manual Mirror

> **Evidence status: TEST_BLOCKED**
> This is a human-authored mirror of the intended executable SSpec flow, not
> generated documentation and not runtime-pass evidence. No admitted
> current-source pure-Simple CLI was available when this mirror was authored.
> The executable source belongs only under `test/03_system`; this directory
> contains Markdown documentation only.

## Purpose and audience

This manual describes how infrastructure maintainers and release reviewers
verify that `scripts/check/check-sspec-count-truthful.shs` cannot report a false
green when an SSpec runner executes fewer examples than the source declares.
It is also the review surface for the future executable system spec at
`test/03_system/infra/sspec_count_truthfulness_spec.spl`.

The lane protects three observable contracts:

- **REQ-SCT-001:** the selected runner's pure-Simple self-hosted identity is
  admitted before any count measurement.
- **REQ-SCT-002:** a nonzero SSpec runner result remains nonzero and can never
  be rewritten as a passing count claim.
- **REQ-SCT-003:** anchored, statically declared examples must equal the
  runner's reported `Results:` total exactly.

## Preconditions and qualification boundary

The executable verification requires all of the following:

1. A pure-Simple self-hosted CLI built from the source revision under test.
2. Successful admission by the repository's canonical self-hosted identity
   gate. The Rust bootstrap seed, a stale deployed binary, and an identity
   bypass are not acceptable evidence.
3. The tracked non-discovered fixture files under the system-spec lane.
4. The repository checkout containing the gate and its identity helper.
5. No dependency on network state, another scenario's fixtures, or a manually
   edited success transcript.

If qualification cannot be established, stop with **TEST_BLOCKED**. Do not run
the runtime scenarios through another compiler and do not infer a PASS from
static inspection.

## Visible operator workflow

The executable spec and future generated manual must expose these exact step
labels in this order within their applicable scenarios:

1. `Select the admitted pure-Simple SSpec runner`
2. `Run the count-truthfulness gate on a two-example passing spec`
3. `Confirm declared and reported counts agree`
4. `Run the count-truthfulness gate on the anchored-count edge fixture`
5. `Confirm non-example text does not inflate the declared count`
6. `Run the count-truthfulness gate on a deliberately failing spec`
7. `Confirm the runner failure remains nonzero`
8. `Run the count-truthfulness gate with a missing compiler path`
9. `Confirm unavailable identity is TEST_BLOCKED and never PASS`

Setup and cleanup may be folded in generated documentation, but these decision
steps must remain visible. The transcript must retain command status and the
relevant `OK`, `FAIL`, or qualification diagnostic; a summary without exit
status is insufficient evidence.

## Scenario narratives

### 1. Green path — exact two-example count

**Requirements:** REQ-SCT-001, REQ-SCT-002, REQ-SCT-003
**Intent:** demonstrate the only accepted success path.

The operator selects an admitted pure-Simple runner, creates an isolated SSpec
fixture containing exactly two executable `it` declarations, and invokes the
truthfulness gate. The scenario asserts all of the following with built-in
matchers:

- process exit status is exactly `0`;
- output contains `declared=2 reported=2`;
- output starts with or contains the gate's `OK` verdict; and
- output does not substitute a skip, blocker, or missing-results diagnostic.

The scenario passes only when the static count and runner summary agree.

### 2. Anchored edge — non-example lookalikes are ignored

**Requirements:** REQ-SCT-001, REQ-SCT-002, REQ-SCT-003
**Intent:** prove source counting is anchored to actual declaration position.

The fixture contains one real `it` example plus representative lookalikes
such as commented `it` text, a quoted string containing `it`, and an identifier
whose name contains those characters. The runner reports the one real
example. The scenario asserts exit status `0`, the exact
`declared=1 reported=1` evidence, and absence of `declared=2`. Any inflated
declared count is a failure because it would make the gate sensitive to
non-example text.

### 3. Red path — runner failure remains nonzero

**Requirements:** REQ-SCT-001, REQ-SCT-002, REQ-SCT-003
**Intent:** prevent a failing SSpec execution from being converted to success
by later count parsing.

The fixture contains a real failing assertion. The gate runs it with the
admitted runner. The scenario asserts that the gate status is exactly `1`,
the output contains a runner-exit failure diagnostic, and the output
does not contain an `OK` verdict for that fixture. This scenario is not
satisfied by a count mismatch alone: the original runner failure must remain
observable as a nonzero gate result.

### 4. Qualification error — missing compiler path never passes

**Requirements:** REQ-SCT-001, REQ-SCT-002
**Intent:** prove fail-closed behavior before test execution.

The gate is invoked with `SIMPLE_BIN` set to an explicit nonexistent path. The
scenario asserts exit status `2`, diagnostics containing `SKIPPED (cannot
test)` and `This is NOT a pass`, and absence of an `OK` verdict.
For operator reporting, this condition is **TEST_BLOCKED**, never PASS and
never evidence that the runtime behaviors above were exercised.

## Requirement traceability

| Requirement | Green | Anchored edge | Red exit | Missing binary | Required evidence |
|---|:---:|:---:|:---:|:---:|---|
| REQ-SCT-001 | Yes | Yes | Yes | Yes | Identity admission precedes every measured result; unavailable identity exits `2` and never emits `OK` |
| REQ-SCT-002 | Yes | Yes | Yes | Yes | Successful exits remain `0`, runner failure remains `1`, and admission failure remains `2` |
| REQ-SCT-003 | Yes | Yes | Yes | — | Exact equality, anchored lookalikes, and runner-failure refusal cover positive, edge, and error routes |

## Evidence and provenance

Durable evidence for a qualified run consists of:

- the exact source commit and executable-spec path;
- the admitted pure-Simple CLI path and identity/admission result;
- the truthfulness-gate command line;
- per-scenario exit status and captured diagnostic output;
- a zero-stub docgen result produced by the same admitted CLI; and
- the generated/manual comparison showing all nine frozen steps and the claim
  boundary above are retained.

Current provenance is limited to authored design review of the gate and this
manual mirror. Runtime, SPipe, `sspec-maintain`, and docgen were not run for
this artifact. Therefore the current evidence status remains **TEST_BLOCKED**.
The reviewed static inputs are:

- executable spec SHA-256:
  `71acb8d3e43e4485c33386b86650df6d7fec13ef05ed12c666a9e4b106b80ccb`;
- production gate SHA-256:
  `13bc2a38a1a1475c04712608767ecbe89473e3ead5179f97d343f00bc00b274f`.

These hashes establish authored-review identity only; they are not runtime or
generated-manual provenance.

## Quality score and findings

| Area | Authored-review score | Runtime finding |
|---|---:|---|
| Visible scenario flow | 4/4 | Nine frozen steps specified; generation not yet checked |
| Positive, edge, and error coverage | 4/4 | Four substantive narratives; execution blocked |
| REQ traceability | 4/4 | REQ-SCT-001..003 mapped to observable assertions |
| Fail-closed evidence | 3/4 | Static intent complete; admitted-runtime proof pending |
| Generated-manual fidelity | 0/4 | TEST_BLOCKED: docgen has not run |

**Authored-review total: 15/20.** There are no placeholder-pass findings in
the designed assertions. The open finding is qualification-dependent:
executable results and generated-manual fidelity must remain TEST_BLOCKED until
the admitted CLI produces them.

## Troubleshooting

- **Runner cannot be admitted:** retain the diagnostic and report
  TEST_BLOCKED. Do not switch to the Rust seed or a stale binary.
- **No `Results:` summary:** the gate must fail because no passing count claim
  can be proven. Inspect the captured runner output rather than editing it.
- **Declared count exceeds one in the edge fixture:** inspect whether a
  non-example line begins with statement-position `it`; keep comments and
  strings representative without accidentally creating a real declaration.
- **Failing fixture returns zero:** treat this as a release-blocking false
  green in the runner/gate path; preserve the fixture and full diagnostic.
- **Manual omits a frozen step:** treat docgen/manual quality as failed even if
  executable assertions pass.

## Compatibility and limitations

The manual specifies POSIX-shell gate behavior and Simple SSpec output using a
`Results: N total` summary. It does not qualify alternative test frameworks,
Windows-native shells, legacy runner summary formats, or a compiler that fails
the canonical self-hosted admission check. The anchored-count scenario checks
the current statement-position declaration contract; it is not a general
Simple parser conformance test. This authored mirror is intentionally not a
substitute for the executable spec, runtime transcript, `sspec-maintain`, or
zero-stub generated documentation.
