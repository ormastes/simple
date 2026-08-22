# discovery_spec

> Verifies the discovery behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# discovery_spec

Verifies the discovery behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/std/doctest/discovery_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the discovery behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Doctest Source Parsing

#### parse_doctests integration

#### discovers doctests in doc comments

- Verify: discovers doctests in doc comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-DOCTEST_DISCOVERY-001
step("Verify: discovers doctests in doc comments")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val source = "/// Example usage:\n/// >>> 1 + 2\n/// 3\nfn add(a: i64, b: i64) -> i64:\n    a + b\n"
val items = parse_doctests(source, "lib/math.spl")

expect items.len to eq 1
expect items[0].commands to eq ["1 + 2"]
expect items[0].source_path to eq "lib/math.spl"
```

</details>

#### discovers multiple doctests across functions

- Verify: discovers multiple doctests across functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-DOCTEST_DISCOVERY-001
step("Verify: discovers multiple doctests across functions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val source = "/// >>> 1 + 1\n/// 2\nfn foo(): pass\n\n/// >>> 2 + 2\n/// 4\nfn bar(): pass\n"
val items = parse_doctests(source, "lib/ops.spl")

expect items.len to eq 2
expect items[0].commands to eq ["1 + 1"]
expect items[1].commands to eq ["2 + 2"]
```

</details>

#### skips functions without doc comments

- Verify: skips functions without doc comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-DOCTEST_DISCOVERY-001
step("Verify: skips functions without doc comments")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val source = "fn helper(): pass\n\n/// >>> 42\n/// 42\nfn documented(): pass\n"
val items = parse_doctests(source, "lib/mixed.spl")

expect items.len to eq 1
expect items[0].commands to eq ["42"]
```

</details>

#### handles exception expectations in doc comments

- Verify: handles exception expectations in doc comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-DOCTEST_DISCOVERY-001
step("Verify: handles exception expectations in doc comments")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val source = "/// >>> bad_call()\n/// Error: ValueError\nfn risky(): pass\n"
val items = parse_doctests(source, "lib/errors.spl")

expect items.len to eq 1
match items[0].expected:
    case Expected.Exception(type, msg):
        expect type to eq "ValueError"
    case _:
        fail "Expected Exception"
```

</details>

#### preserves line numbers

- Verify: preserves line numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-DOCTEST_DISCOVERY-001
step("Verify: preserves line numbers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val source = "# header\n\n/// >>> 1\n/// 1\nfn f(): pass\n"
val items = parse_doctests(source, "test.spl")

expect items.len to eq 1
expect items[0].start_line to eq 3
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `490728bb7807e27dab16addb416cca33fd1f544efc78162f40158b79045c490e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `490728bb7807e27dab16addb416cca33fd1f544efc78162f40158b79045c490e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `490728bb7807e27dab16addb416cca33fd1f544efc78162f40158b79045c490e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/lib/std/doctest/discovery_spec.spl
mirror: doc/06_spec/02_integration/lib/std/doctest/discovery_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/std/doctest/discovery_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/lib/std/doctest/discovery_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/std/doctest/discovery_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
