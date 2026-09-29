# smf_reader_bridge_parity_class_spec

> Class-detection spec for the "SFFI bridge silently returns empty" defect class.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smf_reader_bridge_parity_class_spec

Class-detection spec for the "SFFI bridge silently returns empty" defect class.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/smf_reader_bridge_parity_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Class-detection spec for the "SFFI bridge silently returns empty" defect class.

Related bug: doc/08_tracking/bug/smf_reader_bridge_silent_nil.md

The defect class is NOT "one extern was missing". It is: a reader whose data
path runs through an unregistered extern still reports SUCCESS, and hands back
a well-formed but EMPTY answer. Nothing crashes, nothing logs, and the caller
cannot tell an empty module from a module it failed to read.

The generalizing invariant asserted here is a DIFFERENTIAL one, and it holds
regardless of which extern is or is not implemented:

    for the same bytes, the file-backed reader (SmfReaderImpl) and the
    in-memory reader (SmfReaderMemory, ~919 lines of pure Simple with no
    externs at all) must agree.

SmfReaderMemory is the oracle: it has no extern in its path, so it cannot
exhibit this defect and it cannot be silently emptied. Any future change that
re-routes a reader back onto an unimplemented extern -- or onto any bridge that
fails open -- breaks parity here even if the reproducing spec's specific
assertions were re-tuned around it.

The last two examples pin NON-VACUITY: the oracle itself must report non-empty
for a non-empty input, so a run where BOTH readers return empty is a failure
rather than a spurious pass.

## Scenarios

### SMF reader bridges never fail open into an empty answer

#### agrees with the in-memory oracle on a module with no symbols

- agrees with the in-memory oracle on a module with no symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees with the in-memory oracle on a module with no symbols")
assert_parity("none", fixture_no_symbols())
```

</details>

#### agrees with the in-memory oracle on a module with one symbol

- agrees with the in-memory oracle on a module with one symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees with the in-memory oracle on a module with one symbol")
assert_parity("one", fixture_one_symbol())
```

</details>

#### agrees with the in-memory oracle on a module with three symbols

- agrees with the in-memory oracle on a module with three symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees with the in-memory oracle on a module with three symbols")
assert_parity("three", fixture_three_symbols())
```

</details>

#### propagates a read failure instead of reporting an empty success

- propagates a read failure instead of reporting an empty success
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("propagates a read failure instead of reporting an empty success")
# A path that does not exist must be an Err. The defining symptom of
# this class was Ok-with-nothing-in-it.
val result = SmfReaderImpl.open("/tmp/smf_bridge_parity_absent_7c21.smf")
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects a file that is not SMF instead of reporting an empty success

- rejects a file that is not SMF instead of reporting an empty success
   - Expected: SmfReaderImpl.open(path).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a file that is not SMF instead of reporting an empty success")
var junk: [u8] = [0, 1, 2, 3]
while junk.len() < 300:
    junk.push(7)
val path = write_fixture("junk", junk)
expect(SmfReaderImpl.open(path).is_err()).to_equal(true)
```

</details>

#### the oracle reports a non-empty symbol set for a non-empty fixture

- the oracle reports a non-empty symbol set for a non-empty fixture
   - Expected: oracle.get_header().symbol_count equals `3`
   - Expected: oracle.exported_symbols().len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the oracle reports a non-empty symbol set for a non-empty fixture")
val oracle = SmfReaderMemory.from_data(fixture_three_symbols()).unwrap()
expect(oracle.get_header().symbol_count).to_equal(3)
expect(oracle.exported_symbols().len()).to_equal(3)
```

</details>

#### the oracle resolves each fixture symbol by its real name

- the oracle resolves each fixture symbol by its real name
   - Expected: oracle.lookup_symbol("alpha").is_ok() is true
   - Expected: oracle.lookup_symbol("beta").is_ok() is true
   - Expected: oracle.lookup_symbol("gamma").is_ok() is true
   - Expected: oracle.lookup_symbol("not_present").is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the oracle resolves each fixture symbol by its real name")
val oracle = SmfReaderMemory.from_data(fixture_three_symbols()).unwrap()
expect(oracle.lookup_symbol("alpha").is_ok()).to_equal(true)
expect(oracle.lookup_symbol("beta").is_ok()).to_equal(true)
expect(oracle.lookup_symbol("gamma").is_ok()).to_equal(true)
expect(oracle.lookup_symbol("not_present").is_err()).to_equal(true)
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `da5285a6ba02a271549637c3db3100fd50ff4e7135445ef215b7d9aa8442f1b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da5285a6ba02a271549637c3db3100fd50ff4e7135445ef215b7d9aa8442f1b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da5285a6ba02a271549637c3db3100fd50ff4e7135445ef215b7d9aa8442f1b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/linker/smf_reader_bridge_parity_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/linker/smf_reader_bridge_parity_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/linker/smf_reader_bridge_parity_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/linker/smf_reader_bridge_parity_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/linker/smf_reader_bridge_parity_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/linker/smf_reader_bridge_parity_class_spec.spl:185:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with the in-memory oracle on a module with no symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/smf_reader_bridge_parity_class_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with the in-memory oracle on a module with one symbol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/smf_reader_bridge_parity_class_spec.spl:195:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with the in-memory oracle on a module with three symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
