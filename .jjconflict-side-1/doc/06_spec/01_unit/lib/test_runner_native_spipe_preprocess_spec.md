# Test Runner Native Spipe Preprocess Specification

> Tests covering native SPipe preprocessing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Native Spipe Preprocess Specification

## Scenarios

### native SPipe preprocessing

#### preserves the legacy wrapper and adds ordered native result guards

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves the legacy wrapper and adds ordered native result guards


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves the legacy wrapper and adds ordered native result guards")
val source = "/tmp/simple_native_spipe_{time_now_unix_micros()}_spec.spl"
val body = "use std.spec.*\n\nfn deliberate_failure():\n    fail(\"deliberate\")\n\ndescribe \"sample\":\n    it \"passes\":\n        expect(2).to_equal(2)   \n        expect 3 to_not_equal 4\n"
expect(file_write(source, body)).to_be(true)

val legacy_path = preprocess_spipe_file(source)
val native_path = preprocess_spipe_native_result_file(source)
val legacy = file_read(legacy_path)
val native = file_read(native_path)
expect(legacy).to_contain("fn main():")
expect(legacy.contains("rt_bdd_executed_count")).to_be(false)
expect(legacy.contains("native result wrapper complete")).to_be(false)
expect(native).to_contain("fn main() -> i64:")
expect(native).to_contain("extern fn rt_exit(code: i64)")
expect(native).to_contain("fn fail_assertion(message: text):\n    print \"    assertion failed: \" + message\n    expect false\n    rt_exit(1)")
expect(native).to_contain("\n            expect(2 == 2)\n")
expect(native).to_contain("expect(3 != 4)")

val clear_at = native.index_of("\n    rt_bdd_clear_state()\n")
val body_at = native.index_of("describe \"sample\"")
val format_at = native.index_of("val __simple_native_spec_failures = rt_bdd_format_results()")
val count_at = native.index_of("val __simple_native_spec_executed = rt_bdd_executed_count()")
val zero_at = native.index_of("__simple_native_spec_executed == 0")
val marker_at = native.index_of("test-runner: native result wrapper complete")
val failure_at = native.index_of("test-runner: spec failed")
expect(body_at).to_be_greater_than(clear_at)
expect(format_at).to_be_greater_than(body_at)
expect(count_at).to_be_greater_than(format_at)
expect(zero_at).to_be_greater_than(count_at)
expect(marker_at).to_be_greater_than(zero_at)
expect(failure_at).to_be_greater_than(marker_at)

delete_if_present(native_path)
delete_if_present(legacy_path)
delete_if_present(source)
```

</details>

#### uses distinct compiler-safe native paths for a hyphenated source path

- uses distinct compiler-safe native paths for a hyphenated source path
   - Expected: file_write(source, "describe \"sample\":\n    it \"passes\":\n        expect(1 equals `1)\n")).to_be(true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses distinct compiler-safe native paths for a hyphenated source path")
val source = "/tmp/simple-font-worktree-{time_now_unix_micros()}-spec.spl"
expect(file_write(source, "describe \"sample\":\n    it \"passes\":\n        expect(1).to_equal(1)\n")).to_be(true)
val first = preprocess_spipe_native_result_file(source)
val second = preprocess_spipe_native_result_file(source)
expect(first == second).to_be(false)
expect(first).to_start_with("/tmp/spipe_native_")
expect(second).to_start_with("/tmp/spipe_native_")
expect(first).to_end_with("_spec.spl")
expect(second).to_end_with("_spec.spl")
expect(first.contains("-")).to_be(false)
expect(second.contains("-")).to_be(false)
delete_if_present(first)
delete_if_present(second)
delete_if_present(source)
```

</details>

#### keeps consecutive font declarations before the generated main

- keeps consecutive font declarations before the generated main


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps consecutive font declarations before the generated main")
val source = "/tmp/simple_native_spipe_font_decls_{time_now_unix_micros()}_spec.spl"
val body = "val FONT_ASSET_ROOT = \"/tmp/fonts\"   \nval FONT_CORPUS_PATH = \"/tmp/fonts/CORPUS\"\nconst FONT_COUNT = 16\nalias FontName = text\nstruct FontRow:\n    family: text\nexport FontRow\nclass FontFixture:\n    name: text\nfn setup_shared_font_fixture() -> FontFixture:\n    FontFixture(name: \"fixture\")\nfn expect_font_license(value: text):\n    expect(value).to_equal(\"OFL\")\ndescribe \"font manifest\":\n    it \"loads pinned data\":\n        step(\"Load the pinned multilingual font manifest\")\n        expect(1).to_equal(1)\n"
expect(file_write(source, body)).to_be(true)
val native_path = preprocess_spipe_native_result_file(source)
val native = file_read(native_path)
val main_at = native.index_of("fn main() -> i64:")
val fixture_at = native.index_of("class FontFixture:")
val setup_at = native.index_of("fn setup_shared_font_fixture()")
val license_at = native.index_of("fn expect_font_license(value: text)")
val step_at = native.index_of("step(\"Load the pinned multilingual font manifest\")")
expect(native.index_of("val FONT_ASSET_ROOT")).to_be_less_than(main_at)
expect(native.index_of("val FONT_CORPUS_PATH")).to_be_less_than(main_at)
expect(native.index_of("const FONT_COUNT")).to_be_less_than(main_at)
expect(native.index_of("alias FontName")).to_be_less_than(main_at)
expect(native.index_of("struct FontRow")).to_be_less_than(main_at)
expect(native.index_of("export FontRow")).to_be_less_than(main_at)
expect(fixture_at).to_be_less_than(main_at)
expect(setup_at).to_be_less_than(main_at)
expect(license_at).to_be_less_than(main_at)
expect(step_at).to_be_greater_than(main_at)
expect(native.contains("\n    fn setup_shared_font_fixture")).to_be(false)
expect(native.contains("\n    fn expect_font_license")).to_be(false)
delete_if_present(native_path)
delete_if_present(source)
```

</details>

#### lowers a font assertion without mistaking numeric conversion for a matcher

- lowers a font assertion without mistaking numeric conversion for a matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers a font assertion without mistaking numeric conversion for a matcher")
val source = "/tmp/simple_native_spipe_font_conversion_{time_now_unix_micros()}_spec.spl"
val body = "describe \"font pixels\":\n    it \"matches the atlas quad\":\n        step(\"Prepare one shared font batch for 2D\")\n        expect(pixels.len()).to_equal((quad.width * quad.height).to_i64())\n        expect(checker).to_contain(\"void main()\")\n"
expect(file_write(source, body)).to_be(true)
val native_path = preprocess_spipe_native_result_file(source)
val native = file_read(native_path)
expect(native_path == "").to_be(false)
expect(native).to_contain("expect(pixels.len() == (quad.width * quad.height).to_i64())")
expect(native).to_contain("expect((checker).contains(\"void main()\"))")
delete_if_present(native_path)
delete_if_present(source)
```

</details>

#### strips the SPipe import and supplies the font inequality helper

- strips the SPipe import and supplies the font inequality helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips the SPipe import and supplies the font inequality helper")
val source = "/tmp/simple_native_spipe_font_assert_ne_{time_now_unix_micros()}_spec.spl"
val body = "use std.spipe.*\n\ndescribe \"font identity\":\n    it \"rejects a stale wrapper\":\n        step(\"Reject a stale global-face wrapper after loading a second selected face\")\n        assert_not_equal(first, second)\n"
expect(file_write(source, body)).to_be(true)
val native_path = preprocess_spipe_native_result_file(source)
val native = file_read(native_path)
expect(native_path == "").to_be(false)
expect(native.contains("use std.spipe")).to_be(false)
expect(native).to_contain("fn assert_not_equal(a, b):")
expect(native).to_contain("assert_not_equal(first, second)")
delete_if_present(native_path)
delete_if_present(source)
```

</details>

#### fails closed for empty, colliding, and unsupported matcher sources

- fails closed for empty, colliding, and unsupported matcher sources
   - Expected: file_write(chained, "describe \"sample\":\n    it \"fails closed\":\n        expect(1 equals `1`
   - Expected: preprocess_spipe_native_result_file(empty) equals ``
   - Expected: preprocess_spipe_native_result_file(collision) equals ``
   - Expected: preprocess_spipe_native_result_file(unsupported) equals ``
   - Expected: preprocess_spipe_native_result_file(multiline) equals ``
   - Expected: preprocess_spipe_native_result_file(chained) equals ``
   - Expected: preprocess_spipe_native_result_file(invalid_arity) equals ``
   - Expected: preprocess_spipe_native_result_file(pending_block) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed for empty, colliding, and unsupported matcher sources")
val stamp = time_now_unix_micros()
val empty = "/tmp/simple_native_spipe_empty_{stamp}_spec.spl"
val collision = "/tmp/simple_native_spipe_collision_{stamp}_spec.spl"
val unsupported = "/tmp/simple_native_spipe_unsupported_{stamp}_spec.spl"
val multiline = "/tmp/simple_native_spipe_multiline_matcher_{stamp}_spec.spl"
val chained = "/tmp/simple_native_spipe_chained_matcher_{stamp}_spec.spl"
val invalid_arity = "/tmp/simple_native_spipe_invalid_arity_{stamp}_spec.spl"
val pending_block = "/tmp/simple_native_spipe_pending_block_{stamp}_spec.spl"
expect(file_write(empty, "")).to_be(true)
expect(file_write(collision, "fn main():\n    print \"collision\"\n")).to_be(true)
expect(file_write(unsupported, "describe \"sample\":\n    it \"fails closed\":\n        expect(1).to_unknown(1)\n")).to_be(true)
expect(file_write(multiline, "describe \"sample\":\n    it \"fails closed\":\n        expect(1)\n            .to_equal(1)\n")).to_be(true)
expect(file_write(chained, "describe \"sample\":\n    it \"fails closed\":\n        expect(1).to_equal(1).to_equal(1)\n")).to_be(true)
expect(file_write(invalid_arity, "describe \"sample\":\n    it \"fails closed\":\n        expect(nil).to_be_nil(fail(\"side effect\"))\n")).to_be(true)
expect(file_write(pending_block, "describe \"sample\":\n    pending_on(\"must not false-green\", \"dependency\", deliberate_failure)\n")).to_be(true)
expect(preprocess_spipe_native_result_file(empty)).to_equal("")
expect(preprocess_spipe_native_result_file(collision)).to_equal("")
expect(preprocess_spipe_native_result_file(unsupported)).to_equal("")
expect(preprocess_spipe_native_result_file(multiline)).to_equal("")
expect(preprocess_spipe_native_result_file(chained)).to_equal("")
expect(preprocess_spipe_native_result_file(invalid_arity)).to_equal("")
expect(preprocess_spipe_native_result_file(pending_block)).to_equal("")
delete_if_present(empty)
delete_if_present(collision)
delete_if_present(unsupported)
delete_if_present(multiline)
delete_if_present(chained)
delete_if_present(invalid_arity)
delete_if_present(pending_block)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner_native_spipe_preprocess_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native SPipe preprocessing.
- native SPipe preprocessing

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58bac70e35f5d791e59650f1d4f9dabe2e28d92673aacc43576fb19e8df7e07b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58bac70e35f5d791e59650f1d4f9dabe2e28d92673aacc43576fb19e8df7e07b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58bac70e35f5d791e59650f1d4f9dabe2e28d92673aacc43576fb19e8df7e07b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/test_runner_native_spipe_preprocess_spec.spl
mirror: doc/06_spec/01_unit/lib/test_runner_native_spipe_preprocess_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/test_runner_native_spipe_preprocess_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/test_runner_native_spipe_preprocess_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/test_runner_native_spipe_preprocess_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves the legacy wrapper and adds ordered native result guards' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner_native_spipe_preprocess_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses distinct compiler-safe native paths for a hyphenated source path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner_native_spipe_preprocess_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps consecutive font declarations before the generated main' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
