# text_builtin_rfind_lowering_spec

> Purpose: Prove that Text builtin rfind MIR lowering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# text_builtin_rfind_lowering_spec

Purpose: Prove that Text builtin rfind MIR lowering.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/text_builtin_rfind_lowering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Text builtin rfind MIR lowering.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Text builtin rfind MIR lowering

#### keeps a replace result on the string runtime owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps a replace result on the string runtime owner
- Verify: keeps a replace result on the string runtime owner
   - Expected: mir does not contain `rt_string_to_lower`
   - Expected: mir does not contain `DoubleEndedIterator`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a replace result on the string runtime owner")
step("Verify: keeps a replace result on the string runtime owner")
# @req: REQ-COMPILER-MIR-001
val source = "fn parent_dir(path: text) -> i64:\n    val normalized = path.replace(\"\\\\\", \"/\")\n    return normalized.rfind(\"/\")\n"
val mir = lower_text_method_mir(source, "parent_dir")

expect(mir).to_contain("rt_string_replace")
expect(mir).to_contain("rt_string_rfind")
expect(mir.contains("rt_string_to_lower")).to_equal(false)
expect(mir.contains("DoubleEndedIterator")).to_equal(false)
```

</details>

### Primitive text conversion MIR lowering

#### selects each scalar renderer for both aliases

- selects each scalar renderer for both aliases
- Verify: selects each scalar renderer for both aliases
   - Expected: mir.split("rt_raw_bool_to_string").len() - 1 equals `2`
   - Expected: mir.split("rt_raw_f64_to_string").len() - 1 equals `2`
   - Expected: mir.split("rt_raw_u64_to_string").len() - 1 equals `2`
   - Expected: mir.split("rt_raw_i64_to_string").len() - 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("selects each scalar renderer for both aliases")
step("Verify: selects each scalar renderer for both aliases")
val source = "fn render_string(b: bool, f: f64, u: u64, i: i64) -> text:\n    b.to_string() + \"|\" + f.to_string() + \"|\" + u.to_string() + \"|\" + i.to_string()\n\nfn render_text(b: bool, f: f64, u: u64, i: i64) -> text:\n    b.to_text() + \"|\" + f.to_text() + \"|\" + u.to_text() + \"|\" + i.to_text()\n"
val mir = lower_text_method_mir(source, "primitive_to_string")

expect(mir.split("rt_raw_bool_to_string").len() - 1).to_equal(2)
expect(mir.split("rt_raw_f64_to_string").len() - 1).to_equal(2)
expect(mir.split("rt_raw_u64_to_string").len() - 1).to_equal(2)
expect(mir.split("rt_raw_i64_to_string").len() - 1).to_equal(2)
```

</details>

### Text char_code_at MIR lowering

#### rejects a source definition of the compiler-reserved alias

- rejects a source definition of the compiler-reserved alias
- Verify: rejects a source definition of the compiler-reserved alias
   - Expected: lowering.errors.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a source definition of the compiler-reserved alias")
step("Verify: rejects a source definition of the compiler-reserved alias")
val module = parse_full_frontend("fn __simple_rt_string_char_code_at(value: i64, index: i64) -> i64:\n    999\n", "reserved_alias.spl", "reserved_alias.spl", Logger(level: 0))
var lowering = HirLowering.with_filename("reserved_alias.spl")
val _hir = lowering.lower_module(module)

expect(lowering.errors.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(lowering.errors[0].message).to_contain("is reserved for compiler-generated text calls")
```

</details>

#### accepts the alias only from the canonical runtime module

- accepts the alias only from the canonical runtime module
- Verify: accepts the alias only from the canonical runtime module
   - Expected: lowering.errors.len() equals `0`
   - Expected: spoof_lowering.errors.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts the alias only from the canonical runtime module")
step("Verify: accepts the alias only from the canonical runtime module")
val source = "fn __simple_rt_string_char_code_at(value: i64, index: i64) -> i64:\n    999\n"
for filename in ["src/runtime/simple_core/core_string.spl", "src\\runtime\\simple_core\\core_string.spl"]:
    val module = parse_full_frontend(source, filename, filename, Logger(level: 0))
    var lowering = HirLowering.with_filename(filename)
    val _hir = lowering.lower_module(module)

    expect(lowering.errors.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement

val spoof = "/tmp/project/src/runtime/simple_core/core_string.spl"
val spoof_module = parse_full_frontend(source, spoof, spoof, Logger(level: 0))
var spoof_lowering = HirLowering.with_filename(spoof)
val _spoof_hir = spoof_lowering.lower_module(spoof_module)
expect(spoof_lowering.errors.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### uses the reserved raw runtime ABI without capturing a source function

- uses the reserved raw runtime ABI without capturing a source function
- Verify: uses the reserved raw runtime ABI without capturing a source function
   - Expected: mir.split("__simple_rt_string_char_code_at").len() - 1 equals `2`
   - Expected: mir does not contain `rt_strlen`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses the reserved raw runtime ABI without capturing a source function")
step("Verify: uses the reserved raw runtime ABI without capturing a source function")
val source = "fn rt_string_char_code_at(value: i64, index: i64) -> i64:\n    return 999\n\nfn codes() -> i64:\n    val tagged = \"X\" + \"Y\"\n    return \"X\".char_code_at(0) + tagged.char_code_at(0) + rt_string_char_code_at(1, 2)\n"
val mir = lower_text_method_mir(source, "text_char_code_at")

expect(mir.split("__simple_rt_string_char_code_at").len() - 1).to_equal(2)
expect(mir).to_contain("\"name\":\"rt_string_char_code_at\"")
expect(mir.contains("rt_strlen")).to_equal(false)
```

</details>

### Text predicate custom-owner MIR lowering

#### keeps custom predicate methods ahead of text fallbacks

- keeps custom predicate methods ahead of text fallbacks
- Verify: keeps custom predicate methods ahead of text fallbacks
   - Expected: mir does not contain `rt_string_starts_with`
   - Expected: mir does not contain `rt_string_ends_with`
   - Expected: mir does not contain `rt_string_contains`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps custom predicate methods ahead of text fallbacks")
step("Verify: keeps custom predicate methods ahead of text fallbacks")
val source = "struct PredicateOwner:\n    marker: i64\n\nimpl PredicateOwner:\n    fn starts_with(self, value: text) -> bool: self.marker == value.len()\n    fn ends_with(self, value: text) -> bool: self.marker != value.len()\n    fn contains(self, value: text) -> bool: self.marker > value.len()\n\nstruct StaticPredicates:\n    marker: i64\n\nimpl StaticPredicates:\n    static fn starts_with(value: text) -> bool: value.len() == 1\n    static fn ends_with(value: text) -> bool: value.len() == 2\n    static fn contains(value: text) -> bool: value.len() == 3\n\nfn predicate_calls(owner: PredicateOwner) -> bool:\n    owner.starts_with(\"a\") and owner.ends_with(\"bb\") and owner.contains(\"ccc\") and StaticPredicates.starts_with(\"a\") and StaticPredicates.ends_with(\"bb\") and StaticPredicates.contains(\"ccc\")\n"
val mir = lower_text_method_mir(source, "predicate_owner")

expect(mir.split("PredicateOwner::starts_with").len() - 1).to_be_greater_than(1)
expect(mir.split("PredicateOwner::ends_with").len() - 1).to_be_greater_than(1)
expect(mir.split("PredicateOwner::contains").len() - 1).to_be_greater_than(1)
expect(mir.split("StaticPredicates::starts_with").len() - 1).to_be_greater_than(1)
expect(mir.split("StaticPredicates::ends_with").len() - 1).to_be_greater_than(1)
expect(mir.split("StaticPredicates::contains").len() - 1).to_be_greater_than(1)
expect(mir.contains("rt_string_starts_with")).to_equal(false)
expect(mir.contains("rt_string_ends_with")).to_equal(false)
expect(mir.contains("rt_string_contains")).to_equal(false)
```

</details>

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

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-MIR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2c0a0e828cb8292b36d58bcc67db4c88cdf0b28aa2fbad794b0f3dafecfa77c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c0a0e828cb8292b36d58bcc67db4c88cdf0b28aa2fbad794b0f3dafecfa77c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c0a0e828cb8292b36d58bcc67db4c88cdf0b28aa2fbad794b0f3dafecfa77c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mir/text_builtin_rfind_lowering_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/text_builtin_rfind_lowering_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/text_builtin_rfind_lowering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/text_builtin_rfind_lowering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/text_builtin_rfind_lowering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/text_builtin_rfind_lowering_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a replace result on the string runtime owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/text_builtin_rfind_lowering_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects each scalar renderer for both aliases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/text_builtin_rfind_lowering_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a source definition of the compiler-reserved alias' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
