# parser_declaration_header_parity_spec

> Regression coverage for compiled_checker_declaration_header_parity_gaps_2026_08_03.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# parser_declaration_header_parity_spec

Regression coverage for compiled_checker_declaration_header_parity_gaps_2026_08_03.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/parser_declaration_header_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression coverage for compiled_checker_declaration_header_parity_gaps_2026_08_03.

The pure-Simple parser accepts canonical metadata blocks, bodyless and legacy
newline declarations, optional class-field types, and complete where clauses.
Malformed where headers still diagnose and a later parse recovers.

## Scenarios

### compiled checker declaration/header parity

#### parses the exact nested arch metadata shape and following declaration

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses the exact nested arch metadata shape and following declaration
   - Expected: parses_clean("metadata_arch_exact.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the exact nested arch metadata shape and following declaration")
val source = "# Token stream → AST\n" +
    "arch {\n" +
    "  dimension = \"feature\"\n" +
    "  imports { allow = [\"shared/**\"] deny = [\"backend/**\"] }\n" +
    "}\n" +
    "fn after_arch() -> i64: 1\n"
expect(parses_clean("metadata_arch_exact.spl", source)).to_equal(true)
```

</details>

#### parses adjacent config and metadata block spellings

- parses adjacent config and metadata block spellings
   - Expected: parses_clean("metadata_adjacent.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses adjacent config and metadata block spellings")
val source = "config { mode = \"debug\" nested { enabled = true } }\n" +
    "metadata { owner = \"compiler\" }\n" +
    "fn after_metadata() -> i64: 2\n"
expect(parses_clean("metadata_adjacent.spl", source)).to_equal(true)
```

</details>

#### preserves consecutive bodyless declarations including public functions

- preserves consecutive bodyless declarations including public functions
   - Expected: parses_clean("bodyless_declarations_exact.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves consecutive bodyless declarations including public functions")
val source = "fn buffer_create(capacity: i64) -> Buffer\n" +
    "fn buffer_read_byte(buf: Buffer) -> i64\n" +
    "pub fn read_char() -> text\n" +
    "fn implemented() -> i64: 3\n"
expect(parses_clean("bodyless_declarations_exact.spl", source)).to_equal(true)
```

</details>

#### parses a colonless indented function body without stealing its successor

- parses a colonless indented function body without stealing its successor
   - Expected: parses_clean("colonless_indented_function.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a colonless indented function body without stealing its successor")
val source = "fn main()\n" +
    "    val image = 1\n" +
    "    image\n" +
    "fn after_main() -> i64: 4\n"
expect(parses_clean("colonless_indented_function.spl", source)).to_equal(true)
```

</details>

#### defaults bare class fields to any beside typed fields and methods

- defaults bare class fields to any beside typed fields and methods
   - Expected: parses_clean("optional_class_field_types.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults bare class fields to any beside typed fields and methods")
val source = "class Snapshot:\n" +
    "    value\n" +
    "    version: i64\n" +
    "    fn get():\n" +
    "        self.value\n" +
    "fn after_class() -> i64: 5\n"
expect(parses_clean("optional_class_field_types.spl", source)).to_equal(true)
```

</details>

#### parses single multiple plus and generic where bounds

- parses single multiple plus and generic where bounds
   - Expected: parses_clean("where_constraints_exact.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses single multiple plus and generic where bounds")
val source = "fn hash_array<T>(arr: [T]) -> i64 where T: Hash: 1\n" +
    "fn hash_pair<T, U>(a: T, b: U) -> i64 where T: Hash + Clone, U: Iterable<T>: 2\n" +
    "fn bodyless<T>() where T: Clone\n" +
    "fn after_where() -> i64: 6\n"
expect(parses_clean("where_constraints_exact.spl", source)).to_equal(true)
```

</details>

#### reports an incomplete where header then recovers on the adjacent family

- reports an incomplete where header then recovers on the adjacent family
   - Expected: parses_clean("where_constraint_bad.spl", "fn bad<T>() where T:\n") is false
   - Expected: parses_clean("where_constraint_recovery.spl", recovered) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports an incomplete where header then recovers on the adjacent family")
expect(parses_clean("where_constraint_bad.spl", "fn bad<T>() where T:\n")).to_equal(false)
val recovered = "fn good<T>() -> i64 where T: Hash + Clone: 7\n" +
    "fn next() -> i64: 8\n"
expect(parses_clean("where_constraint_recovery.spl", recovered)).to_equal(true)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ed0ac2c188a90bd35d5932bb6282f5385c645fb81a46a0645a6a0e0aaddcd73f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ed0ac2c188a90bd35d5932bb6282f5385c645fb81a46a0645a6a0e0aaddcd73f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ed0ac2c188a90bd35d5932bb6282f5385c645fb81a46a0645a6a0e0aaddcd73f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/parser_declaration_header_parity_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/parser_declaration_header_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/parser_declaration_header_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/parser_declaration_header_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/parser_declaration_header_parity_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the exact nested arch metadata shape and following declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/parser_declaration_header_parity_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses adjacent config and metadata block spellings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/parser_declaration_header_parity_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves consecutive bodyless declarations including public functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
