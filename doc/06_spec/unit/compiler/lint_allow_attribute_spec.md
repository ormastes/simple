# `#![allow(RULE)]` / `@allow(RULE)` lint suppression

> The `primitive_api` rule header has documented two suppression mechanisms since

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `#![allow(RULE)]` / `@allow(RULE)` lint suppression

The `primitive_api` rule header has documented two suppression mechanisms since

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / Lint |
| Status | Regression guard |
| Source | `test/unit/compiler/lint_allow_attribute_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The `primitive_api` rule header has documented two suppression mechanisms since
it was written — `@allow(primitive_api)` on an item and `#[allow(raw_unit)]` for
its neighbour rule — and neither existed. Files under
`src/lib/nogc_sync_mut/engine/physics/` already carried those annotations as if
they were load-bearing; the lint ignored them completely, so every run reported
byte-identical findings with and without the annotation.

An annotation that silently does nothing is worse than no annotation: it teaches
authors that the debt is handled.

The audience is anyone adding a text-scanning EasyFix lint rule that needs a
suppression escape.

## Scope and Preconditions

`compiler.tools.fix.rules.impl_.lint_allow` is the shared machinery: file-scope
`#![allow(...)]` recognised in the header block, and item-scope `@allow(...)` /
`#[allow(...)]` recognised on the contiguous comment/annotation run directly
above a declaration.

Honest scope limit, asserted below rather than glossed: because these rules are
line scanners over raw source, "item scope" reaches exactly one contiguous
comment block upward. Function-body and module-item scope require the AST rule
in `compiler.semantics.lint.primitive_api` and are NOT provided here.

See doc/08_tracking/bug/primitive_api_allow_annotation_unimplemented_2026-08-11.md

## Scenarios

### lint allow attributes

#### recognises every documented spelling of an allow attribute

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognises every documented spelling of an allow attribute
- The Rust-inner spelling used for file scope
- The Rust-outer spelling used for item scope
- The Simple annotation spelling, bare and inside a comment
- A comma-separated list names more than one rule
- A different rule name is NOT suppressed by this line


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognises every documented spelling of an allow attribute")
step("The Rust-inner spelling used for file scope")
expect(line_has_allow("#![allow(primitive_api)]", "primitive_api")).to_be(true)

step("The Rust-outer spelling used for item scope")
expect(line_has_allow("#[allow(raw_unit)]", "raw_unit")).to_be(true)

step("The Simple annotation spelling, bare and inside a comment")
expect(line_has_allow("@allow(primitive_api)", "primitive_api")).to_be(true)
expect(line_has_allow("# @allow(primitive_api)", "primitive_api")).to_be(true)

step("A comma-separated list names more than one rule")
expect(line_has_allow("@allow(primitive_api, raw_unit)", "raw_unit")).to_be(true)

step("A different rule name is NOT suppressed by this line")
expect(line_has_allow("@allow(raw_unit)", "primitive_api")).to_be(false)
```

</details>

#### suppresses the whole file from a header-block #![allow]

- suppresses the whole file from a header-block #![allow]
- Without the annotation the offending signature is reported
- With #![allow(primitive_api)] as the first line, nothing is reported
   - Expected: allowed.len() equals `0`
- An unrelated rule name does not suppress this one
   - Expected: other.len() equals `bare.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suppresses the whole file from a header-block #![allow]")
step("Without the annotation the offending signature is reported")
val bare = check_primitive_api(_sample_offender(), "model.spl")
expect(bare.len()).to_be_greater_than(0)

step("With #![allow(primitive_api)] as the first line, nothing is reported")
val allowed = check_primitive_api("#![allow(primitive_api)]\n" + _sample_offender(), "model.spl")
expect(allowed.len()).to_equal(0)

step("An unrelated rule name does not suppress this one")
val other = check_primitive_api("#![allow(raw_unit)]\n" + _sample_offender(), "model.spl")
expect(other.len()).to_equal(bare.len())
```

</details>

#### ignores a #![allow] that appears after code has started

- ignores a #![allow] that appears after code has started
- File scope means the HEADER block, not anywhere in the file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores a #![allow] that appears after code has started")
step("File scope means the HEADER block, not anywhere in the file")
val src = _sample_offender() + "#![allow(primitive_api)]\n"
expect(check_primitive_api(src, "model.spl").len()).to_be_greater_than(0)
```

</details>

#### suppresses a single declaration from an @allow directly above it

- suppresses a single declaration from an @allow directly above it
- Annotate only the offending declaration
   - Expected: check_primitive_api(src, "model.spl").len() equals `0`
- A second, unannotated declaration further down is still reported


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suppresses a single declaration from an @allow directly above it")
step("Annotate only the offending declaration")
val src = "# @allow(primitive_api)\n" + _sample_offender()
expect(check_primitive_api(src, "model.spl").len()).to_equal(0)

step("A second, unannotated declaration further down is still reported")
val two = "# @allow(primitive_api)\n" + _sample_offender() + "\npub fn evidence_node_at(order: i64) -> text:\n    str(order)\n"
expect(check_primitive_api(two, "model.spl").len()).to_be_greater_than(0)
```

</details>

#### does not let an @allow reach across intervening code

- does not let an @allow reach across intervening code
- A blank line is transparent, but a code line ends the annotation run


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not let an @allow reach across intervening code")
step("A blank line is transparent, but a code line ends the annotation run")
val lines = ["@allow(primitive_api)", "", "pub fn f(a: i64) -> i64:"]
expect(line_is_allowed(lines, 2, "primitive_api")).to_be(true)

val broken = ["@allow(primitive_api)", "pub fn g(b: i64) -> i64:", "pub fn f(a: i64) -> i64:"]
expect(line_is_allowed(broken, 2, "primitive_api")).to_be(false)
```

</details>

#### records the honest scope limit of a text-scanning rule

- records the honest scope limit of a text-scanning rule
- File-scope detection reads only the leading comment/annotation block
- It deliberately reports false once real code has begun


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records the honest scope limit of a text-scanning rule")
step("File-scope detection reads only the leading comment/annotation block")
expect(source_allows_rule("# header comment\n#![allow(primitive_api)]\n\npub fn f(a: i64) -> i64:\n", "primitive_api")).to_be(true)

step("It deliberately reports false once real code has begun")
expect(source_allows_rule("pub fn f(a: i64) -> i64:\n#![allow(primitive_api)]\n", "primitive_api")).to_be(false)
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

- `REQ-SSPEC-UNIT`
- `REQ-LINT-ALLOW-ATTR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e97a5d5da196be41fa53cd7c90a1d6a47879a82cdf1edecfb57895f052788422`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e97a5d5da196be41fa53cd7c90a1d6a47879a82cdf1edecfb57895f052788422`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e97a5d5da196be41fa53cd7c90a1d6a47879a82cdf1edecfb57895f052788422`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/compiler/lint_allow_attribute_spec.spl
mirror: doc/06_spec/unit/compiler/lint_allow_attribute_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/compiler/lint_allow_attribute_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/lint_allow_attribute_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/lint_allow_attribute_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/lint_allow_attribute_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/compiler/lint_allow_attribute_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognises every documented spelling of an allow attribute' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/lint_allow_attribute_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'suppresses the whole file from a header-block #![allow]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/lint_allow_attribute_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores a #![allow] that appears after code has started' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
