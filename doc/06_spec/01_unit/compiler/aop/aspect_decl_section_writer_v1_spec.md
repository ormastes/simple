# Writing `aspect-decl|` from a compiled module

> Purpose: document and pin

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Writing `aspect-decl|` from a compiled module

Purpose: document and pin

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/aop/aspect_decl_section_writer_v1_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: document and pin
`src/compiler/80.driver/cache/aspect_tldr_section_writer_v1.spl`, the writer
that turns one module's typed-HIR aspect capture into its `aspect-decl|` TLDR
entry (aspect plan stage AW-1), and prove the stage's two edit rules on real
parsed and lowered modules rather than on hand-built rows:

- editing an advice body changes only the `advice.body` facet;
- editing a selector changes the declaration row and the module's leaf digest.

Audience: compiler engineers wiring TLDR publication and reviewers deciding
what an advice edit is allowed to invalidate.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/aop/aspect_decl_section_writer_v1_spec.spl`
   from the repository root. Every scenario parses and lowers a small module
   in memory; no file is read.
2. Measure coverage with
   `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<f> <seed> run <this spec>`
   (doc/07_guide/infra/testing/coverage.md).

## How the writer gets its inputs

| Input | Source |
|-------|--------|
| declarations, handler signature and effects, leaf digest | `directory_aspect_semantic_capture_v2`, run while the module's HIR owner is alive |
| handler body digest | sha256 over the handler's own source span (`HirFunction.span`), blank edges trimmed |

The body digest is taken from source text, so a comment or layout change
inside the handler counts as a body edit. That is conservative: it can cause
an extra rebuild of the advice object, never a stale one.

## Lifecycle

Research: doc/01_research/local/dir_tldr_aspect.md
Plan: doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md (AW-1)
Architecture: doc/04_architecture/compiler/aspect_dynload/typed_facet_pipeline_2026-08-22.md
Design: doc/05_design/compiler/cache/aspect_tldr_async_trace.md (section 3)

## Decision inventory (MC/DC)

| Function | Decision | Covering scenario |
|----------|----------|-------------------|
| `aspect_function_body_digests_v1` | loop over the module's functions: none left / one more | every scenario (one or two functions) |
| `aspect_decl_tldr_entry_v1` | section built or refused (match arms) | "a compiled module writes one row per declaration", "a source that is not the parsed text is refused" |

Exclusions: none. All fail-closed rules live in the pure codec and are
covered by `aspect_decl_section_v1_spec.spl`.

## Compatibility and limitations

The writer is not yet called by TLDR publication: publication runs at parse
time, before the typed-HIR capture exists. Until the engine's write-once slots
land, a caller that holds the capture appends the entry itself.

## Scenarios

### aspect_decl_tldr_entry_v1

#### a compiled module writes one row per declaration

- Compile a module with one `@advice` function and write its aspect-decl entry
- The entry decodes to one logical row carrying the capture's digests and the handler body digest
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: entry.starts_with("aspect-decl|") is true
   - Expected: section.leaf_digest equals `built.semantic.interface_digest`
   - Expected: section.rows[0].signature_digest equals `built.semantic.handlers[0].signature_digest`
   - Expected: section.rows[0].effects_digest equals `built.semantic.handlers[0].effects_digest`
   - Expected: section.rows[0].body_digest.byte_len() equals `64)  # oracle: sha256 hex width`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-WRITER
step("Compile a module with one `@advice` function and write its aspect-decl entry")
val built = compiled(LOGICAL)
val entry = aspect_decl_tldr_entry_v1(built.semantic, built.module, built.source).unwrap()
val section = aspect_decl_section_of_entries_v1([entry]).section
step("The entry decodes to one logical row carrying the capture's digests and the handler body digest")
expect(entry.starts_with("aspect-decl|")).to_equal(true)
expect(section.leaf_digest).to_equal(built.semantic.interface_digest)
expect([section.rows[0].family, section.rows[0].handler, section.rows[0].form,
    section.rows[0].selector, section.rows[0].activation]).to_equal(
    ["logical", "observe", "forward", "submit", "static"])
expect(section.rows[0].signature_digest).to_equal(built.semantic.handlers[0].signature_digest)
expect(section.rows[0].effects_digest).to_equal(built.semantic.handlers[0].effects_digest)
expect(section.rows[0].body_digest).to_equal(
    aspect_function_body_digests_v1(built.module, built.source)["observe"])
expect(section.rows[0].body_digest.byte_len()).to_equal(64)  # oracle: sha256 hex width
```

</details>

#### both families are written, mir rows first

- Compile a module that declares an `on pc{...}` advice and an `@advice` function
- The section has a mir row for `hook` and a logical row for `observe`, with different ids
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: [section.rows[1].family, section.rows[1].handler] equals `["logical", "observe"]`
   - Expected: section.rows[0].advice_id == section.rows[1].advice_id is false
   - Expected: section.rows[0].body_digest == section.rows[1].body_digest is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-WRITER
step("Compile a module that declares an `on pc{...}` advice and an `@advice` function")
val section = section_of(MIR_PART + "\n\nfn hook():\n    return\n\n" + LOGICAL)
step("The section has a mir row for `hook` and a logical row for `observe`, with different ids")
expect([section.rows[0].family, section.rows[0].handler, section.rows[0].form]).to_equal(
    ["mir", "hook", "before"])
expect([section.rows[1].family, section.rows[1].handler]).to_equal(["logical", "observe"])
expect(section.rows[0].advice_id == section.rows[1].advice_id).to_equal(false)
expect(section.rows[0].body_digest == section.rows[1].body_digest).to_equal(false)
```

</details>

#### a module without advice writes a section with no row

- Compile a module that declares no advice and write its entry
- The section exists, names the module and has no row, so absence of advice is a stated fact
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: section.rows.len() equals `0)  # oracle: no declaration in the source`
   - Expected: section.module_identity == "" is false
   - Expected: section.leaf_digest.byte_len() equals `64)  # oracle: sha256 hex width`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-WRITER
step("Compile a module that declares no advice and write its entry")
val section = section_of(PLAIN)
step("The section exists, names the module and has no row, so absence of advice is a stated fact")
expect(section.rows.len()).to_equal(0)  # oracle: no declaration in the source
expect(section.module_identity == "").to_equal(false)
expect(section.leaf_digest.byte_len()).to_equal(64)  # oracle: sha256 hex width
```

</details>

#### a source that is not the parsed text is refused

- Write the entry of a compiled module while passing another source text
- No entry is produced, because the handler span does not hold the handler in that text
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: wrong.unwrap_err() equals `advice-body-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-WRITER
step("Write the entry of a compiled module while passing another source text")
val built = compiled(LOGICAL)
val wrong = aspect_decl_tldr_entry_v1(built.semantic, built.module, PLAIN)
step("No entry is produced, because the handler span does not hold the handler in that text")
expect(wrong.unwrap_err()).to_equal("advice-body-unavailable")
```

</details>

### aspect-decl edit rules on compiled modules

#### an advice body edit changes only the advice.body facet

- Compile the module, edit only the body of the advice function, and compile it again
- The leaf digest and the row digest are equal; only the body facet differs
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: after.leaf_digest equals `before.leaf_digest`
   - Expected: aspect_decl_row_digest_v1(after.rows[0]) equals `aspect_decl_row_digest_v1(before.rows[0])`
   - Expected: after.rows[0].body_digest == before.rows[0].body_digest is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FACETS
step("Compile the module, edit only the body of the advice function, and compile it again")
val before = section_of(LOGICAL)
val after = section_of(BODY_EDIT)
step("The leaf digest and the row digest are equal; only the body facet differs")
expect(after.leaf_digest).to_equal(before.leaf_digest)
expect(aspect_decl_row_digest_v1(after.rows[0])).to_equal(aspect_decl_row_digest_v1(before.rows[0]))
expect(after.rows[0].body_digest == before.rows[0].body_digest).to_equal(false)
```

</details>

#### a selector edit changes the row and the leaf digest

- Compile the module, change only the selector of the `@advice` line, and compile it again
- Leaf digest, row digest and selector id change; the advice id and the body facet do not
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: after.leaf_digest == before.leaf_digest is false
   - Expected: aspect_decl_row_digest_v1(after.rows[0]) == aspect_decl_row_digest_v1(before.rows[0]) is false
   - Expected: after.rows[0].selector_id == before.rows[0].selector_id is false
   - Expected: after.rows[0].advice_id equals `before.rows[0].advice_id`
   - Expected: after.rows[0].body_digest equals `before.rows[0].body_digest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FACETS
step("Compile the module, change only the selector of the `@advice` line, and compile it again")
val before = section_of(LOGICAL)
val after = section_of(SELECTOR_EDIT)
step("Leaf digest, row digest and selector id change; the advice id and the body facet do not")
expect(after.leaf_digest == before.leaf_digest).to_equal(false)
expect(aspect_decl_row_digest_v1(after.rows[0]) == aspect_decl_row_digest_v1(before.rows[0])).to_equal(false)
expect(after.rows[0].selector_id == before.rows[0].selector_id).to_equal(false)
expect(after.rows[0].advice_id).to_equal(before.rows[0].advice_id)
expect(after.rows[0].body_digest).to_equal(before.rows[0].body_digest)
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

- `REQ-ASPECT-AW1-WRITER`
- `REQ-ASPECT-AW1-FACETS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b3d5a6dfd48b186c36a9dc6d8e003e6a936607aec74b754af75228322f3a7794`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b3d5a6dfd48b186c36a9dc6d8e003e6a936607aec74b754af75228322f3a7794`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b3d5a6dfd48b186c36a9dc6d8e003e6a936607aec74b754af75228322f3a7794`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: 01_unit/compiler/aop/aspect_decl_section_writer_v1_spec.spl
mirror: doc/06_spec/01_unit/compiler/aop/aspect_decl_section_writer_v1_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/aop/aspect_decl_section_writer_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/aop/aspect_decl_section_writer_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
