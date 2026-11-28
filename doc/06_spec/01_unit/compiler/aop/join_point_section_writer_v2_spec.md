# Writing `join-point|` from a compiled module, and facts from sections

> Purpose: document and pin `join_point_tldr_entry_v2` in

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Writing `join-point|` from a compiled module, and facts from sections

Purpose: document and pin `join_point_tldr_entry_v2` in

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/aop/join_point_section_writer_v2_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: document and pin `join_point_tldr_entry_v2` in
`src/compiler/80.driver/cache/aspect_tldr_section_writer_v1.spl` (aspect plan
stage AW-2), and prove on real parsed and lowered modules that:

- directory facts built from the members' `join-point|` sections equal the
  facts the compiler builds today from every member's HIR
  (`aop_directory_facts_from_hir_v1`), on a directory with private functions,
  attributes and a static guard;
- the section rows additionally carry a signature digest and a real base body
  digest, which the HIR-built facts do not;
- a member that has not written its section makes the facts incomplete;
- the directory aspect root is independent of member order and unchanged by an
  advice body edit.

Audience: compiler engineers replacing whole-program fact collection with
per-module sections, and reviewers checking that the replacement cannot change
a match result.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/aop/join_point_section_writer_v2_spec.spl`
   from the repository root. Every scenario parses and lowers small modules in
   memory; no file is read.
2. Measure coverage with
   `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<f> <seed> run <this spec>`
   (doc/07_guide/infra/testing/coverage.md).

## How the writer gets its inputs

| Row field | Source |
|-----------|--------|
| kind, symbol | `forward_join_points_for_module_v1`: every pure forwarder of the module, exported or not |
| attrs | the parser's join-point attribute registry for the module path |
| signature digest | `hir_abi_function_digest_v1` of the forwarder (parameters, result, effects; no body) |
| base body digest | sha256 over the forwarder's own source span, blank edges trimmed |
| guards | supplied by the caller: the module's static guard evaluations for the target profile |

## Lifecycle

Research: doc/01_research/local/dir_tldr_aspect.md
Plan: doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md (AW-2)
Architecture: doc/04_architecture/compiler/aspect_dynload/typed_facet_pipeline_2026-08-22.md
Design: doc/05_design/compiler/cache/aspect_tldr_async_trace.md (section 3, gap G15)

## Decision inventory (MC/DC)

| Function | Decision | Covering scenario |
|----------|----------|-------------------|
| `join_point_tldr_entry_v2` | module has a source path / only a module key | "facts from sections equal facts from HIR", "a module without a source path is owned by its key" |
| `join_point_tldr_entry_v2` | loop over functions: none left / one more | every scenario |
| `join_point_tldr_entry_v2` | section built or refused (match arms) | "facts from sections equal facts from HIR", "a source that is not the parsed text is refused" |

Exclusions: the `Err` arm of the signature digest (`hir_abi_function_digest_v1`
fails only for a function whose types cannot be encoded) is a match arm with
no fixture; such a function gets an empty digest, which the pure builder
refuses (`join-point-signature-unavailable`, covered in
`join_point_section_v2_spec.spl`).

## Compatibility and limitations

The writer is not yet called by TLDR publication, for the same reason as the
`aspect-decl|` writer: publication runs before typed HIR exists.
The parity scenario compares facts key, negative root, guard root, ids,
attributes and completeness. `base_body_digest` is excluded from the equality
because the HIR path leaves it empty; it is asserted separately.

## Scenarios

### join_point_tldr_entry_v2

#### facts from sections equal facts from HIR

- Lower two modules of directory `pay`, build its facts from HIR, then from the two modules' sections
- Scope, completeness, facts key, negative root, guard root, members, ids and attributes are equal
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: from_hir.len() equals `1)  # oracle: both modules are in the one directory `pay``
   - Expected: from_sections.complete is true
   - Expected: selector_visible(from_sections) equals `selector_visible(from_hir[0])`
   - Expected: from_sections.sorted_join_points.len() equals `3)  # oracle: submit_view, _hidden_view, refund_view`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-PARITY
step("Lower two modules of directory `pay`, build its facts from HIR, then from the two modules' sections")
val modules = pay_modules()
val from_hir = aop_directory_facts_from_hir_v1(modules, guard_sources())
val sections = pay_sections(modules)
val from_sections = directory_join_point_facts_of_sections_v2("pay", [FILE_A, FILE_B], sections,
    aop_guard_profile_v1())
step("Scope, completeness, facts key, negative root, guard root, members, ids and attributes are equal")
expect(from_hir.len()).to_equal(1)  # oracle: both modules are in the one directory `pay`
expect(from_sections.complete).to_equal(true)
expect(selector_visible(from_sections)).to_equal(selector_visible(from_hir[0]))
expect(from_sections.sorted_join_points.len()).to_equal(3)  # oracle: submit_view, _hidden_view, refund_view
```

</details>

#### section rows carry a signature digest and a real base body digest

- Write and read back the sections of both modules and build the directory facts from them
- Every row has both digests, the private forwarder is a row, the guarded file lists its guard, and the HIR path has no body digest
   - Exec capture: after_step
   - Evidence: execution result verified by 10 expected checks
   - Expected: [a_points[0].id, a_points[1].id] equals `["pay_a::_hidden_view", "pay_a::submit_view"]`
   - Expected: a_points[1].attrs equals `["logged"]`
   - Expected: point.signature_digest.byte_len() equals `64)  # oracle: sha256 hex width`
   - Expected: point.base_body_digest.byte_len() equals `64)  # oracle: sha256 hex width`
   - Expected: a_points[0].base_body_digest == a_points[1].base_body_digest is false
   - Expected: a_points[0].guard_ids equals `[]`
   - Expected: sections[1].points[0].guard_ids.len() equals `sections[1].guards.len()`
   - Expected: sections[1].guards.len() > 0 is true
   - Expected: point.base_body_digest.byte_len() equals `64)  # oracle: sha256 hex width`
   - Expected: point.base_body_digest equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-WRITER
step("Write and read back the sections of both modules and build the directory facts from them")
val modules = pay_modules()
val sections = pay_sections(modules)
val facts = directory_join_point_facts_of_sections_v2("pay", [FILE_A, FILE_B], sections,
    aop_guard_profile_v1())
val hir_facts = aop_directory_facts_from_hir_v1(modules, guard_sources())[0]
val a_points = sections[0].points
step("Every row has both digests, the private forwarder is a row, the guarded file lists its guard, and the HIR path has no body digest")
expect([a_points[0].id, a_points[1].id]).to_equal(["pay_a::_hidden_view", "pay_a::submit_view"])
expect(a_points[1].attrs).to_equal(["logged"])
for section in sections:
    for point in section.points:
        expect(point.signature_digest.byte_len()).to_equal(64)  # oracle: sha256 hex width
        expect(point.base_body_digest.byte_len()).to_equal(64)  # oracle: sha256 hex width
expect(a_points[0].base_body_digest == a_points[1].base_body_digest).to_equal(false)
expect(a_points[0].guard_ids).to_equal([])
expect(sections[1].points[0].guard_ids.len()).to_equal(sections[1].guards.len())
expect(sections[1].guards.len() > 0).to_equal(true)
for point in facts.sorted_join_points:
    expect(point.base_body_digest.byte_len()).to_equal(64)  # oracle: sha256 hex width
for point in hir_facts.sorted_join_points:
    expect(point.base_body_digest).to_equal("")
```

</details>

#### a member without a section makes the facts incomplete

- Build the facts of `pay` from the section of pay_a only
- The facts are incomplete; with both sections they are complete
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: facts.complete is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-PARITY
step("Build the facts of `pay` from the section of pay_a only")
val modules = pay_modules()
val only_a = [section_of("pay_a", modules["pay_a"], SOURCE_A)]
val facts = directory_join_point_facts_of_sections_v2("pay", [FILE_A, FILE_B], only_a,
    aop_guard_profile_v1())
step("The facts are incomplete; with both sections they are complete")
expect(facts.complete).to_equal(false)
expect(directory_join_point_facts_of_sections_v2("pay", [FILE_A, FILE_B], pay_sections(modules),
    aop_guard_profile_v1()).complete).to_equal(true)
```

</details>

#### a module without a source path is owned by its key

- Write the section of a lowered module whose path was cleared
- The owner file is the module key; with a path it is the path
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: keyed.owner_file equals `pay_b`
   - Expected: pathed.owner_file equals `FILE_B`
   - Expected: keyed.points[0].id equals `pathed.points[0].id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-WRITER
step("Write the section of a lowered module whose path was cleared")
val module = lower(SOURCE_B, FILE_B, "pay_b")
val keyed = section_of("pay_b", HirModule(..module, path: ""), SOURCE_B)
val pathed = section_of("pay_b", module, SOURCE_B)
step("The owner file is the module key; with a path it is the path")
expect(keyed.owner_file).to_equal("pay_b")
expect(pathed.owner_file).to_equal(FILE_B)
expect(keyed.points[0].id).to_equal(pathed.points[0].id)
```

</details>

#### a source that is not the parsed text is refused

- Write the section of pay_a while passing the source of pay_b
- No entry is produced: a forwarder span that does not hold the forwarder has no body digest
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: wrong.unwrap_err() equals `join-point-body-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-WRITER
step("Write the section of pay_a while passing the source of pay_b")
val module = lower(SOURCE_A, FILE_A, "pay_a")
val wrong = join_point_tldr_entry_v2("pay_a", module, SOURCE_B, aop_guard_profile_v1(), [])
step("No entry is produced: a forwarder span that does not hold the forwarder has no body digest")
expect(wrong.unwrap_err()).to_equal("join-point-body-unavailable")
```

</details>

### aspect root of compiled advice modules

#### an advice body edit leaves the aspect root unchanged and a selector edit changes it

- Capture the leaf digest of an advice module, of its body edit and of its selector edit
- The root is the same for the body edit and in the other member order, and differs for the selector edit
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: aspect_root_digest_v1([body_edit_leaf, sibling], [child]) equals `root`
   - Expected: aspect_root_digest_v1([sibling, leaf], [child]) equals `root`
   - Expected: aspect_root_digest_v1([selector_edit_leaf, sibling], [child]) == root is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-ROOT
step("Capture the leaf digest of an advice module, of its body edit and of its selector edit")
val leaf = aspect_leaf(ADVICE)
val body_edit_leaf = aspect_leaf(ADVICE_BODY_EDIT)
val selector_edit_leaf = aspect_leaf(ADVICE_SELECTOR_EDIT)
val sibling = sha256_text("leaf of a sibling module")
val child = aspect_root_digest_v1([sha256_text("leaf in a child directory")], [])
val root = aspect_root_digest_v1([leaf, sibling], [child])
step("The root is the same for the body edit and in the other member order, and differs for the selector edit")
expect(aspect_root_digest_v1([body_edit_leaf, sibling], [child])).to_equal(root)
expect(aspect_root_digest_v1([sibling, leaf], [child])).to_equal(root)
expect(aspect_root_digest_v1([selector_edit_leaf, sibling], [child]) == root).to_equal(false)
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

- `REQ-ASPECT-AW2-WRITER`
- `REQ-ASPECT-AW2-PARITY`
- `REQ-ASPECT-AW2-ROOT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f5840419b00ac8c5c85f293513971308429bb87457025125d9a26640a3222fa9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f5840419b00ac8c5c85f293513971308429bb87457025125d9a26640a3222fa9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f5840419b00ac8c5c85f293513971308429bb87457025125d9a26640a3222fa9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: 01_unit/compiler/aop/join_point_section_writer_v2_spec.spl
mirror: doc/06_spec/01_unit/compiler/aop/join_point_section_writer_v2_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/aop/join_point_section_writer_v2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/aop/join_point_section_writer_v2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
