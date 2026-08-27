# `resource` HIR metadata propagation — WP-C acceptance

> Per architecture §3/§7, ownership strategy is selected by per-resource

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `resource` HIR metadata propagation — WP-C acceptance

Per architecture §3/§7, ownership strategy is selected by per-resource

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Plan | doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md (WP-C) |
| Design | doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md §1 |
| Source | `test/01_unit/compiler/resource/resource_hir_metadata_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Why `resource_is_move_only` has no separate storage

Per architecture §3/§7, ownership strategy is selected by per-resource
`@sffi` metadata (`sharing:`, retain/release presence) plus the use-site
sigil (`R`/`*R`/`@R`) — NOT by a global type-table flag, and NOT by the
defining tier. Every declared `resource` is affine/move-only by definition
until a later WP's use-site sigil relaxes it (WP-B parses the sigils, WP-G
enforces), so `resource_is_move_only(name)` is currently exactly
`resource_is_declared(name)` — there is nothing else to store yet.

## Scenarios

### resource HIR metadata: registry propagation

#### records a declared resource name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records a declared resource name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records a declared resource name")
build("@sffi(prefix: \"rt_io_file\")\nresource File\n")
assert_true(resource_is_declared("File"))
```

</details>

#### does not record an undeclared name

- does not record an undeclared name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not record an undeclared name")
build("@sffi(prefix: \"rt_io_file\")\nresource File\n")
assert_false(resource_is_declared("NotAResource"))
```

</details>

#### round-trips every documented @sffi key

- round-trips every documented @sffi key
   - Expected: resource_meta_prefix("Image") equals `rt_image`
   - Expected: resource_meta_handle("Image") equals `i64`
   - Expected: resource_meta_invalid("Image") equals `0`
   - Expected: resource_meta_retain("Image") equals `rt_image_ref`
   - Expected: resource_meta_release("Image") equals `rt_image_unref`
   - Expected: resource_meta_sharing("Image") equals `foreign`
   - Expected: resource_meta_thread_safe("Image") equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every documented @sffi key")
build(
    "@sffi(prefix: \"rt_image\", handle: i64, invalid: 0, retain: rt_image_ref, release: rt_image_unref, sharing: foreign, thread_safe: false)\n" +
    "resource Image\n"
)
expect(resource_meta_prefix("Image")).to_equal("rt_image")
expect(resource_meta_handle("Image")).to_equal("i64")
expect(resource_meta_invalid("Image")).to_equal("0")
expect(resource_meta_retain("Image")).to_equal("rt_image_ref")
expect(resource_meta_release("Image")).to_equal("rt_image_unref")
expect(resource_meta_sharing("Image")).to_equal("foreign")
expect(resource_meta_thread_safe("Image")).to_equal("false")
```

</details>

#### preserves the sign on a negative `invalid` sentinel

- preserves the sign on a negative `invalid` sentinel
   - Expected: resource_meta_invalid("File") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves the sign on a negative `invalid` sentinel")
# `invalid: -1` lexes as TWO tokens (minus, then int) — a lowering
# that only handles single tokens silently drops the sign and
# records "1" instead of "-1".
build("@sffi(prefix: \"rt_io_file\", invalid: -1)\nresource File\n")
expect(resource_meta_invalid("File")).to_equal("-1")
```

</details>

#### keeps two resources in the same source independently queryable

- keeps two resources in the same source independently queryable
   - Expected: resource_meta_sharing("CudaPrimaryContext") equals `foreign`
   - Expected: resource_meta_invalid("File2") equals `-1`
   - Expected: resource_meta_sharing("File2") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps two resources in the same source independently queryable")
build(
    "@sffi(prefix: \"rt_cuda_primary_ctx\", sharing: foreign)\nresource CudaPrimaryContext\n" +
    "@sffi(prefix: \"rt_io_file\", invalid: -1)\nresource File2\n"
)
expect(resource_meta_sharing("CudaPrimaryContext")).to_equal("foreign")
expect(resource_meta_invalid("File2")).to_equal("-1")
# No cross-contamination: File2 declared no `sharing:`.
expect(resource_meta_sharing("File2")).to_equal("")
```

</details>

#### resets the registry on a fresh parse, not accumulates across calls

- resets the registry on a fresh parse, not accumulates across calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets the registry on a fresh parse, not accumulates across calls")
build("@sffi(prefix: \"rt_a\")\nresource A\n")
assert_true(resource_is_declared("A"))
# A second, unrelated parse in the same process must not still see
# the first parse's resource — parser_init_with_path resets the
# registry exactly like it resets the AST arena.
build("val x = 1\n")
assert_false(resource_is_declared("A"))
```

</details>

### resource HIR metadata: affine/move-only marking

#### marks a declared resource as move-only

- marks a declared resource as move-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks a declared resource as move-only")
build("@sffi(prefix: \"rt_io_file\")\nresource File\n")
assert_true(resource_is_move_only("File"))
```

</details>

#### does not mark an ordinary (non-resource) name as move-only

- does not mark an ordinary (non-resource) name as move-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not mark an ordinary (non-resource) name as move-only")
build("@sffi(prefix: \"rt_io_file\")\nresource File\n")
assert_false(resource_is_move_only("PlainStruct"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md (WP-C)`
- **Design:** `doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md §1`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7aedf0c71a12047e22008b635cb31df53f76f786eacfc97118bc0b4a52232407`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7aedf0c71a12047e22008b635cb31df53f76f786eacfc97118bc0b4a52232407`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7aedf0c71a12047e22008b635cb31df53f76f786eacfc97118bc0b4a52232407`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/resource/resource_hir_metadata_spec.spl
mirror: doc/06_spec/01_unit/compiler/resource/resource_hir_metadata_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/resource/resource_hir_metadata_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/resource/resource_hir_metadata_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/resource/resource_hir_metadata_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records a declared resource name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_hir_metadata_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not record an undeclared name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_hir_metadata_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips every documented @sffi key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
