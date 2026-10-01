# `resource` ownership sigils (`R` / `*R` / `@R` / `-R`) — WP-B acceptance

> `*T` in type-annotation position already parsed (probed directly per plan

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `resource` ownership sigils (`R` / `*R` / `@R` / `-R`) — WP-B acceptance

`*T` in type-annotation position already parsed (probed directly per plan

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Plan | doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md (WP-B) |
| Design | doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md §3, §7 |
| Source | `test/01_unit/compiler/resource/resource_ownership_sigil_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## What already parsed before this WP

`*T` in type-annotation position already parsed (probed directly per plan
`#0.5`), but as `TypeKind.Pointer(inner, false)` via the pre-existing raw
pointer branch in `parser_parse_type_impl` -- there was no dedicated "shared"
representation and no registry linkage. `TypeKind.Atomic` already existed as
an enum variant, but nothing in `core/parser.spl` produced it: `@` was only
consumed as `TOK_AT` in attribute/annotation position
(`parser_expr.spl`), never in type position. `-T` (weak) did not parse at
all -- `TOK_MINUS` was unhandled in `parser_parse_type_impl`.

## Why this spec feeds source STRINGS instead of writing sigils directly

Same oracle-unreachability finding as WP-A/WP-C (plan `#0.5`): `bin/simple
test` re-execs a child Rust seed whose parser reads a spec file's own
module-level syntax, so a spec file cannot itself contain `*File` / `@File`
/ `-File` type annotations as *the spec's own source* and have that prove
anything about the pure-Simple frontend. This spec drives the same
source-string harness `resource_hir_metadata_spec.spl` (WP-C) uses: past
`parse_module_body()` into `parse_and_build_module()`, which runs the actual
flat-bridge conversion under test (`_FlatAstBridge/convert_nodes.spl
convert_flat_type`).

## Why ownership recording lives in the bridge, not the parser

`resource_registry_declare` (WP-C) is only called from
`_FlatAstBridge/module_assembly.spl`'s `__resource_decl` handling, which runs
during the flat-bridge walk -- AFTER the whole file has already been parsed
into a flat AST. At raw-parse time (`core/parser.spl`'s `parser_parse_type_impl`),
no resource has been registered yet even if its `@sffi resource` decl appears
textually earlier in the same source, so a `resource_is_declared` check made
from the parser would always read false. The ownership-kind recording and the
`@R` `thread_safe:` legality gate are therefore implemented in
`convert_flat_type`, which walks decls in the same source order the bridge
already established `__resource_decl` metadata in.

## Scenarios

### resource ownership sigils: parse + registry recording

#### records 'unique' as the default ownership kind (no sigil observed)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records 'unique' as the default ownership kind (no sigil observed)
   - Expected: resource_ownership_kind("File") equals `unique`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records 'unique' as the default ownership kind (no sigil observed)")
build("@sffi(prefix: \"rt_io_file\", thread_safe: true)\nresource File\n")
expect(resource_ownership_kind("File")).to_equal("unique")
```

</details>

#### records 'shared' for the *R use-site sigil

- records 'shared' for the *R use-site sigil
   - Expected: resource_ownership_kind("File") equals `shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records 'shared' for the *R use-site sigil")
build(
    "@sffi(prefix: \"rt_io_file\")\nresource File\n" +
    "fn take(f: *File):\n    pass_do_nothing\n"
)
expect(resource_ownership_kind("File")).to_equal("shared")
assert_false(parser_has_errors())
```

</details>

#### records 'weak' for the -R use-site sigil

- records 'weak' for the -R use-site sigil
   - Expected: resource_ownership_kind("File") equals `weak`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records 'weak' for the -R use-site sigil")
build(
    "@sffi(prefix: \"rt_io_file\")\nresource File\n" +
    "fn take(f: -File):\n    pass_do_nothing\n"
)
expect(resource_ownership_kind("File")).to_equal("weak")
assert_false(parser_has_errors())
```

</details>

#### records 'atomic' for the @R use-site sigil when thread_safe: true

- records 'atomic' for the @R use-site sigil when thread_safe: true
   - Expected: resource_ownership_kind("File") equals `atomic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records 'atomic' for the @R use-site sigil when thread_safe: true")
build(
    "@sffi(prefix: \"rt_io_file\", thread_safe: true)\nresource File\n" +
    "fn take(f: @File):\n    pass_do_nothing\n"
)
expect(resource_ownership_kind("File")).to_equal("atomic")
assert_false(parser_has_errors())
```

</details>

#### rejects @R on a resource that is not declared thread_safe: true (clean diagnostic, not silent accept)

- rejects @R on a resource that is not declared thread_safe: true (clean diagnostic, not silent accept)
   - Expected: resource_ownership_kind("File") equals `unique`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects @R on a resource that is not declared thread_safe: true (clean diagnostic, not silent accept)")
val errors = build_errors(
    "@sffi(prefix: \"rt_io_file\", thread_safe: false)\nresource File\n" +
    "fn take(f: @File):\n    pass_do_nothing\n"
)
assert_true(parser_has_errors())
var found_thread_safe_error = false
var i = 0
while i < errors.len():
    if errors[i].contains("thread_safe"):
        found_thread_safe_error = true
    i = i + 1
assert_true(found_thread_safe_error)
# The illegal sigil must NOT be silently recorded as legal.
expect(resource_ownership_kind("File")).to_equal("unique")
```

</details>

#### rejects @R on a resource with no thread_safe: metadata at all (absent defaults to unsafe)

- rejects @R on a resource with no thread_safe: metadata at all (absent defaults to unsafe)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects @R on a resource with no thread_safe: metadata at all (absent defaults to unsafe)")
val errors = build_errors(
    "@sffi(prefix: \"rt_io_file\")\nresource File\n" +
    "fn take(f: @File):\n    pass_do_nothing\n"
)
assert_true(parser_has_errors())
assert_true(errors.len() > 0)
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


## Related Documentation

- **Plan:** `doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md (WP-B)`
- **Design:** `doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md §3, §7`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8b4e9afbdea92c001feafeb198bb323c94834afebe3296291e4691f45e5bfd80`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b4e9afbdea92c001feafeb198bb323c94834afebe3296291e4691f45e5bfd80`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b4e9afbdea92c001feafeb198bb323c94834afebe3296291e4691f45e5bfd80`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/resource/resource_ownership_sigil_spec.spl
mirror: doc/06_spec/01_unit/compiler/resource/resource_ownership_sigil_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/resource/resource_ownership_sigil_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/resource/resource_ownership_sigil_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/resource/resource_ownership_sigil_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records 'unique' as the default ownership kind (no sigil observed)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_ownership_sigil_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records 'shared' for the *R use-site sigil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_ownership_sigil_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records 'weak' for the -R use-site sigil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
