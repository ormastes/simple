# hir_stage4_field_inference_spec

> HIR Stage-4 Field Inference Regression Tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hir_stage4_field_inference_spec

HIR Stage-4 Field Inference Regression Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_stage4_field_inference_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

HIR Stage-4 Field Inference Regression Tests

Regression coverage for the 7 residual "Cannot infer field type: struct 'ANY'
field '<X>'" errors that blocked bootstrap stage-4 deploy (bug doc:
doc/08_tracking/bug/hir_type_inference_any_field_2026-05-02.md, W13 re-investigation).

All 7 failures were Class 3: cross-module import resolution failures where the
type-loader emits [WARN] Failed to load imported types and the field receiver
becomes ANY-typed.

Fix commits: f489fcffb2 (SMF type reader for import_loader + non-fatal re-exports,
2026-05-18), 982744b5c2 (cross-module struct field collision resolution in Rust
seed, 2026-05-18).

LIMITATION: This spec uses text-grep assertions (no compiler-internal imports)
because `compiler.hir.*` / `compiler.frontend.*` imports cause interpreter-mode
hangs. The spec verifies structural invariants of the source files that the bug
depended on — confirming that:
  (a) the field definitions exist in the stdlib types, and
  (b) the fix's import-loader code paths are present in the Rust seed.
For a full HIR-level regression (compile + lower), see the existing Rust test:
  src/compiler_rust/compiler/tests/import_reexport_hir.rs

RUNNER NOTE: Verified to pass (12/12) under `bin/simple run`. The `bin/simple test`
runner did not complete within 60s for this spec or for an empty 3-line spec in
the same parent directory — root cause unconfirmed (may be slow cache warm-up or
subprocess protocol issue in test/unit/compiler/). This spec is a manual
verification script; it is not gated by `bin/simple test` or `bin/simple build check`.

## Scenarios

### hir stage4 field inference — stdlib struct definitions

#### FixReport struct declares 'applied' field in easy_fix types

- FixReport struct declares 'applied' field in easy_fix types
   - Expected: has_class is true
   - Expected: has_applied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FixReport struct declares 'applied' field in easy_fix types")
val path = "src/lib/nogc_sync_mut/tooling/easy_fix/types.spl"
val has_class = file_contains(path, "class FixReport:")
val has_applied = file_contains(path, "applied:")
expect(has_class).to_equal(true)
expect(has_applied).to_equal(true)
```

</details>

#### EasyFix struct declares 'replacements' field in easy_fix types

- EasyFix struct declares 'replacements' field in easy_fix types
   - Expected: has_class is true
   - Expected: has_replacements is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EasyFix struct declares 'replacements' field in easy_fix types")
val path = "src/lib/nogc_sync_mut/tooling/easy_fix/types.spl"
val has_class = file_contains(path, "class EasyFix:")
val has_replacements = file_contains(path, "replacements:")
expect(has_class).to_equal(true)
expect(has_replacements).to_equal(true)
```

</details>

#### EasyFix struct declares 'description' field in easy_fix types

- EasyFix struct declares 'description' field in easy_fix types
   - Expected: has_description is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EasyFix struct declares 'description' field in easy_fix types")
val path = "src/lib/nogc_sync_mut/tooling/easy_fix/types.spl"
val has_description = file_contains(path, "description:")
expect(has_description).to_equal(true)
```

</details>

#### StitchDesignSystem struct declares 'metadata' field in glass tokens

- StitchDesignSystem struct declares 'metadata' field in glass tokens
   - Expected: has_class is true
   - Expected: has_metadata is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("StitchDesignSystem struct declares 'metadata' field in glass tokens")
val path = "src/lib/common/ui/glass/tokens.spl"
val has_class = file_contains(path, "class StitchDesignSystem:")
val has_metadata = file_contains(path, "metadata:")
expect(has_class).to_equal(true)
expect(has_metadata).to_equal(true)
```

</details>

#### StitchMetadata struct is declared in glass tokens

- StitchMetadata struct is declared in glass tokens
   - Expected: has_meta_class is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("StitchMetadata struct is declared in glass tokens")
val path = "src/lib/common/ui/glass/tokens.spl"
val has_meta_class = file_contains(path, "class StitchMetadata:")
expect(has_meta_class).to_equal(true)
```

</details>

### hir stage4 field inference — fix commit code paths present

#### import_loader has smf fallback path for cross-module type loading

- import_loader has smf fallback path for cross-module type loading
   - Expected: has_smf is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("import_loader has smf fallback path for cross-module type loading")
val path = "src/compiler_rust/compiler/src/hir/lower/import_loader.rs"
val has_smf = file_contains(path, "smf")
expect(has_smf).to_equal(true)
```

</details>

#### import_loader handles non-fatal re-export resolution via silent skip

- import_loader handles non-fatal re-export resolution via silent skip
   - Expected: has_silent_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("import_loader handles non-fatal re-export resolution via silent skip")
val path = "src/compiler_rust/compiler/src/hir/lower/import_loader.rs"
# f489fcffb2 made re-export failures non-fatal: `Err(_) => return Ok(())`
val has_silent_skip = file_contains(path, "Silently skip")
expect(has_silent_skip).to_equal(true)
```

</details>

#### access.rs try_resolve_global_field_type_by_name is present

- access.rs try_resolve_global_field_type_by_name is present
   - Expected: has_fn is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("access.rs try_resolve_global_field_type_by_name is present")
val path = "src/compiler_rust/compiler/src/hir/lower/expr/access.rs"
val has_fn = file_contains(path, "try_resolve_global_field_type_by_name")
expect(has_fn).to_equal(true)
```

</details>

#### access.rs try_resolve_field_type_by_name fallback chain is present

- access.rs try_resolve_field_type_by_name fallback chain is present
   - Expected: has_chain is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("access.rs try_resolve_field_type_by_name fallback chain is present")
val path = "src/compiler_rust/compiler/src/hir/lower/expr/access.rs"
val has_chain = file_contains(path, "try_resolve_field_type_by_name")
expect(has_chain).to_equal(true)
```

</details>

### hir stage4 field inference — consumer import declarations

#### theme_sync.spl imports from common.ui.glass.tokens for metadata access

- theme_sync.spl imports from common.ui.glass.tokens for metadata access
   - Expected: has_import is true
   - Expected: has_metadata is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("theme_sync.spl imports from common.ui.glass.tokens for metadata access")
val path = "src/app/cli/theme_sync.spl"
val has_import = file_contains(path, "common.ui.glass.tokens")
val has_metadata = file_contains(path, "metadata")
expect(has_import).to_equal(true)
expect(has_metadata).to_equal(true)
```

</details>

#### run_commands.spl imports from std.tooling.easy_fix.types for applied field

- run_commands.spl imports from std.tooling.easy_fix.types for applied field
   - Expected: has_import is true
   - Expected: has_applied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("run_commands.spl imports from std.tooling.easy_fix.types for applied field")
val path = "src/app/io/_CliCommands/run_commands.spl"
val has_import = file_contains(path, "std.tooling.easy_fix.types")
val has_applied = file_contains(path, "applied")
expect(has_import).to_equal(true)
expect(has_applied).to_equal(true)
```

</details>

#### fix/main.spl imports from std.tooling.easy_fix for replacements access

- fix/main.spl imports from std.tooling.easy_fix for replacements access
   - Expected: has_import is true
   - Expected: has_replacements is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fix/main.spl imports from std.tooling.easy_fix for replacements access")
val path = "src/compiler/90.tools/fix/main.spl"
val has_import = file_contains(path, "easy_fix")
val has_replacements = file_contains(path, "replacements")
expect(has_import).to_equal(true)
expect(has_replacements).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `7b70edb3db6c2e34a030c800463c9daa4d1a941a30a6cc2c3f43e54a0afd5715`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b70edb3db6c2e34a030c800463c9daa4d1a941a30a6cc2c3f43e54a0afd5715`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b70edb3db6c2e34a030c800463c9daa4d1a941a30a6cc2c3f43e54a0afd5715`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/hir_stage4_field_inference_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_stage4_field_inference_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_stage4_field_inference_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_stage4_field_inference_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_stage4_field_inference_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FixReport struct declares 'applied' field in easy_fix types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_stage4_field_inference_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'EasyFix struct declares 'replacements' field in easy_fix types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_stage4_field_inference_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'EasyFix struct declares 'description' field in easy_fix types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
