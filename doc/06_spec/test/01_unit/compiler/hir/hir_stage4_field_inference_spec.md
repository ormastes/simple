# hir_stage4_field_inference_spec

> HIR Stage-4 Field Inference Regression Tests

<!-- sdn-diagram:id=hir_stage4_field_inference_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hir_stage4_field_inference_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hir_stage4_field_inference_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hir_stage4_field_inference_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/lib/nogc_sync_mut/src/tooling/easy_fix/types.spl"
val has_class = file_contains(path, "class FixReport:")
val has_applied = file_contains(path, "applied:")
expect(has_class).to_equal(true)
expect(has_applied).to_equal(true)
```

</details>

#### EasyFix struct declares 'replacements' field in easy_fix types

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/lib/nogc_sync_mut/src/tooling/easy_fix/types.spl"
val has_class = file_contains(path, "class EasyFix:")
val has_replacements = file_contains(path, "replacements:")
expect(has_class).to_equal(true)
expect(has_replacements).to_equal(true)
```

</details>

#### EasyFix struct declares 'description' field in easy_fix types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/lib/nogc_sync_mut/src/tooling/easy_fix/types.spl"
val has_description = file_contains(path, "description:")
expect(has_description).to_equal(true)
```

</details>

#### StitchDesignSystem struct declares 'metadata' field in glass tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/lib/common/ui/glass/tokens.spl"
val has_class = file_contains(path, "class StitchDesignSystem:")
val has_metadata = file_contains(path, "metadata:")
expect(has_class).to_equal(true)
expect(has_metadata).to_equal(true)
```

</details>

#### StitchMetadata struct is declared in glass tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/lib/common/ui/glass/tokens.spl"
val has_meta_class = file_contains(path, "class StitchMetadata:")
expect(has_meta_class).to_equal(true)
```

</details>

### hir stage4 field inference — fix commit code paths present

#### import_loader has smf fallback path for cross-module type loading

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/compiler_rust/compiler/src/hir/lower/import_loader.rs"
val has_smf = file_contains(path, "smf")
expect(has_smf).to_equal(true)
```

</details>

#### import_loader handles non-fatal re-export resolution via silent skip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/compiler_rust/compiler/src/hir/lower/import_loader.rs"
# f489fcffb2 made re-export failures non-fatal: `Err(_) => return Ok(())`
val has_silent_skip = file_contains(path, "Silently skip")
expect(has_silent_skip).to_equal(true)
```

</details>

#### access.rs try_resolve_global_field_type_by_name is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/compiler_rust/compiler/src/hir/lower/expr/access.rs"
val has_fn = file_contains(path, "try_resolve_global_field_type_by_name")
expect(has_fn).to_equal(true)
```

</details>

#### access.rs try_resolve_field_type_by_name fallback chain is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/compiler_rust/compiler/src/hir/lower/expr/access.rs"
val has_chain = file_contains(path, "try_resolve_field_type_by_name")
expect(has_chain).to_equal(true)
```

</details>

### hir stage4 field inference — consumer import declarations

#### theme_sync.spl imports from common.ui.glass.tokens for metadata access

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/cli/theme_sync.spl"
val has_import = file_contains(path, "common.ui.glass.tokens")
val has_metadata = file_contains(path, "metadata")
expect(has_import).to_equal(true)
expect(has_metadata).to_equal(true)
```

</details>

#### cli_commands_part1.spl imports from std.tooling.easy_fix.types for applied field

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/io/cli_commands_part1.spl"
val has_import = file_contains(path, "std.tooling.easy_fix.types")
val has_applied = file_contains(path, "applied")
expect(has_import).to_equal(true)
expect(has_applied).to_equal(true)
```

</details>

#### fix/main.spl imports from std.tooling.easy_fix for replacements access

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
