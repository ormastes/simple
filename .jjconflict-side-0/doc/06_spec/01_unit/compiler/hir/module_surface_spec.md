# module_surface_spec

> Purpose: Prove that module surfaces.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# module_surface_spec

Purpose: Prove that module surfaces.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/module_surface_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that module surfaces.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### module surfaces

#### retains canonical and compiler aliases as scalar names on one physical surface

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- retains canonical and compiler aliases as scalar names on one physical surface
- Verify: retains canonical and compiler aliases as scalar names on one physical surface
   - Expected: builder.add_parsed(module, canonical, 0).is_ok() is true
   - Expected: builder.add_alias(compiler_core_alias).is_ok() is true
   - Expected: builder.resolve_export_origins().is_ok() is true
   - Expected: result.is_ok() is true
   - Expected: surfaces.surfaces.len() equals `1`
   - Expected: surfaces.index_by_name["compiler.frontend.core.shared"] equals `0`
   - Expected: surfaces.index_by_name["compiler.core.shared"] equals `0`
   - Expected: surfaces.ordered_indices equals `[0, 0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("retains canonical and compiler aliases as scalar names on one physical surface")
step("Verify: retains canonical and compiler aliases as scalar names on one physical surface")
# @req: REQ-COMPILER-HIR-001
val body = "pub fn shared_tick() -> i64:\n    1\n"
val module = parse_and_build_module(body, "src/compiler/10.frontend/core/shared.spl")
val canonical = SourceFile(
    path: "src/compiler/10.frontend/core/shared.spl",
    content: body,
    module_name: "compiler.frontend.core.shared")
val compiler_core_alias = SourceFile(
    path: "src/compiler/10.frontend/core/shared.spl",
    content: body,
    module_name: "compiler.core.shared")
var builder = ModuleSurfaceBuilder.new()
expect(builder.add_parsed(module, canonical, 0).is_ok()).to_equal(true)
expect(builder.add_alias(compiler_core_alias).is_ok()).to_equal(true)
expect(builder.resolve_export_origins().is_ok()).to_equal(true)
val result = builder.finish()
expect(result.is_ok()).to_equal(true)
val surfaces = result.unwrap()
expect(surfaces.surfaces.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(surfaces.index_by_name["compiler.frontend.core.shared"]).to_equal(0)
expect(surfaces.index_by_name["compiler.core.shared"]).to_equal(0)
expect(surfaces.ordered_indices).to_equal([0, 0])
```

</details>

#### keeps a second physical source alias at index one

- keeps a second physical source alias at index one
- Verify: keeps a second physical source alias at index one
   - Expected: result.is_ok() is true
   - Expected: surfaces.surfaces.len() equals `2`
   - Expected: surfaces.index_by_name["second_alias"] equals `1`
   - Expected: surfaces.ordered_names equals `["first", "second", "second_alias"]`
   - Expected: surfaces.ordered_indices equals `[0, 1, 1]`
   - Expected: surfaces.surfaces[surfaces.ordered_indices[0]].source_index equals `0`
   - Expected: surfaces.surfaces[surfaces.ordered_indices[1]].source_index equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a second physical source alias at index one")
step("Verify: keeps a second physical source alias at index one")
val first = parse_and_build_module("fn first() -> i64:\n    1\n", "first.spl")
val second = parse_and_build_module("fn second() -> i64:\n    2\n", "second.spl")
val modules = {
    "first": first,
    "second": second,
    "second_alias": second
}
val sources = [
    SourceFile(path: "first.spl", content: "fn first() -> i64:\n    1\n", module_name: "first"),
    SourceFile(path: "second.spl", content: "fn second() -> i64:\n    2\n", module_name: "second")
]

val result = module_surfaces_from_modules(modules, sources)
expect(result.is_ok()).to_equal(true)
val surfaces = result.unwrap()
expect(surfaces.surfaces.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(surfaces.index_by_name["second_alias"]).to_equal(1)
expect(surfaces.ordered_names).to_equal(["first", "second", "second_alias"])
expect(surfaces.ordered_indices).to_equal([0, 1, 1])
expect(surfaces.surfaces[surfaces.ordered_indices[0]].source_index).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(surfaces.surfaces[surfaces.ordered_indices[1]].source_index).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### collapses repository symlink spellings to one physical surface

- collapses repository symlink spellings to one physical surface
- Verify: collapses repository symlink spellings to one physical surface
   - Expected: result.is_ok() is true
   - Expected: surfaces.surfaces.len() equals `1`
   - Expected: surfaces.index_by_name["lib_alias"] equals `0`
   - Expected: surfaces.index_by_name["std_alias"] equals `0`
   - Expected: surfaces.ordered_names equals `["lib_alias", "std_alias"]`
   - Expected: surfaces.ordered_indices equals `[0, 0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collapses repository symlink spellings to one physical surface")
step("Verify: collapses repository symlink spellings to one physical surface")
val body = "fn shared() -> i64:\n    1\n"
val module = parse_and_build_module(body, "shared.spl")
val modules = {"lib_alias": module, "std_alias": module}
val sources = [
    SourceFile(path: "src/lib/nogc_async_mut/io.spl", content: body, module_name: "lib_alias"),
    SourceFile(path: "src/std/nogc_async_mut/io.spl", content: body, module_name: "std_alias")
]

val result = module_surfaces_from_modules(modules, sources)
expect(result.is_ok()).to_equal(true)
val surfaces = result.unwrap()
expect(surfaces.surfaces.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(surfaces.index_by_name["lib_alias"]).to_equal(0)
expect(surfaces.index_by_name["std_alias"]).to_equal(0)
expect(surfaces.ordered_names).to_equal(["lib_alias", "std_alias"])
expect(surfaces.ordered_indices).to_equal([0, 0])
```

</details>

#### coalesces physical aliases before resolving one plain facade owner

- coalesces physical aliases before resolving one plain facade owner
- Verify: coalesces physical aliases before resolving one plain facade owner
   - Expected: result.is_ok() is true
   - Expected: surfaces.surfaces.len() equals `2`
   - Expected: surfaces.index_by_name["pkg.lib_owner"] equals `surfaces.index_by_name["pkg.std_owner"]`
   - Expected: facade_surface.export_origins["shared_tick"].owner_module equals `pkg.lib_owner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("coalesces physical aliases before resolving one plain facade owner")
step("Verify: coalesces physical aliases before resolving one plain facade owner")
val body = "pub fn shared_tick() -> i64:\n    1\n"
val provider = parse_and_build_module(body, "src/lib/nogc_async_mut/io.spl")
val facade_body = "export shared_tick\n"
val facade = parse_and_build_module(facade_body, "pkg/__init__.spl")
val modules = {
    "pkg.lib_owner": provider,
    "pkg.std_owner": provider,
    "pkg.__init__": facade
}
val sources = [
    SourceFile(path: "src/lib/nogc_async_mut/io.spl", content: body, module_name: "pkg.lib_owner"),
    SourceFile(path: "src/std/nogc_async_mut/io.spl", content: body, module_name: "pkg.std_owner"),
    SourceFile(path: "pkg/__init__.spl", content: facade_body, module_name: "pkg.__init__")
]

val result = module_surfaces_from_modules(modules, sources)
expect(result.is_ok()).to_equal(true)
val surfaces = result.unwrap()
expect(surfaces.surfaces.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(surfaces.index_by_name["pkg.lib_owner"]).to_equal(surfaces.index_by_name["pkg.std_owner"])
val facade_surface = surfaces.surfaces[surfaces.index_by_name["pkg.__init__"]]
expect(facade_surface.export_origins["shared_tick"].owner_module).to_equal("pkg.lib_owner")
```

</details>

#### resolves aliases by physical source identity before declaration shape

- resolves aliases by physical source identity before declaration shape
- Verify: resolves aliases by physical source identity before declaration shape
   - Expected: first.name equals `first.spl`
   - Expected: result.is_ok() is true
   - Expected: surfaces.surfaces.len() equals `2`
   - Expected: surfaces.index_by_name["first_alias"] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves aliases by physical source identity before declaration shape")
step("Verify: resolves aliases by physical source identity before declaration shape")
val first_body = "fn shared() -> i64:\n    1\n"
val second_body = "fn shared() -> i64:\n    2\n"
val first = parse_and_build_module(first_body, "first.spl")
val second = parse_and_build_module(second_body, "second.spl")
expect(first.name).to_equal("first.spl")
val modules = {
    "first": first,
    "second": second,
    "first_alias": first
}
val sources = [
    SourceFile(path: "first.spl", content: first_body, module_name: "first"),
    SourceFile(path: "second.spl", content: second_body, module_name: "second")
]

val result = module_surfaces_from_modules(modules, sources)
expect(result.is_ok()).to_equal(true)
val surfaces = result.unwrap()
expect(surfaces.surfaces.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(surfaces.index_by_name["first_alias"]).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-HIR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eac0343abc0fd5d1166c5c6e4a3521c764d0c93597032bdd5cd5e2f5bad52991`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eac0343abc0fd5d1166c5c6e4a3521c764d0c93597032bdd5cd5e2f5bad52991`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eac0343abc0fd5d1166c5c6e4a3521c764d0c93597032bdd5cd5e2f5bad52991`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/module_surface_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/module_surface_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/module_surface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/module_surface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/module_surface_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/module_surface_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains canonical and compiler aliases as scalar names on one physical surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/module_surface_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a second physical source alias at index one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/module_surface_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collapses repository symlink spellings to one physical surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
