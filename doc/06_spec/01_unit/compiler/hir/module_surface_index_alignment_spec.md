# Module Surface Index Alignment Specification

> Tests covering module surface aligned scalar index.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Surface Index Alignment Specification

## Scenarios

### module surface aligned scalar index

#### preserves discovery order and deduplicates a same-target alias

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves discovery order and deduplicates a same-target alias
   - Expected: builder.add_indexed_name("first", 0).is_ok() is true
   - Expected: builder.add_indexed_name("second", 1).is_ok() is true
   - Expected: builder.add_indexed_name("second_alias", 1).is_ok() is true
   - Expected: builder.add_indexed_name("second_alias", 1).is_ok() is true
   - Expected: finish_error equals ``
   - Expected: surfaces.frozen is true
   - Expected: surfaces.ordered_names equals `["first", "second", "second_alias"]`
   - Expected: surfaces.ordered_indices equals `[0, 1, 1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves discovery order and deduplicates a same-target alias")
var builder = ModuleSurfaceBuilder.new()
expect(builder.add_indexed_name("first", 0).is_ok()).to_equal(true)
expect(builder.add_indexed_name("second", 1).is_ok()).to_equal(true)
expect(builder.add_indexed_name("second_alias", 1).is_ok()).to_equal(true)
expect(builder.add_indexed_name("second_alias", 1).is_ok()).to_equal(true)
builder.surfaces = [ModuleSurface.empty("first"), ModuleSurface.empty("second")]
val surfaces = ModuleSurfacesByName(
    surfaces: [], index_by_name: {},
    ordered_names: [], ordered_indices: [], generation: 0, frozen: false)
val finish_error = builder.finish_into(surfaces)
expect(finish_error).to_equal("")
expect(surfaces.frozen).to_equal(true)
expect(surfaces.ordered_names).to_equal(["first", "second", "second_alias"])
expect(surfaces.ordered_indices).to_equal([0, 1, 1])
```

</details>

#### rejects a second finish without replacing its destination

- rejects a second finish without replacing its destination
   - Expected: builder.add_indexed_name("new", 0).is_ok() is true
   - Expected: builder.finish_into(first_destination) equals ``
   - Expected: destination.ordered_names equals `["existing"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a second finish without replacing its destination")
var builder = ModuleSurfaceBuilder.new()
expect(builder.add_indexed_name("new", 0).is_ok()).to_equal(true)
builder.surfaces = [ModuleSurface.empty("new")]
val first_destination = ModuleSurfacesByName(
    surfaces: [], index_by_name: {},
    ordered_names: [], ordered_indices: [], generation: 0, frozen: false)
expect(builder.finish_into(first_destination)).to_equal("")
val destination = ModuleSurfacesByName(
    surfaces: [], index_by_name: {},
    ordered_names: [], ordered_indices: [], generation: 0, frozen: false)
destination.ordered_names = ["existing"]
val finish_error = builder.finish_into(destination)
expect(finish_error).to_contain("builder is frozen")
expect(destination.ordered_names).to_equal(["existing"])
```

</details>

#### retains exact names aliases and misses after registry scope teardown

- retains exact names aliases and misses after registry scope teardown
   - Expected: began is true
   - Expected: first_added is true
   - Expected: alias_added is true
   - Expected: origin_added is true
   - Expected: finish_error equals ``
   - Expected: paused is true
   - Expected: promoted is true
   - Expected: ended is true
   - Expected: module_surfaces_retained_alignment(registry) is true
   - Expected: module_surface_registry_index(registry, "first") equals `0`
   - Expected: module_surface_registry_index(registry, "first_alias") equals `0`
   - Expected: module_surface_registry_index(registry, "missing") equals `-1`
   - Expected: retained_hit.found is true
   - Expected: retained_hit.owner_module equals `provider`
   - Expected: retained_hit.source_name equals `source_answer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("retains exact names aliases and misses after registry scope teardown")
val began = rt_transient_array_scope_begin()
var builder = ModuleSurfaceBuilder.new()
val first_added = builder.add_indexed_name("first", 0).is_ok()
val alias_added = builder.add_indexed_name("first_alias", 0).is_ok()
val surface = ModuleSurface.empty("first")
val origin_index = surface.export_origin_index
val origin_added = module_surface_export_origin_index_put(
    origin_index, "answer", "provider", "source_answer", "explicit").is_ok()
builder.surfaces = [surface]
val registry = ModuleSurfacesByName(
    surfaces: [], index_by_name: {},
    ordered_names: [], ordered_indices: [], generation: 0, frozen: false)
val finish_error = builder.finish_into(registry)
val paused = rt_transient_array_scope_pause()
val promoted = if paused: module_surfaces_promote(registry) else: false
val ended = rt_transient_array_scope_end()
expect(began).to_equal(true)
expect(first_added).to_equal(true)
expect(alias_added).to_equal(true)
expect(origin_added).to_equal(true)
expect(finish_error).to_equal("")
expect(paused).to_equal(true)
expect(promoted).to_equal(true)
expect(ended).to_equal(true)
expect(module_surfaces_retained_alignment(registry)).to_equal(true)
expect(module_surface_registry_index(registry, "first")).to_equal(0)
expect(module_surface_registry_index(registry, "first_alias")).to_equal(0)
expect(module_surface_registry_index(registry, "missing")).to_equal(-1)
val retained_origin_index = registry.surfaces[0].export_origin_index
val retained_hit = module_surface_export_origin_index_lookup(
    retained_origin_index, "answer")
expect(retained_hit.found).to_equal(true)
expect(retained_hit.owner_module).to_equal("provider")
expect(retained_hit.source_name).to_equal("source_answer")
expect(module_surface_export_origin_index_lookup(
    retained_origin_index, "missing").found).to_equal(false)
```

</details>

#### rejects an alias that changes its existing target

- rejects an alias that changes its existing target
   - Expected: builder.add_indexed_name("alias", 0).is_ok() is true
   - Expected: builder.add_indexed_name("alias", 1).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects an alias that changes its existing target")
var builder = ModuleSurfaceBuilder.new()
expect(builder.add_indexed_name("alias", 0).is_ok()).to_equal(true)
expect(builder.add_indexed_name("alias", 1).is_err()).to_equal(true)
```

</details>

#### fails closed for misaligned constructor data and preserves misses

- fails closed for misaligned constructor data and preserves misses
   - Expected: mismatch.is_err() is true
   - Expected: negative.is_err() is true
   - Expected: out_of_range.is_err() is true
   - Expected: conflicting.is_err() is true
   - Expected: module_surface_index_by_name({"owner": 0}, "missing") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails closed for misaligned constructor data and preserves misses")
val mismatch = module_surfaces_by_name_from_parts(
    [ModuleSurface.empty("owner")], {"owner": 0}, ["owner"], [])
expect(mismatch.is_err()).to_equal(true)
val negative = module_surfaces_by_name_from_parts(
    [ModuleSurface.empty("owner")], {"owner": 0}, ["owner"], [-1])
expect(negative.is_err()).to_equal(true)
val out_of_range = module_surfaces_by_name_from_parts(
    [ModuleSurface.empty("owner")], {"owner": 1}, ["owner"], [1])
expect(out_of_range.is_err()).to_equal(true)
val conflicting = module_surfaces_by_name_from_parts(
    [ModuleSurface.empty("owner")], {"owner": 1}, ["owner"], [0])
expect(conflicting.is_err()).to_equal(true)
expect(module_surface_index_by_name({"owner": 0}, "missing")).to_equal(-1)
```

</details>

#### uses an explicit index receiver for native-safe origin writes and reads

- uses an explicit index receiver for native-safe origin writes and reads
   - Expected: write.is_ok() is true
   - Expected: hit.found is true
   - Expected: hit.owner_module equals `provider`
   - Expected: hit.source_name equals `answer`
   - Expected: miss.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses an explicit index receiver for native-safe origin writes and reads")
val index = module_surface_export_origin_index_empty()
val write = module_surface_export_origin_index_put(
    index, "answer", "provider", "answer", "explicit")
expect(write.is_ok()).to_equal(true)
val hit = module_surface_export_origin_index_lookup(index, "answer")
expect(hit.found).to_equal(true)
expect(hit.owner_module).to_equal("provider")
expect(hit.source_name).to_equal("answer")
val miss = module_surface_export_origin_index_lookup(index, "missing")
expect(miss.found).to_equal(false)
val malformed = ModuleSurfaceExportOriginIndex(
    origins: {}, index_by_name: {"answer": 0}, frozen: true,
    names: ["answer"], owner_modules: [], source_names: ["answer"],
    resolution_kinds: ["explicit"])
expect(module_surface_export_origin_index_lookup(
    malformed, "answer").found).to_equal(false)
```

</details>

#### reads frozen origins from scalar rows when compatibility dicts are unavailable

- reads frozen origins from scalar rows when compatibility dicts are unavailable
   - Expected: hit.found is true
   - Expected: hit.owner_module equals `compiler.common.diagnostics.span`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads frozen origins from scalar rows when compatibility dicts are unavailable")
val index = module_surface_export_origin_index_empty()
expect(module_surface_export_origin_index_put(
    index, "Span", "compiler.common.diagnostics.span", "Span",
    "explicit").is_ok()).to_equal(true)
index.origins = {}
index.index_by_name = {}
val hit = module_surface_export_origin_index_lookup(index, "Span")
expect(hit.found).to_equal(true)
expect(hit.owner_module).to_equal("compiler.common.diagnostics.span")
```

</details>

#### validates scalar routes independently from signature projections

- validates scalar routes independently from signature projections
   - Expected: module_surface_route_arrays_aligned(surface) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates scalar routes independently from signature projections")
val surface = ModuleSurface.empty("consumer")
surface.signature_names = ["broken"]
expect(module_surface_route_arrays_aligned(surface)).to_equal(true)
```

</details>

#### declares the canonical Span owner used by surface records

- declares the canonical Span owner used by surface records


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares the canonical Span owner used by surface records")
val source = file_read(
    "src/compiler/20.hir/hir_lowering/module_surface_types.spl")
expect(source).to_contain(
    "use compiler.common.diagnostics.span.")
```

</details>

#### declares canonical owners for staged signature dependencies

- declares canonical owners for staged signature dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares canonical owners for staged signature dependencies")
expect(file_read(
    "src/compiler/15.blocks/blocks/value.spl")).to_contain(
    "use compiler.common.diagnostics.span.")
expect(file_read(
    "src/compiler/25.traits/trait_validation.spl")).to_contain(
    "use compiler.common.diagnostics.span.")
expect(file_read(
    "src/compiler/30.types/type_infer_types.spl")).to_contain(
    "use compiler.common.diagnostics.span.")
expect(file_read(
    "src/compiler/10.frontend/treesitter_types.spl")).to_contain(
    "use compiler.common.diagnostics.span.")
expect(file_read(
    "src/compiler/80.driver/driver_bootstrap.spl")).to_contain(
    "use compiler.backend.backend.backend_types.")
expect(file_read(
    "src/compiler/80.driver/driver_compiler_type.spl")).to_contain(
    "use compiler.common.diagnostics.span.")
expect(file_read(
    "src/lib/nogc_sync_mut/io/process_ops.spl")).to_contain(
    "use std.nogc_sync_mut.io_runtime.")
```

</details>

#### keeps exported backend signatures on canonical type names

- keeps exported backend signatures on canonical type names
   - Expected: source does not contain `CodegenBarrierScope`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps exported backend signatures on canonical type names")
val source = file_read(
    "src/compiler/70.backend/backend/vulkan_backend.spl")
expect(source).to_contain(
    "fn compile_barrier(scope: GpuBarrierScope)")
expect(source.contains("CodegenBarrierScope")).to_equal(false)
expect(file_read(
    "src/compiler/70.backend/backend/gpu_codegen_types.spl")).to_contain(
    "export use compiler.mir.mir_instructions.{GpuBarrierScope, GpuAtomicOpKind}")
expect(file_read(
    "src/compiler/70.backend/backend/common/gpu_codegen.spl")).to_contain(
    "export use compiler.mir.mir_instructions.{GpuBarrierScope, GpuAtomicOpKind}")
```

</details>

#### does not allocate array capacity during repeated scalar lookup

- does not allocate array capacity during repeated scalar lookup
   - Expected: module_surface_index_by_name(name_index, "owner") equals `0`
   - Expected: after equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not allocate array capacity during repeated scalar lookup")
val name_index = {"owner": 0}
val before = rt_heap_array_capacity_bytes()
var iteration = 0
while iteration < 1000:
    expect(module_surface_index_by_name(name_index, "owner")).to_equal(0)
    iteration = iteration + 1
val after = rt_heap_array_capacity_bytes()
expect(after).to_equal(before)
```

</details>

#### resolves exact source identity without fallback allocation

- resolves exact source identity without fallback allocation
   - Expected: registry_result.is_ok() is true
   - Expected: registry != nil is true
   - Expected: module_surface_index_for_source(registry, source, 7) equals `0`
   - Expected: module_surface_index_for_source(registry, wrong_content, 7) equals `-1`
   - Expected: module_surface_index_for_source(registry, source, 8) equals `-1`
   - Expected: module_surface_index_for_source(registry, unknown_alias, 7) equals `-1`
   - Expected: after equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves exact source identity without fallback allocation")
val source = SourceFile(
    path: "identity/owner.spl", content: "fn answer(): 42",
    module_name: "identity.owner")
var surface = ModuleSurface.empty("identity.owner")
surface.source_index = 7
val absolute_path = rt_path_absolute(source.path)
surface.canonical_path = (
    if absolute_path != "": absolute_path else: source.path).replace("\\", "/")
surface.module_name = source.module_name
surface.content_length = source.content.len()
surface.content_hash = rt_hash_text(source.content)
val registry_result = module_surfaces_by_name_from_parts(
    [surface], {"identity.owner": 0}, ["identity.owner"], [0])
expect(registry_result.is_ok()).to_equal(true)
if registry_result.is_ok():
    val registry = registry_result.unwrap()
    expect(registry != nil).to_equal(true)
    val before = rt_heap_array_capacity_bytes()
    expect(module_surface_index_for_source(registry, source, 7)).to_equal(0)
    val wrong_content = SourceFile(
        path: source.path, content: "fn answer(): 43",
        module_name: source.module_name)
    expect(module_surface_index_for_source(registry, wrong_content, 7)).to_equal(-1)
    expect(module_surface_index_for_source(registry, source, 8)).to_equal(-1)
    val unknown_alias = SourceFile(
        path: source.path, content: source.content,
        module_name: "identity.alias")
    expect(module_surface_index_for_source(registry, unknown_alias, 7)).to_equal(-1)
    val after = rt_heap_array_capacity_bytes()
    expect(after).to_equal(before)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/module_surface_index_alignment_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering module surface aligned scalar index.
- module surface aligned scalar index

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5d1591d04dbb34b33ef0524d6bc84903068fcb0e0be896da6426d98747773237`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d1591d04dbb34b33ef0524d6bc84903068fcb0e0be896da6426d98747773237`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d1591d04dbb34b33ef0524d6bc84903068fcb0e0be896da6426d98747773237`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/hir/module_surface_index_alignment_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/module_surface_index_alignment_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/hir/module_surface_index_alignment_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/module_surface_index_alignment_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/module_surface_index_alignment_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/hir/module_surface_index_alignment_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/module_surface_index_alignment_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves discovery order and deduplicates a same-target alias' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/module_surface_index_alignment_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a second finish without replacing its destination' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/module_surface_index_alignment_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains exact names aliases and misses after registry scope teardown' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
