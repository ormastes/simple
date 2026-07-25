# Smf Runtime Specification

> <details>

<!-- sdn-diagram:id=smf_runtime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_runtime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_runtime_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_runtime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Runtime Specification

## Scenarios

### SmfHeader

#### test_header_create

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = SmfHeader.create(2, 5, 0)
expect(h.version).to_equal(2)
expect(h.section_count).to_equal(5)
```

</details>

#### test_header_trailer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = SmfHeader.create(1, 3, 128)
expect(h.has_trailer()).to_equal(true)
```

</details>

#### test_header_validate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = SmfHeader.create(1, 3, 0).validate()
expect(h.is_valid).to_equal(true)
```

</details>

#### test_header_empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = SmfHeader.empty()
expect(h.version).to_equal(0)
expect(h.is_valid == false).to_equal(true)
```

</details>

### TrailerDetection

#### test_detect_trailer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TrailerDetection.trailer(256)
expect(td.confidence).to_equal(100)
```

</details>

#### test_detect_not_found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val td = TrailerDetection.not_found()
expect(td.detection_mode).to_equal("none")
```

</details>

### GenerationState

#### test_gen_loaded

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gs = GenerationState.loaded("mymod", 1)
expect(gs.state).to_equal("loaded")
```

</details>

#### test_gen_candidate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gs = GenerationState.candidate("mymod", 2)
expect(gs.state).to_equal("candidate")
```

</details>

#### test_gen_promote

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gs = GenerationState.candidate("mymod", 2).promote()
expect(gs.state).to_equal("active")
```

</details>

### CandidateMapping

#### test_candidate_not_ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cm = CandidateMapping.create("ref_abc")
expect(cm.ready_to_swap == false).to_equal(true)
```

</details>

### SymbolSwap

#### test_swap_create

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw = SymbolSwap.create("old_fn", "new_fn")
expect(sw.swap_status).to_equal("pending")
```

</details>

#### test_swap_complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sw = SymbolSwap.create("old_fn", "new_fn").complete()
expect(sw.swap_status).to_equal("complete")
```

</details>

### SmfSource

#### test_source_file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SmfSource.from_file("mod.smf", 10, 3)
expect(s.source_kind).to_equal("file")
```

</details>

#### test_source_jit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SmfSource.from_jit("mod.jit", 5, 2)
expect(s.source_kind).to_equal("jit")
```

</details>

#### test_source_total

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SmfSource.from_file("mod.smf", 10, 3)
expect(s.total_symbols()).to_equal(13)
```

</details>

### ImportMetadata

#### test_import_pending

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = ImportMetadata.create("sym_foo", "libbar")
expect(im.is_resolved).to_equal(false)
```

</details>

#### test_import_resolve

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = ImportMetadata.create("sym_foo", "libbar").resolve(42)
expect(im.is_resolved).to_equal(true)
expect(im.resolved_offset).to_equal(42)
```

</details>

### DynLoadRequest

#### test_dynload_lazy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = DynLoadRequest.lazy("libfoo.so", "/usr/lib", "ns_proc")
expect(req.load_mode).to_equal("lazy")
```

</details>

### DynLoadResult

#### test_dynload_ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = DynLoadResult.ok("libfoo.so", 7)
expect(res.success).to_equal(true)
```

</details>

### LinkNamespace

#### test_namespace_global

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = LinkNamespace.global_ns()
expect(ns.is_global).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/smf_runtime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SmfHeader
- TrailerDetection
- GenerationState
- CandidateMapping
- SymbolSwap
- SmfSource
- ImportMetadata
- DynLoadRequest
- DynLoadResult
- LinkNamespace

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
