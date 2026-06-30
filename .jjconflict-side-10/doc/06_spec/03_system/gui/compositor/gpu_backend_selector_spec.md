# gpu_backend_selector_spec

> Feature: GPU backend selector (TODO #29)

<!-- sdn-diagram:id=gpu_backend_selector_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_backend_selector_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_backend_selector_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_backend_selector_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_backend_selector_spec

Feature: GPU backend selector (TODO #29)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/compositor/gpu_backend_selector_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Feature: GPU backend selector (TODO #29)
Category: compositor / display
Status: RED

## Scenarios

### select_backend with has_gpu=true

#### routes to the GPU backend contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_selector_probe(true)
expect(code).to_equal(0)
expect(stdout.contains("Passed: 1")).to_equal(true)
```

</details>

### select_backend with has_gpu=false

#### routes to the framebuffer fallback contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_selector_probe(false)
expect(code).to_equal(0)
expect(stdout.contains("Passed: 1")).to_equal(true)
```

</details>

### CompositorBackend trait parity

#### supports the shared backend surface for both capability branches

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (gpu_stdout, _gpu_stderr, gpu_code) = run_selector_probe(true)
val (fb_stdout, _fb_stderr, fb_code) = run_selector_probe(false)
expect(gpu_code).to_equal(0)
expect(fb_code).to_equal(0)
expect(gpu_stdout.contains("Passed: 1")).to_equal(true)
expect(fb_stdout.contains("Passed: 1")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
