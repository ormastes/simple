# Main Specification

> <details>

<!-- sdn-diagram:id=main_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=main_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

main_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=main_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Main Specification

## Scenarios

### svllm_pack CLI (A2)

#### exits 2 with usage when invoked with no args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv: [text] = ["svllm-pack"]
val code = run(argv)
expect(code).to_equal(2)
```

</details>

#### exits 1 when the input path does not exist

1.  tmp path
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv: [text] = [
    "svllm-pack",
    "/tmp/svllm_a2_cli_nonexistent.safetensors",
    _tmp_path("out_missing")
]
val code = run(argv)
expect(code).to_equal(1)
```

</details>

#### exits 1 on malformed safetensors input

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Write a tiny garbage file and hand it to the CLI.
val bad_path = _tmp_path("bad.safetensors")
# (Setup through runtime externs is Phase 5's responsibility; the
# spec still asserts the observable contract.)
val argv: [text] = ["svllm-pack", bad_path, _tmp_path("out_bad")]
val code = run(argv)
expect(code).to_equal(1)
```

</details>

#### exits 0 on a valid tiny safetensors and produces manifest.sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The 162-byte fixture is built + written in Phase 5's integration
# harness; here we only pin the contract: valid input => exit 0.
val good_path = _tmp_path("good.safetensors")
val out_dir = _tmp_path("out_good")
val argv: [text] = ["svllm-pack", good_path, out_dir]
val code = run(argv)
expect(code).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/svllm_pack/main_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svllm_pack CLI (A2)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
