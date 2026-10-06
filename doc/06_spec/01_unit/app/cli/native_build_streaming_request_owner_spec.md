# Native Build Streaming Request Owner Specification

> Tests covering Native build streaming cache warmup owner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Build Streaming Request Owner Specification

## Scenarios

### Native build streaming cache warmup owner

#### honors ordinary and stage four streaming requests without bootstrap mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val previous_stage3 = env_get("SIMPLE_STAGE3_STREAMING_SURFACES") ?? ""
val previous_stage4 = env_get("SIMPLE_BOOTSTRAP_STAGE4") ?? ""
val previous_stage4_streaming = env_get("SIMPLE_STAGE4_STREAMING_SURFACES") ?? ""
val previous_bootstrap = env_get("SIMPLE_BOOTSTRAP") ?? ""
env_set("SIMPLE_BOOTSTRAP", "")
env_set("SIMPLE_STAGE3_STREAMING_SURFACES", "")
env_set("SIMPLE_BOOTSTRAP_STAGE4", "")
env_set("SIMPLE_STAGE4_STREAMING_SURFACES", "")
val ordinary_default = native_build_streaming_surfaces()
env_set("SIMPLE_STAGE3_STREAMING_SURFACES", "1")
val ordinary_requested = native_build_streaming_surfaces()
env_set("SIMPLE_STAGE3_STREAMING_SURFACES", "0")
val ordinary_off = native_build_streaming_surfaces()
env_set("SIMPLE_BOOTSTRAP_STAGE4", "1")
env_set("SIMPLE_STAGE4_STREAMING_SURFACES", "1")
val stage4_requested = native_build_streaming_surfaces()
env_set("SIMPLE_STAGE4_STREAMING_SURFACES", "0")
val stage4_off = native_build_streaming_surfaces()
env_set("SIMPLE_STAGE3_STREAMING_SURFACES", previous_stage3)
env_set("SIMPLE_BOOTSTRAP_STAGE4", previous_stage4)
env_set("SIMPLE_STAGE4_STREAMING_SURFACES", previous_stage4_streaming)
env_set("SIMPLE_BOOTSTRAP", previous_bootstrap)
expect(ordinary_default).to_equal(false)
expect(ordinary_requested).to_equal(true)
expect(ordinary_off).to_equal(false)
expect(stage4_requested).to_equal(true)
expect(stage4_off).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/native_build_streaming_request_owner_spec.spl` |
| Updated | 2026-10-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Native build streaming cache warmup owner.
- Native build streaming cache warmup owner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

## Verification evidence and remaining qualification

Phase 1 immutable compiler SHA256 `0f9bfc1f7a9f6aca254755a543687d6b3d60f18b254da9441cb60e1cd3d4a2c7`, interpreter mode: one actual named example passed with five assertions, zero failures/skips/ignored, 282 ms. Peak 174,896 KiB under a 1 GiB outer watchdog. The subsequent source change adds only the manual display annotation; behavior was not replayed.

The isolated single-example test restores saved string values before its assertions. The facade has no environment-unset export: an originally absent variable becomes explicitly empty. These four request flags treat both values identically; this is value restoration, not preservation of absence.

Canonical SPipe generation completed with one complete manual and zero stubs, one active scenario and its full Executable SSpec block. Generator watchdog exit 0, peak 341,648 KiB under 1 GiB; receipts are retained in `/tmp/simple-memory-routing-owner-evidence-20261006/docgen`.

Native admission remains pending: the changed producer must execute a normal-coordinator ordinary streaming build, skip redundant parse-cache workers, preserve source-authority and semantic rejection gates, and build/run the result under the aggregate 6 GB bound. Native elapsed/RSS and performance evidence are required; the focused owner PASS does not prove these gates.
