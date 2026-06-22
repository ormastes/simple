# Hosted SDL2 Backend Spec

> Unit tests for the SDL2 compositor backend. Tests use the headless

<!-- sdn-diagram:id=hosted_backend_sdl2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hosted_backend_sdl2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hosted_backend_sdl2_spec -> std
hosted_backend_sdl2_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hosted_backend_sdl2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted SDL2 Backend Spec

Unit tests for the SDL2 compositor backend. Tests use the headless

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/hosted_backend_sdl2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the SDL2 compositor backend. Tests use the headless
fallback path since rt_sdl2_* externs return stubs in test mode.

## Scenarios

### HostedSdl2Backend

#### reports sdl2-native as implementation name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(HostedSdl2Backend.implementation_name()).to_equal("sdl2-native")
```

</details>

#### rejects zero-width creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = HostedSdl2Backend.try_create(0, 480, "test")
expect(result == nil).to_equal(true)
```

</details>

#### rejects zero-height creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = HostedSdl2Backend.try_create(640, 0, "test")
expect(result == nil).to_equal(true)
```

</details>

#### rejects negative dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = HostedSdl2Backend.try_create(-1, -1, "test")
expect(result == nil).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
