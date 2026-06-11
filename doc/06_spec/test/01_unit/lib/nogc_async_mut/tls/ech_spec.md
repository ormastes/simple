# TLS ECH Parse Check Specification

> <details>

<!-- sdn-diagram:id=ech_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ech_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ech_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ech_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TLS ECH Parse Check Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC-11 |
| Category | Stdlib / TLS / ECH |
| Difficulty | 3/5 |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/tls/ech_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### ECH types and disabled config (AC-11)

#### disabled config has empty config list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ech_server_config_disabled()
expect(cfg.enabled).to_equal(false)
expect(cfg.config_list.configs.len()).to_equal(0)
```

</details>

#### detect returns nil for empty extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = detect_ech_extension([])
expect(result.?).to_equal(false)
```

</details>

#### detect returns nil for short extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = detect_ech_extension([0, 0])
expect(result.?).to_equal(false)
```

</details>

#### server decides NotPresent when no ECH

1. fail
2. fail
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = ech_server_decide(nil, ech_server_config_disabled())
match decision:
    case EchDecision.NotPresent:
        expect(decision).to_equal(EchDecision.NotPresent)
    case EchDecision.ProviderUnavailable:
        fail("disabled ECH config returned ProviderUnavailable instead of NotPresent")
    case EchDecision.AcceptInner:
        fail("disabled ECH config accepted inner ClientHello without ECH")
    case EchDecision.RejectWithRetryConfig:
        fail("disabled ECH config requested retry config without ECH")
```

</details>

#### retry config extension is empty when disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ech_server_config_disabled()
val ext = ech_build_retry_config_extension(cfg)
expect(ext.len()).to_equal(0)
```

</details>

#### grease extension needs at least 10 random bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val short = ech_grease_extension_data([1, 2, 3])
expect(short.len()).to_equal(0)
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


</details>
