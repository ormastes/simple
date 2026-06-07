# Play Cdp Facade Specification

> <details>

<!-- sdn-diagram:id=play_cdp_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=play_cdp_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

play_cdp_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=play_cdp_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Play Cdp Facade Specification

## Scenarios

### nogc_async_mut play cdp facade

#### re-exports pure CDP URL and frame helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = cdp_parse_ws_url("ws://127.0.0.1:9222/devtools/page/abc")
expect(parsed.0).to_equal("127.0.0.1")
expect(parsed.1).to_equal(9222)
expect(parsed.2).to_equal("/devtools/page/abc")
expect(parsed.3).to_equal(false)

val frame = cdp_parse_frame([WS_FIN | WS_OP_TEXT, 2, 111, 107])
expect(frame.parsed).to_equal(true)
expect(frame.opcode).to_equal(WS_OP_TEXT)
expect(frame.payload.length()).to_equal(2)
```

</details>

#### re-exports CDP domain constants and modifier helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CDP_DEFAULT_TIMEOUT).to_equal(10000)
expect(cdp_modifiers_from(["alt", "control", "shift"])).to_equal(CDP_MOD_ALT | CDP_MOD_CTRL | CDP_MOD_SHIFT)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/play/cdp/play_cdp_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut play cdp facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
