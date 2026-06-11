# Dap Adapter Facade Specification

> <details>

<!-- sdn-diagram:id=dap_adapter_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dap_adapter_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dap_adapter_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dap_adapter_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dap Adapter Facade Specification

## Scenarios

### nogc_async_mut dap adapter facade

#### re-exports adapter config and capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.gdb("localhost", 3333, "kernel.elf")
expect(cfg.adapter_type).to_equal("gdb")
expect(cfg.port).to_equal(3333)
expect(AdapterCapabilities.basic().supports_memory).to_equal(false)
expect(AdapterCapabilities.basic().with_memory().supports_memory).to_equal(true)
expect(lldb_config("app.spl").adapter_type).to_equal("lldb-dap")
```

</details>

#### re-exports DAP framing and JSON helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dap_encode("{}")).to_equal("Content-Length: 2\r\n\r\n{}")
expect(dap_parse_content_length("Content-Length: 17")).to_equal(17)
expect(dap_request(3, "launch", "{}")).to_contain("\"command\":\"launch\"")
val json = "{\"name\":\"main\",\"ok\":true,\"line\":42}"
expect(json_get_text(json, "name")).to_equal("main")
expect(json_get_bool(json, "ok")).to_equal(true)
expect(json_get_int(json, "line")).to_equal(42)
```

</details>

#### re-exports stlink parsing helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_hex("10")).to_equal(16)
expect(parse_stlink_hex_dump("01 0f 10")[2]).to_equal(16)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/dap/adapter/dap_adapter_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut dap adapter facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
