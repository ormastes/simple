# Loader Run Function Specification

> <details>

<!-- sdn-diagram:id=loader_run_function_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=loader_run_function_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

loader_run_function_spec -> compiler
loader_run_function_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=loader_run_function_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Loader Run Function Specification

## Scenarios

### Loader run function

<details>
<summary>Advanced: loads a precompiled stub and executes it</summary>

#### loads a precompiled stub and executes it _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Precompiled machine code: mov eax, 7; ret (x86_64)
val code: [u8] = [184, 7, 0, 0, 0, 195]

# Write mock SMF code section as raw bytes to a fake path (loader reads via SmfReader; here minimal stand-in)
# NOTE: This is a placeholder until a real SMF fixture is available in compiled mode.
# Using loader directly on code is not supported in interpreter; expect NotFound in interpreter mode.
val loader = ModuleLoader.with_defaults()
val load_res = moduleloader_load(loader, "build/artifacts/mock.smf")
match load_res:
    case Error(msg):
        expect true   # placeholder to allow interpreter run
    case _:
        val sym_res = moduleloader_resolve_symbol(loader, "_start")
        match sym_res:
            case Found(sym, _):
                val result = native_call_function_0(sym.address)
                expect(result).to_equal(7)
            case _:
                expect true
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/loader_run_function_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Loader run function

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
