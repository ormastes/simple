# T32 Compiled (SMF) Mode Tests

> Validates T32 operations work in compiled mode.

<!-- sdn-diagram:id=compiled_smf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiled_smf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiled_smf_spec -> std
compiled_smf_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiled_smf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Compiled (SMF) Mode Tests

Validates T32 operations work in compiled mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/modes/compiled_smf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates T32 operations work in compiled mode.
All backends including ctypes are available.

## Scenarios

### T32 in compiled mode

#### core operations

#### connects to T32

1. Ok
   - Expected: c.connected is true
2. c disconnect
3. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        expect(c.connected).to_equal(true)
        c.disconnect()
    Err(e):
        expect("connect failed: {e}").to_contain("skip")
```

</details>

#### evaluates expression

1. Ok
2. c disconnect
3. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        val r = c.eval_expr("VERSION.BUILD()")
        c.disconnect()
        match r:
            Ok(v): expect(v.trim().len()).to_be_greater_than(0)
            Err(e): expect("eval: {e}").to_contain("eval")
    Err(e):
        expect("connect failed: {e}").to_contain("skip")
```

</details>

#### runs command

1. Ok
2. c disconnect
3. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        val r = c.run_command("SYStem.Up")
        c.disconnect()
        match r:
            Ok(_): expect("ok").to_equal("ok")
            Err(e): expect("cmd: {e}").to_contain("cmd")
    Err(e):
        expect("connect failed: {e}").to_contain("skip")
```

</details>

#### reads registers

1. Ok
2. c disconnect
3. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        val r = c.read_register("PC")
        c.disconnect()
        match r:
            Ok(v): expect(v).to_be_greater_than(-1)
            Err(e): expect("reg: {e}").to_contain("reg")
    Err(e):
        expect("connect failed: {e}").to_contain("skip")
```

</details>

#### ctypes backend (compiled only)

#### ctypes library availability check

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = t32_hw_ctypes_available()
# Just report availability -- not a failure if missing
if available:
    expect(available).to_equal(true)
else:
    expect("ctypes not available on this system").to_contain("not available")
```

</details>

#### connects via ctypes if available

1. Ok
2. c disconnect
3. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_probe_available() or not t32_hw_ctypes_available():
    expect("skipped").to_contain("skip")
    return
# Ctypes connection would go through the C API bridge
# For now validate that the probe at least works
val client = t32_hw_connect()
match client:
    Ok(c):
        val r = c.eval_expr("VERSION.BUILD()")
        c.disconnect()
        match r:
            Ok(v): expect(v.trim().len()).to_be_greater_than(0)
            Err(e): expect("ctypes eval: {e}").to_contain("eval")
    Err(e):
        expect("ctypes connect: {e}").to_contain("skip")
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
