# Platform Library Example Specification

> 1. print "  Host: {arch name}-{os name}

<!-- sdn-diagram:id=platform_library_example_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=platform_library_example_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

platform_library_example_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=platform_library_example_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Platform Library Example Specification

## Scenarios

### Platform Library Examples

#### Example 1: Auto-detect host platform

1. print "  Host: {arch name}-{os name}
   - Expected: arch_name.len() > 0 is true
   - Expected: os_name.len() > 0 is true
   - Expected: host.pointer_bytes > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = host_config()

# Platform information is automatically detected
val arch_name = host.arch.name()
val os_name = host.os.name()
val endian_name = host.endian.name()

print "  Host: {arch_name}-{os_name} ({endian_name}-endian)"

# Verify detection worked
expect(arch_name.len() > 0).to_equal(true)
expect(os_name.len() > 0).to_equal(true)
expect(host.pointer_bytes > 0).to_equal(true)
```

</details>

#### Example 2: Same-platform conversion (zero-cost no-op)

1. print "  Value: {value} → {result}
   - Expected: result equals `value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = host_config()
val value = 42

# When host == remote, no conversion happens
val result = send_u32(host, host, value)

print "  Value: {value} → {result} (no conversion)"

expect(result).to_equal(value)
```

</details>

#### Example 3: Cross-endian byte swapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create configs for little-endian and big-endian platforms
val le = make_config(TargetArch.X86_64(), TargetOS.Linux())
val be = make_config(TargetArch.MCS51(), TargetOS.BareMetal())

val original = 0x12345678
val swapped = send_u32(le, be, original)
val restored = recv_u32(le, be, swapped)

print "  LE: 0x{original:x} → BE: 0x{swapped:x} → LE: 0x{restored:x}"

# Verify byte swap happened
expect(swapped).to_equal(0x78563412)
# Verify round-trip
expect(restored).to_equal(original)
```

</details>

#### Example 4: Network byte order (always big-endian)

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = host_config()
val net = network_config()

val value = 0x1A2B3C4D
val network_val = send_u32(host, net, value)
val restored = recv_u32(host, net, network_val)

print "  Local: 0x{value:x} → Network: 0x{network_val:x}"

# Network byte order is big-endian
expect(network_val == 0x4D3C2B1A or network_val == value).to_equal(true)
# Round-trip works
expect(restored).to_equal(value)
```

</details>

#### Example 5: Text newline conversion (LF ↔ CRLF)

1. print "  Unix
   - Expected: unix_len equals `17`
   - Expected: win_len equals `19`
   - Expected: back equals `unix_text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unix = make_config(TargetArch.X86_64(), TargetOS.Linux())
val win = make_config(TargetArch.X86_64(), TargetOS.Windows())

val unix_text = "Line1\nLine2\nLine3"
val win_text = send_text(unix, win, unix_text)
val back = recv_text(unix, win, win_text)

val unix_len = unix_text.len()
val win_len = win_text.len()
val back_len = back.len()
print "  Unix ({unix_len}b) → Win ({win_len}b) → Unix ({back_len}b)"

# Windows text is longer (CRLF vs LF)
expect(unix_len).to_equal(17)
expect(win_len).to_equal(19)
# Round-trip preserves content
expect(back).to_equal(unix_text)
```

</details>

#### Example 6: Wire format serialization

1. var writer = wire writer network
2. writer write u32
3. writer write text
4. writer write u32
5. var reader = wire reader new
   - Expected: n1 equals `12345`
   - Expected: msg equals `Protocol`
   - Expected: n2 equals `67890`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Serialize data in network byte order
var writer = wire_writer_network()
writer.write_u32(12345)
writer.write_text("Protocol")
writer.write_u32(67890)

val bytes = writer.to_bytes()

# Deserialize from network byte order
var reader = wire_reader_new(bytes, network_config())
val n1 = reader.read_u32()
val msg = reader.read_text()
val n2 = reader.read_u32()

# Verify round-trip
expect(n1).to_equal(12345)
expect(msg).to_equal("Protocol")
expect(n2).to_equal(67890)
```

</details>

#### Example 7: Platform-aware file I/O

1. text file write local
2. file delete
   - Expected: read_back equals `content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/platform_test.txt"
val content = "First\nSecond\nThird\n"

# Write with host platform newlines
text_file_write_local(path, content)

# Read back
val read_back = text_file_read_local(path)

# Clean up
file_delete(path)

# Content preserved
expect(read_back).to_equal(content)
```

</details>

#### Example 8: Creating custom platform configs

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create configs for various platforms
val arm_linux = make_config(TargetArch.Arm(), TargetOS.Linux())
val riscv_bare = make_config(TargetArch.Riscv64(), TargetOS.BareMetal())
val x86_win = make_config(TargetArch.X86_64(), TargetOS.Windows())

val arm_nl_len = arm_linux.newline.len()
val riscv_nl_len = riscv_bare.newline.len()
val win_nl_len = x86_win.newline.len()
print "  ARM/Linux: {arm_linux.pointer_bytes}b ptr, {arm_nl_len}b nl"
print "  RISC-V bare: {riscv_bare.pointer_bytes}b ptr, {riscv_nl_len}b nl"
print "  x86_64/Win: {x86_win.pointer_bytes}b ptr, {win_nl_len}b nl"

# Verify configs
expect(arm_linux.pointer_bytes).to_equal(4)
expect(riscv_bare.pointer_bytes).to_equal(8)
val win_nl = x86_win.newline
expect(win_nl_len).to_equal(2)
```

</details>

#### Example 9: Checking platform compatibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# use std.platform.config.{same_platform, needs_swap}

val host = host_config()
val net = network_config()

# Check if platforms are the same
val is_same = same_platform(host, host)
val needs_convert = needs_swap(host, net)

print "  Same platform: {is_same}"
print "  Needs swap: {needs_convert}"

expect(is_same).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/examples/platform_library_example_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Platform Library Examples

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
