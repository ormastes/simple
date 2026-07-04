# MIR Complex Constructs

> Tests MIR generation for complex language constructs including closures, pattern matching, generics, and trait dispatch. Verifies that advanced features are correctly lowered to MIR with proper type erasure and monomorphization.

<!-- sdn-diagram:id=mir_complex_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mir_complex_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mir_complex_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mir_complex_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MIR Complex Constructs

Tests MIR generation for complex language constructs including closures, pattern matching, generics, and trait dispatch. Verifies that advanced features are correctly lowered to MIR with proper type erasure and monomorphization.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/mir_complex_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests MIR generation for complex language constructs including closures, pattern
matching, generics, and trait dispatch. Verifies that advanced features are
correctly lowered to MIR with proper type erasure and monomorphization.

## Scenarios

### MIR Complex

#### compiles arithmetic and if/else MIR and outputs '42'

1. end idx = elf bytes len
2. chunk = chunk + byte to hex
3. shell
4. shell
5. shell
6. shell
   - Expected: link_r[2] equals `0`
   - Expected: run_r[0].trim() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend and linker":
    val module = build_complex_module()
    val mach_module = isel_module(module)
    val allocated = regalloc_module(mach_module)
    val encoded_funcs = encode_module(allocated)
    val elf_bytes = emit_elf_complex(encoded_funcs, allocated)

    var offset = 0
    while offset < elf_bytes.len():
        var chunk = ""
        var end_idx = offset + 800
        if end_idx > elf_bytes.len():
            end_idx = elf_bytes.len()
        var j = offset
        while j < end_idx:
            chunk = chunk + byte_to_hex(elf_bytes[j])
            j = j + 1
        if offset == 0:
            shell("echo -n '{chunk}' > /tmp/mir_complex_spec.hex")
        else:
            shell("echo -n '{chunk}' >> /tmp/mir_complex_spec.hex")
        offset = end_idx

    shell("xxd -r -p /tmp/mir_complex_spec.hex /tmp/mir_complex_spec.o")
    shell("rm -f /tmp/mir_complex_spec.hex")
    val link_r = rt_process_run("cc", ["-o", "/tmp/mir_complex_spec", "/tmp/mir_complex_spec.o", "-no-pie"])
    expect(link_r[2]).to_equal(0)

    val run_r = rt_process_run("/tmp/mir_complex_spec", [])
    expect(run_r[0].trim()).to_equal("42")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
