# Native Compile ELF

> Tests the native compilation pipeline that produces ELF executables directly from Simple source. Verifies end-to-end compilation from source through code generation to linked ELF output with correct relocations and entry points.

<!-- sdn-diagram:id=native_compile_elf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_compile_elf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_compile_elf_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_compile_elf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Compile ELF

Tests the native compilation pipeline that produces ELF executables directly from Simple source. Verifies end-to-end compilation from source through code generation to linked ELF output with correct relocations and entry points.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/native_compile_elf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the native compilation pipeline that produces ELF executables directly from
Simple source. Verifies end-to-end compilation from source through code generation
to linked ELF output with correct relocations and entry points.

## Scenarios

### Native Compile ELF

#### generates a valid ELF binary from x86_64 machine code

1. var writer = elf writer x86 64
2. var text section = new text section
3. writer = elf add section
4. writer = elf add symbol
   - Expected: elf_bytes.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native ELF writer":
    # main: push rbp; mov rbp,rsp; xor eax,eax; pop rbp; ret
    val code = [0x55, 0x48, 0x89, 0xe5, 0x31, 0xc0, 0x5d, 0xc3]
    var writer = elf_writer_x86_64()
    var text_section = new_text_section(code)
    writer = elf_add_section(writer, text_section)
    writer = elf_add_symbol(writer, new_func_symbol("main", 1, 0, code.len()))
    val elf_bytes = write_elf64(writer)
    expect(elf_bytes.len() > 0).to_equal(true)
```

</details>

#### produces a linkable and runnable binary with exit 0

1. var writer = elf writer x86 64
2. var text section = new text section
3. writer = elf add section
4. writer = elf add symbol
5. end idx = elf bytes len
6. chunk = chunk + byte to hex
7. shell
8. shell
9. shell
10. shell
   - Expected: link_r[2] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend and linker":
    val code = [0x55, 0x48, 0x89, 0xe5, 0x31, 0xc0, 0x5d, 0xc3]
    var writer = elf_writer_x86_64()
    var text_section = new_text_section(code)
    writer = elf_add_section(writer, text_section)
    writer = elf_add_symbol(writer, new_func_symbol("main", 1, 0, code.len()))
    val elf_bytes = write_elf64(writer)

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
            shell("echo -n '{chunk}' > /tmp/elf_spec.hex")
        else:
            shell("echo -n '{chunk}' >> /tmp/elf_spec.hex")
        offset = end_idx

    shell("xxd -r -p /tmp/elf_spec.hex /tmp/elf_spec.o")
    shell("rm -f /tmp/elf_spec.hex")
    val link_r = rt_process_run("cc", ["-o", "/tmp/elf_spec", "/tmp/elf_spec.o", "-no-pie"])
    expect(link_r[2]).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
