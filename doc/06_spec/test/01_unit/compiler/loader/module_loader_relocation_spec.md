# Module Loader Relocation Specification

> 1. fail

<!-- sdn-diagram:id=module_loader_relocation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_loader_relocation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_loader_relocation_spec -> compiler
module_loader_relocation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_loader_relocation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Loader Relocation Specification

## Scenarios

### Module Loader relocation application

#### applies a live relocation entry from a compiled object

1. fail
2. delete if exists
3. delete if exists
4. delete if exists
   - Expected: rt_file_write_text(src_path, source) is true
5. cleanup tmpdir
6. fail
7. cleanup tmpdir
8. fail
   - Expected: relocs.len() equals `1`
   - Expected: rt_file_write_bytes(smf_path, patched_smf) is true
9. var loader = ModuleLoader with defaults
   - Expected: module.path equals `smf_path`
   - Expected: module.symbols.has("main") is true
   - Expected: patch_bytes equals `i64_to_le_bytes(expected_value)`
   - Expected: patch_bytes equals `i32_to_le_bytes(expected_value as i32)`
   - Expected: patch_bytes equals `i32_to_le_bytes(expected_value as i32)`
10. cleanup tmpdir
11. fail
12. cleanup tmpdir
13. fail
14. cleanup tmpdir


<details>
<summary>Executable SSpec</summary>

Runnable source: 72 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (tmp_stdout, _tmp_stderr, _tmp_code) = run_sh("mktemp -d")
val tmpdir = tmp_stdout.trim()
if tmpdir == "":
    fail("failed to create a temporary directory")

val src_path = "{tmpdir}/reloc_fixture.c"
val obj_path = "{tmpdir}/reloc_fixture.o"
val smf_path = "{tmpdir}/reloc_fixture.smf"

delete_if_exists(src_path)
delete_if_exists(obj_path)
delete_if_exists(smf_path)

val source = "extern long external_value;\nlong main(void) { return (long)&external_value; }\n"
expect(rt_file_write_text(src_path, source)).to_equal(true)

val (compile_stdout, compile_stderr, compile_code) = run_sh("cc -c -O0 -fno-pic -fno-pie -o '{obj_path}' '{src_path}' 2>&1")
if compile_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("cc failed: {compile_stdout}{compile_stderr}")

val object_bytes = file_read_bytes(obj_path).unwrap()
val smf_bytes = build_smf_with_relocations(object_bytes, SmfBuildOptions.create(Target.x86_64_unknown_linux_gnu()))

val parsed = SmfReaderMemory.from_data(smf_bytes)
if parsed.is_err():
    cleanup_tmpdir(tmpdir)
    fail("failed to parse generated SMF: {parsed.unwrap_err()}")

val reader = parsed.unwrap()
val main_symbol = reader.lookup_symbol("main").unwrap()
val code_bytes = reader.read_code(main_symbol).unwrap()
val relocs = reader.read_relocations().unwrap()

expect(relocs.len()).to_equal(1)
expect(relocs[0].symbol_index).to_be_greater_than(0)

val patched_smf = patch_first_reloc_symbol_index_zero(smf_bytes, code_bytes.len() as i64)
expect(rt_file_write_bytes(smf_path, patched_smf)).to_equal(true)

var loader = ModuleLoader.with_defaults()
val load_result = loader.load(smf_path)
match load_result:
    case LoadResult.Success(module):
        expect(module.path).to_equal(smf_path)
        expect(module.symbols.has("main")).to_equal(true)

        val loaded_symbol = module.symbols["main"]
        val reloc = relocs[0]
        val patch_len = match reloc.reloc_type:
            1: 8
            _: 4
        val patch_bytes = native_mmap_read_bytes(loaded_symbol.address, reloc.offset, patch_len)

        match reloc.reloc_type:
            1:
                val expected_value = loaded_symbol.address + reloc.addend
                expect(patch_bytes).to_equal(i64_to_le_bytes(expected_value))
            5:
                val expected_value = loaded_symbol.address + reloc.addend
                expect(patch_bytes).to_equal(i32_to_le_bytes(expected_value as i32))
            _:
                val expected_value = reloc.addend - reloc.offset
                expect(patch_bytes).to_equal(i32_to_le_bytes(expected_value as i32))
    case LoadResult.Error(message):
        cleanup_tmpdir(tmpdir)
        fail("loader rejected the relocation-bearing SMF: {message}")
    case _:
        cleanup_tmpdir(tmpdir)
        fail("unexpected load result")

cleanup_tmpdir(tmpdir)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/module_loader_relocation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Module Loader relocation application

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
