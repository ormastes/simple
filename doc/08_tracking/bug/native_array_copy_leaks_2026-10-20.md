# Native builds leak array copies: helper append, nested-element binding, nested-element argument; `flat`/`base` struct-field parse failure

- **Date:** 2026-10-20
- **Status:** open (codegen / runtime). The internal ELF linker carries `# workaround:` sites that name this record.
- **Seed:** `37b0735cf93c`, cranelift, core-c-bootstrap runtime, `SIMPLE_NATIVE_BUILD_RUST=1`

## Measurements

Each row is a native probe; its `.spl` sits under `test/fixtures/linker/multimod_scratch/` and was not committed. Growth is `process_hwm_kib` before and after the loop.

| pattern | loop | growth |
|---|---|---|
| `xs.push(v)` | 200k | +1.7 MB (fine) |
| `xs = xs.push(v)`, same scope | 200k | +1.6 MB (fine) |
| `fn add(b: [i64], v) -> [i64]: var c = b; c = c.push(v); c` called as `xs = add(xs, v)` | 20k | **+1.6 GB** (copy per call, never freed) |
| `val r = rows[0]` on `[[i64]]` (100k elements) | 2000 | **+1.5 GB** (deep copy per binding, never freed) |
| `val h = holders[0]` (struct with an array field) | 2000 | +60 KB (fine) |
| `rows[0][i]` read or `rows[0][i] = v` write | 2000 | ~0 (fine) |

Passing `contents[k]` (a nested element) as a call argument behaved like the `val` binding and copied the whole section per call.

## Parse bug

A struct constructor argument named `flat` or `base`, for example `_GcState(flat: flat, base: base, ...)`, fails in native-build discovery with `function arguments: expected Comma, found Colon`. The interpreter accepts it.

## Effect on the internal linker

Full cranelift CLI link (2793 objects, 2.3M relocations) with the native driver:

- Before the workarounds, it was OOM-killed at 16 GB in section GC.
- After them, it links in **79 s at a peak RSS of 21.3 GB**.

Most of that peak is still per-record temporaries that are never freed:

| phase | approx. growth |
|---|---|
| relocation loop | +7 GB |
| ElfScanRef records | +3.7 GB |
| symtab | +2.4 GB |

A 153-module program now links in 1.2 s at 397 MB; it was 3.8 GB before.

## Workarounds (revert once fixed)

These sites accumulate into locals, extend with small fresh chunks, index nested arrays directly, and flatten per-object tables:

- `elf/elf_static_link.spl`: contents builder, relocation windows, symtab rows/entries, GOT/rela tables, symtab header patches
- `elf/tls_relax.spl`: batched TLS patches
- `elf/section_gc.spl`: flat live table, direct range indexing, renamed `marks`/`bases` fields
- `elf/synthetic_sections.spl`: `elf_rela_entry` and `elf_sym_entry` return chunks
