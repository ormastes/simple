# Seed: aliased re-exports / imports (`export use m.{a as b}`) do not resolve on every path

- Date: 2026-11-13. Reported by the independent review of lane `work/spy-xray-2-20261113`
  (tip `ad5d4631a6c`), on the reviewer's pinned seed.

## Observation (reviewer)

- `linker/_ElfWriter/encoding.spl` defined `write_u{16,32,64}_le` only as
  `export use std.common.binary_io.{bytes_i64_push_u32_le as write_u32_le, ...}`, and
  `linker/elf_writer.spl:9` re-exports encoding with a glob (`export use ..._ElfWriter.encoding.*`).
  `use compiler.backend.linker.elf_writer.{write_u32_le}` then failed with
  "function write_u32_le not found"; `elf_exec_writer_spec` fell from 6/32 to 2/32.
- `std.common.isa.x64_encode_v1` exported `x64_push_imm32_le_v1` the same way;
  `xray_native_trampoline_x86_64_v1_spec` fell to 1/3 ("x64_push_imm32_le_v1 not found").

So an aliased name reached through a glob re-export, or from a transitively loaded module, is
not registered.

## Not reproduced here

On `src/compiler_rust/target/bootstrap/simple` (sha256 `df9dfb057afb7b8f…`, 2026-11-05) both
paths resolved: `elf_exec_writer_spec` 19/32 on base and tip, the x86-64 trampoline spec 3/3.
The defect is binary-dependent; code in the tree must not rely on it.

## Workaround in the tree

Thin local wrapper functions calling the shared body (no `as` in any import or re-export) in
`_ElfWriter/encoding.spl`, `std.common.isa.x64_encode_v1`, `backend/native/encode_aarch64.spl`
and `linker/coff/coff_object.spl` (`coff_is_bigobj`).

## Next step

Make the resolver register `export use m.{a as b}` under `b` for glob re-exports and for
modules loaded transitively, then add a spec that imports an aliased name through
`export use x.*`.
