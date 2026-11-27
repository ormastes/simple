# Seed records no owner bindings for a module loaded inside a re-export cycle (2026-11-13)

Status: open. Worked around for `ElfSymbol` (`elf_section_symbol()` in
`src/compiler/70.backend/backend/native/elf_writer.spl`, commit `8ff40e8e469`).

## Shape
`backend/native/elf_writer.spl` does `export use compiler.backend.native.elf_writer_serialize.*`
and `elf_writer_serialize.spl` does `use compiler.backend.native.elf_writer.*`.
When the serializer runs, the pinned seed (554460a6b85a) resolves a bare class
name through `resolve_class_in_scope` -> `owner_module_def`
(`src/compiler_rust/compiler/src/module_cache.rs`). The walk for the serializer
misses because `owner_bindings(<elf_writer_serialize.spl>)` has no entry, so its
glob import of `elf_writer` is never followed. With `SIMPLE_DBG_COLLISION=1`:

    [DBG WALK] name=ElfSymbol owner=.../native/elf_writer_serialize.spl hit=false
    [DBG SCOPE] name=ElfSymbol owner=.../native/elf_writer_serialize.spl walk=miss
      candidates=[.../native/elf_writer.spl, .../linker/elf_parser.spl, <entry>] flat=true
    error: semantic: ambiguous type `ElfSymbol`: ... none of them is imported by
      .../native/elf_writer_serialize.spl

Adding an explicit `use compiler.backend.native.elf_writer.{ElfSymbol}` to the
serializer did NOT fix it (verified), which points at the missing binding table
rather than at glob-vs-named resolution.

## Likely second symptom
`test/01_unit/compiler/backend/native/comdat_instance_dedup_spec.spl` fails with
`in call to buf_write_zeroes (declared at line 287): variable ELF64_SYM_SIZE not found`
— a serializer-side name from the same `elf_writer` <-> `elf_writer_serialize`
pair. Identical on base `30382bc764e` and on `work/spy-3-e2e-20261113`.

## Repro
    SIMPLE_DBG_COLLISION=1 XR_SRC=test/fixtures/xray/xray_inprocess_prog.spl XR_OUT=/tmp/libon.so XR_XRAY=1 \
      SIMPLE_NATIVE_BUILD_EMIT_OBJECT=shared <seed> run test/fixtures/xray/xray_native_cli_compile_driver.spl
on `30382bc764e` (before the workaround); grep `DBG WALK.*ElfSymbol`.

## Fix direction
Record owner bindings for a module whose load is entered from inside another
module's `export use` (the cycle edge), or break the cycle by moving the shared
ELF types into a leaf module both files import.
