# Internal ELF linker cannot load the Phase 4 full-CLI inputs: per-byte `[i64]` widening OOMs

- **Date:** 2026-10-20
- **Status:** open
- **Where:** `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl`. This is
  `_InternalElfByteInputs.read_i64` (`:1407-1411`) and `read` (`:1399-1405`, which caches every
  input's `[u8]` for the whole link), plus `internal_link_native_with_operations` (`:1527-1556`).
  `ElfLinkRequest.objects`/`.archives` are `[[i64]]` (`elf/elf_static_link.spl`).

## Measurement

Run: `SIMPLE_LINKER=internal`, `link_to_native` on the kept Phase 4 objects. That is 2793 `.o`
files (364 MB) plus `libsimple_compiler_backfill.a`, `libsimple_stage4_rust_runtime.a`,
`libsimple_stage4_runtime_capsule.a`, `-lpthread -ldl -lm -lz -lzstd -ltinfo -lgcc -lgcc_s`,
`-Wl,--gc-sections`, no-PIE and the five Stage 4 `-u` roots. It ran on the seed interpreter
under a 16 GB cgroup.

- OOM-killed after 224 s at 16.7 GB, while still reading inputs. It never reached
  `elf_link_with_operations`.
- A run stopped at 150 s (`SIMPLE_INTERP_SAMPLE=1`) was at 11.6 GB. `read_i64` had 93.0% self
  time, and `file_read_bytes_result` had 0.2%.

For comparison, the same link takes 0.9 s with lld and 1.4-2.0 s with mold.

The small case works: `test/fixtures/linker/elf/hello_libc_a64.o` links in 2.0 s and the output
runs (exit 42, `hi from libc`). That needed the two fixes in this change: the `mdsocpp_seal_v1`
compact loop and the missing `?` on `elf_append_symtab`.

## Fix wanted

Read inputs as `[u8]`, or as a lazily mapped view, all the way into the engine. Do not widen
per byte in an interpreted loop or keep a second cached copy. `elf/stream_link.spl` already
streams, but `internal_link_native` does not use it, and it rejects TLS, IFUNC and GNU-unique
symbols (`elf/stream_inputs.spl:304`), which the Rust runtime archive needs. Until inputs
load, the engine's real gaps at this scale are unmeasured: relocation coverage over cranelift
output, TLS in the Rust staticlib, `--start-group` over three archives, and `-ltinfo`/`-lzstd`
resolution.

## Entry points (for whoever picks this up)

- No `simple link` subcommand exists. The only selector is `SIMPLE_LINKER=internal` through
  `link_to_native` (`mold.spl:139`). The Rust seed's alias table (`linker.rs` `linker_alias`)
  rejects `internal`, so a seed `native-build` cannot pick it.
- The deployed Phase 4 CLI's own `native-build` stops at SCV admission
  (`entry absent from frozen inventory`) before linking, for a tracked example entry.
- The scratch driver used for these runs called `link_to_native(objects, out, cfg)` from
  `bin/simple run`.
