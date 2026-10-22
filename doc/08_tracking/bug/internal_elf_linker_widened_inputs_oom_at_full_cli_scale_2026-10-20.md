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

## Update 2026-10-20: input widening fixed; the remaining cost is the interpreter

Fixed by keeping the hosted path packed `[u8]` from file read to published image.
Bytes now move only by slice and in-place `extend`. Several quadratic copies under
value semantics were also removed:

- whole-section copy per relocation (now a widened 16-byte window, written back in place)
- definition map copied per object in archive closure and `sym_resolve_objects`
- live table and worklist copied per mark in section GC
- full relocation scan per live section in section GC
- linear pair scans per relocation in AArch64 TLS relax
- per-record relocation scans in `.eh_frame` GC
- insertion-sorted `.eh_frame_hdr`
- per-character strtab names
- pure-Simple SHA-1 build-id

The build-id is now the first 20 bytes of SHA-256 over the image with the payload
zeroed. It is deterministic: same input bytes give the same id. It is computed by
the runtime digest, and its shape is the 20-byte `NT_GNU_BUILD_ID` note.

Measured on the seed interpreter, kept cranelift full-CLI set (2793 objects, 2.3M
relocations, 3.2M symbols):

| phase | before | after |
|---|---|---|
| read inputs | OOM at 16.7 GB after 224 s | 2.2 s |
| parse objects | not reached | 568 s, 9.4 GB RSS |
| archive closure | not reached | 727 s |

Those are AST-interpreter costs: about 1 us per operation and about 1.7 KB per parsed
symbol or relocation record. Imported modules never JIT under `bin/simple run`. The
JIT compiles only the entry file and drops the whole program to the interpreter on the
first unresolved import. A full link therefore needs a natively built driver
(`test/05_perf/compiler/linker/internal_link_spec_driver.spl`) or the deployed
compiler's own `native-build`.

Seed-interpreter traps found along the way (not fixed here):

- `[u8].extend([i64])` is a silent no-op under the JIT.
- An out-of-range `[u8]` read returns 0 under the JIT.
- A class instance passed as a parameter is copied under the interpreter, so `me`
  mutations through the parameter are lost.
- Arithmetic on `[u8]` elements wraps at 8 bits unless cast `as i64`.
- `[[], []]` element arrays reject `extend`.

## Update 2026-10-20 (later): full cranelift CLI links with the internal linker

The linker driver (`test/05_perf/compiler/linker/internal_link_spec_driver.spl`) was built natively with seed `37b0735c`, with the
workarounds in `native_array_copy_leaks_2026-10-20.md`. It linked the kept cranelift full-CLI set
(wyZqCb) under `MemoryMax=24G`:

- **Time:** 79 s wall.
- **Peak RSS:** 21.3 GB. Per-phase peak RSS is printed by `SIMPLE_ELF_LINK_TRACE=1` as `hwm_kib`.
- **Phase times:**

  | phase | time |
  |---|---|
  | parse | 4.8 s |
  | archive closure | 2.5 s |
  | resolve | 7.2 s |
  | refs | 12.6 s |
  | relocation | 30.5 s |
  | symtab | 7.0 s |

- **Output:** 58 MB, against lld's 64.5 MB.

**Acceptance, same as the ld.lld link:**
- `nm -D -u` has no `rt_`/`spl_` symbols. The only difference from lld is the weak `__gmon_start__` and `_ITM_*` refs that crtbegin.o brings in.
- NEEDED is libc, libm and libgcc_s.
- `--version` and `-c 'print(1+1)'` (prints 2) match lld.
- `run hello.spl` gives the same output.
- A fixture spec run gives the same verdict as the lld binary.

For comparison, mold takes 1.4-2.0 s at 45 MB and lld 0.9 s at 680 MB.
