# Internal ELF linker: 200-object link is slow and memory-heavy

- Date: 2026-11-16
- Status: verification-pending. One hotspot is fixed and the rest is still open.
- Area: `src/compiler/70.backend/linker/elf/` (`SIMPLE_LINKER=internal`)
- Related: `internal_elf_linker_elf32_i386_armv7_2026-11-16.md` (item 6),
  `native_array_copy_leaks_2026-10-20.md`

## Benchmark

- Inputs: 200 synthetic x86_64 objects with about 120k relocations, linked
  statically. The objects come from the #9808 lane at
  `C:/dev/wt/elfpar-20261116/build/elfpar/big/o{0..199}.o`. They are not
  committed: regenerate any set of 200 clang `-c` objects of about 600
  relocations each.
- Driver: `build/elfpar/link_driver.spl` from the same lane. It is called with
  `LARCHS=x86_64`, `LINPUTS=<comma list>`, `LOUT=<dir>` and `LJOBS=1`.
- Build command:
  `SIMPLE_NATIVE_BUILD_RUST=1 bin/simple.exe native-build link_driver.spl -o ld.exe --timeout=1500`.
  Put llvm-mingw first on PATH. A cold build of `elf_static_link.spl` needs
  more than the default 300 s file timeout.
- Phase breakdown: `SIMPLE_ELF_LINK_TRACE=1`.

## Measured (Windows x86_64 native, jobs=1, same session)

| build | link ms | peak RSS | output |
|---|---|---|---|
| before (release/1.0.0 @ 017665fc70b) | 29622 | 10.1 GB | reference |
| after (TLS pair set) | 7903 | 1.06 GB | byte-identical |
| ld.lld / mold (WSL) | 120 / 100 | 68 MB / 7 MB | - |

Fixed: x86_64 `_tls_relax_object` called `_tls_is_pair(obj, i)` for every
non-TLS relocation. Each call scanned every relocation in the object, and for
each TLS head it ran another full pair scan. The phase took 21.5 s and grew RSS
by 9.1 GB. Pair members are now computed once per object (`_tls_pair_members`),
and the phase takes 18 ms.

## Open

1. Sharing an input object made later phases much slower, and the cause is
   unexplained. An `if no TLS heads: return Ok(obj)` early-out was tried and
   then removed (it is not in the landed change). With it, output stayed
   byte-identical. Even so, refs collection went from 1.8 s to
   38 s, apply from 4.2 s to 21.8 s, and symtab from 0.7 s to 21.9 s. Those
   phases never touch TLS. A short, safe form is therefore forcing a workaround:
   the x86_64 path always rebuilds the object. `_tls_relax_object_a64` still
   has that early-out, so aarch64 links probably pay the same penalty
   (unmeasured).
2. The remaining 7.9 s is spread across per-relocation work, with no O(n^2)
   loop left:
   - The relocation prep loop before `elf_apply_jobs` takes about 3 s, from
     `elf_ref_value`, text-keyed `defined` lookups and `ElfScanRef` copies.
   - `operations.relocate` and the write-back take about 1.3 s.
   - `elf_collect_refs` takes 1.8 s and adds 235 MB.
   - The symtab append takes 0.7 s.
   - Section GC takes 0.3 s.

   Per relocation that is about 25 us, against roughly 1 us for lld. The likely
   cause is struct and array access cost in native code
   (`ctx.inputs.objects[oi]...`), not the algorithm.
3. RSS is 1.06 GB, against a target of 500 MB. The prep and apply phases add
   about 480 MB, roughly 4 KB per relocation that is never released. Refs
   collection adds another 235 MB.
4. The jobs=16 parallel path is owned by the concurrency lane.

Target: under 2 s and under 500 MB on this set. Not met yet.
