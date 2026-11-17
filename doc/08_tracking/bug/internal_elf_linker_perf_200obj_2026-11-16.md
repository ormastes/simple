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
| round 2 (Result-free per-reloc paths) | 4498 | 820 MB | byte-identical |
| ld.lld / mold (WSL) | 120 / 100 | 68 MB / 7 MB | - |

Round 2: the per-relocation helpers returned `Result`, which costs about 5 us
and leaks per call natively (`native_result_call_cost_2026-11-16.md`).
`elf_symref` is now infallible (error as `SYMREF_ERR`), the collect place is
inlined, and the prep loop and local symtab rows use `elf_ref_value_fast` /
`elf_in_vaddr_fast` with a Result fallback. Phases: refs 1.8 s -> 0.42 s,
relocated (prep + apply) 4.3 s -> 2.1 s, symtab 0.73 s. RSS is pinned by
`test/05_perf/compiler/linker/elf_link_rss_budget.shs` (ratchet 850000 KiB).
The prep loop's symbol resolution is precomputed by `elf_ref_values_fast`, which shards per ref range through `elf_par` (worker `elf_prep_worker`); on ca081c452a2 at jobs=16 relocated drops to 1.86 s (apply 0.81 s), output byte-identical, peak 1.14 GB. The remaining serial prep (~1 s) is the per-ref loop body and job encoding.
Turning `ElfStaticInputs`/`ElfLinkCtx`/`ElfLayout` into classes measured
4137 ms / 675 MB but was left out: the parallel path shares ctx through a
global, and that path belongs to the concurrency lane.

Fixed: x86_64 `_tls_relax_object` called `_tls_is_pair(obj, i)` for every
non-TLS relocation. Each call scanned every relocation in the object, and for
each TLS head it ran another full pair scan. The phase took 21.5 s and grew RSS
by 9.1 GB. Pair members are now computed once per object (`_tls_pair_members`),
and the phase takes 18 ms.

## Open

1. Resolved in round 2. Re-adding the `return Ok(obj)` early-out on the
   round-2 tree measured 4413 ms / 799 MB against 4498 ms / 820 MB without it:
   no slowdown. The earlier 5-32x was the Result-call cost interacting with
   the shared object, gone with the Result-free paths. aarch64's early-out
   is therefore fine. x86_64 still rebuilds because an empty pair set does not
   rule out unpaired heads that must be rejected.
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

5. Remaining after round 2 (4.5 s / 820 MB): serial apply calls the sealed
   `operations.relocate` (Result) and allocates two windows per relocation;
   symtab does ~4 text-keyed dict ops per symbol over 81k symbols; refs keep a
   `"global:"+name` key text per relocation (~1 KB/reloc retained in collect,
   ~1.5 KB/reloc in prep+apply).

6. Round 3 (2026-11-17, verification-pending): the apply loops (serial,
   `elf_apply_worker`, non-deferred) call `ElfSealedOperationsV1.relocate_fast`
   first. It is Result-free, runs `reloc_apply` once (`reloc_patch_value`), and
   is live only on operations from `elf_builtin_*operations_v1`, so a caller's
   relocation callback is never bypassed; a reject or custom operation falls
   back to `relocate` and its error text. Symtab uses `elf_entry_addr_fast` and
   calls `elf_symtab_address` only for STT_TLS. On a regenerated 200-object set
   (100 fns x 200 files, clang -O1 -fno-pic), same session, Windows native,
   jobs=1: 4706-5167 ms / 742 MB -> 3392-3407 ms / 717 MB, image
   byte-identical; relocated 1.47 s -> 0.68 s, symtab 1.55 s -> 0.97 s.
   RSS ratchet lowered to 750000 KiB. Remaining symtab cost is text-keyed dict
   work, and RSS is dominated by per-ref key texts (item 5), not Result.

Target: under 2 s and under 500 MB on this set. Not met yet.
