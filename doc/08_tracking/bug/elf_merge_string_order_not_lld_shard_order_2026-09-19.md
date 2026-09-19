# Internal ELF linker: merged string order is not ld.lld's shard order

- **Filed:** 2026-09-19 (lane C1, `work/lnk-c1`)
- **Status:** OPEN — known, bounded divergence; not a correctness defect
- **Component:** `src/compiler/70.backend/linker/elf/merge_sections.spl`
- **Spec:** `test/01_unit/compiler/backend/linker/elf_merge_strings_spec.spl`

## What is wrong

`ElfLinkRequest.string_merge` (lane C1) implements ld.lld's `-O1` SHF_MERGE
duplicate elimination. The **set** of surviving pieces, the merged size, the
propagated `SHF_MERGE|SHF_STRINGS` flags and `sh_entsize`, and every address a
relocation resolves to all match `ld.lld-23 -O1`. The **byte order inside the
merged blob does not.**

Measured on `test/fixtures/linker/elf/merge_{a,b}_a64.o` (RECIPE.md):

| linker | `.rodata` (0x19 bytes) |
|---|---|
| `ld.lld-23 -O1` | `dup\0only-a\0only-b\0hi\0` |
| internal engine | `hi\0dup\0only-a\0only-b\0` |

Both run and exit 42; with merging off both linkers emit 0x22 bytes and the
program exits 40 (its `_start` adds 2 only when the two objects' `dup\n`
literals share one address), so the dedup decision itself is verified by
execution, not just by size.

## Why

`lld/ELF/SyntheticSections.cpp`, `MergeNoTailSection::finalizeContents`, spreads
the pieces over `constexpr size_t numShards = 32` `StringTableBuilder`s and
concatenates the shards in shard order:

```
size_t shardId = getShardId(sec->pieces[i].hash);      // hash >> (31 - log2(numShards))
...
for (size_t i = 0; i < numShards; ++i) { shards[i].finalizeInOrder(); off += shards[i].getSize(); }
```

and `lld/ELF/InputSection.cpp` `MergeInputSection::splitStrings` sets that hash
to `xxh3_64bits(piece)` truncated to 31 bits. The shard split is therefore
**hash-ordered, not input-ordered**, and is deterministic regardless of
`--threads` (verified: `--threads=1` and `--threads=4` produce identical
bytes). Our engine emits first-appearance order.

## What it would take to close

XXH3-64 in pure Simple (there is only XXH64 in-tree —
`src/lib/nogc_sync_mut/compression/zstd/xxh64.spl`, a different algorithm),
covering at least the 1..16, 17..128 and 129..240-byte paths plus the >240
accumulator loop, including the 64x64->128 multiply folds; then the 32-shard
layout above. Byte-order parity is the only thing this buys — no address,
size or membership changes — so it is filed rather than done, per the lane's
"reject, never mask" rule: the divergence is recorded in the module header,
in the spec header, and here, and nothing claims byte parity.

## Guard

`elf_merge_strings_spec` pins BOTH orders: `sorted_strings(...)` must equal
ld.lld's set, and `sec_strings(...)` must equal our first-appearance order, so
a silent change of either is a failing spec rather than a surprise.
