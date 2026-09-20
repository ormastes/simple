# Stage 3 SCV inventory noncanonical; stage 2 compiler SEGV on struct push

- **Date:** 2026-09-20
- **Status:** OPEN. These are the two blockers left on the FreeBSD QEMU self-host lane after the lane fixes in PR #1141.
- **Area:** the pure-Simple Stage 2 compiler (self-hosted codegen), SCV compile-source inventory (`src/lib/scv/compile_source_inventory.spl`)

## 1. Stage 3 SCV admission: `git-event-apply:inventory-noncanonical`

**Where it was seen:** the FreeBSD 14.4 amd64 QEMU guest (TCG, `-cpu max`, 32 GB RAM). Source was `0d0a78f7cbf` plus the lane fixes. Stage 2 was admitted, and the Stage 3 resume ran with `SIMPLE_SCV_INVENTORY_COLD_INIT=1`.

**What happened:**
- The cold-init inventory ran for about 2.5 h in a single process and peaked at **28.4 GB RSS**. A 16 GB VM OOM-killed it at 12.5 GB.
- It then wrote `build/scv/source-inventory/generations/<sha>.inventory`: generation 16796, 16,796 rows, all rows unique, and every digest a valid 64-hex value.
- Reading that file back failed the round-trip check (`compile_source_inventory_decode_v1`: `encode(decode(file)) != file`), with `inventory-noncanonical`.

**Evidence:** 1,881 adjacent row pairs are not in byte order. For example, `src/app/audit/ffi_analyzer.spl` is stored before `src/app/__init__.spl`, although `_` (0x5F) sorts before `a` (0x61). The encoder sorts with `compile_source_inventory_sort_v1`, an insertion sort using `item.source_identity < sorted[cursor - 1].source_identity` and `sorted[cursor] = sorted[cursor - 1]` over a `[CompileSourceInventoryEntryV1]`. The Stage 2-compiled code therefore produced an order that a second sort does not reproduce.

**Ruled out:** a plain `text <` between two struct fields, or two locals, compiled by the same Stage 2 compiler is bytewise-correct (probe `field-lt: bytewise-ok`, `local-lt: bytewise-ok`). The fault is somewhere else in the sort path, such as array-of-struct element assignment or aliasing.

**Suspected link to the 28 GB peak:** the sort is O(n²), with about 141M comparisons for 16,796 entries. If element stores copy the array, the RSS growth would follow.

## 2. Stage 2 compiler SEGV compiling a struct push

This minimal program crashes the Stage 2 compiler in `native-build`, right after `monomorphize`, with rc 139:

```simple
struct Entry:
    source_identity: text
    n: i64

fn main():
    var items: [Entry] = []
    items = items.push(Entry("a", 1))
    print(items[0].source_identity)
```

It reproduces on:
- the FreeBSD guest's Stage 2 (source `0d0a78f7cbf`, 2026-09-19);
- a **Linux aarch64** Stage 2 built 2026-09-14 (`simple-native1/build/bootstrap-native1a`), in 0.7 s.

It is therefore a general self-hosted-compiler bug, not a FreeBSD one.

## Reproduction (fast, native)

Run from a repo root:

```sh
env SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1 \
  <stage2>/simple native-build --backend llvm --threads 1 --cache-dir /tmp/c \
  --mode dynload -o /tmp/p build/<dir>/main.spl
```

## Update 2026-09-20 12:05 — the sort is NON-DETERMINISTIC

Bug 2 is fixed (PR #1144) and Stage 2 was rebuilt with the fix. Bug 1 survives
unchanged, so the two are independent.

The decisive measurement: two Stage 3 cold-init runs over the **same** tree
produced **different** inventory files — same 6,314,157 bytes and same 16,796
rows, but different content, with **1,881** out-of-order adjacent pairs in the
first run and **1,897** in the second. A deterministic-but-wrong sort would have
produced the same file twice and matched on read-back. It does not.

That is why the read-back fails: `encode(decode(file))` sorts a second time and
reaches a different order than the file holds.

Likely cause, from the same investigation:
`stage2_compiled_program_returned_array_len_zero_2026-09-20.md` records that in
Stage-2-compiled programs a struct's `text` field read out of an array prints a
POINTER rather than the text. If `sorted[cursor - 1].source_identity` yields a
pointer-like value, `<` compares addresses, and the result depends on where the
allocator happened to place each string — non-deterministic between runs, and
partially ordered within one.

The narrow test to write first: build an array of structs holding text, sort it
with `compile_source_inventory_sort_v1`'s exact shape, print each
`entry.source_identity` and the comparison results, and check that reading the
field out of the array yields text, not an address.

## Next steps
- Fix bug 2 with this fixture as the red test, then check whether the same array-of-struct store/alias defect explains bug 1.
- Re-run the FreeBSD Stage 3 resume: `sh scripts/bootstrap/bootstrap-from-scratch.sh --resume-stage3-from-admitted=… --bootstrap-receipt=…` with the checker's env plus `SIMPLE_SCV_INVENTORY_COLD_INIT=1`.
- Size `QEMU_MEM` from the post-fix Stage 3 peak. The current default of 8 GB cannot hold the 28.4 GB measured here.
