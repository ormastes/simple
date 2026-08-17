# Baremetal FreeListAllocator was never callable; BlockHeader overlapped the payload it hands out

- **Date:** 2026-08-08
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **File:** `src/lib/nogc_async_mut_noalloc/baremetal/allocator.spl`
- **Public surface:** re-exported as `std.baremetal.{FreeListAllocator, FixedBlockAllocator, MultiPoolAllocator, BumpAllocator, heap_init, ...}`
  (`src/lib/nogc_async_mut_noalloc/baremetal/__init__.spl:1`,
  `src/lib/nogc_async_mut_noalloc/__init__.spl:96`) and listed as a real
  allocator by the noalloc manifest (`src/compiler/35.semantics/gc_boundary_check.spl:142`,
  `src/compiler/35.semantics/noalloc_checker.spl:109`).

## Defect 1 (FIXED) — `BlockHeader.header_size()` / `.from_addr()` were instance methods called statically

`impl BlockHeader` declared both as `fn` (instance methods), but every call site
invokes them on the class:

- `allocator.spl:174` `val header_size = BlockHeader.header_size()` (in `FreeListAllocator.alloc`)
- `allocator.spl:182` `val header = BlockHeader.from_addr(current)`
- `allocator.spl:233`, `:280` — same, in `dealloc` / `realloc`
- `allocator.spl:237`, `:245`, `:261`, `:265`, `:313` — further `from_addr` call sites

RED, before the fix:

```
SPEC FILE VERDICT: .../probe_spec.spl declared>=1 executed=1 passed=0 failed=1 dropped=0
  ✗ header size
    semantic: unknown static method header_size on class BlockHeader
```

So `FreeListAllocator.alloc`, `.dealloc`, `.realloc` and `heap_init`'s
`global_heap` could never execute — the entire free-list allocator is
non-functional public API.

**Fix:** declare both as `static fn`.

## Defect 2 (FIXED) — header layout overlapped the payload pointer

`BlockHeader` wrote/read `next: u32` at byte offset **+5**:

```
mem_write_u32(addr + 5, self.next)   # occupies bytes 5,6,7,8
```

while `header_size()` reported **8**, and `alloc` returns the payload pointer as
`current + header_size` = `current + 8`. The last byte of `next` and the first
byte of the caller's allocation are therefore the **same address**: the first
byte a caller writes into its own block silently corrupts that block's
free-list link (and `is_free`/`size` of the following block once `next` is
re-read). `next` was also unaligned.

**Fix:** `next` moved to offset **+8**, `header_size()` is now **12**.

## Defect 3 (FIXED) — `capacity - 1` underflows on `u32`

- `FixedBlockAllocator.init`: `while i < self.capacity - 1`
- `MultiPoolAllocator.init_pool`: `while i < capacity - 1`

With `capacity == 0` (reachable in `MultiPoolAllocator.init` whenever
`size / 8 < block_size`, e.g. a heap under 16 KB for the 2048-byte class),
`capacity - 1` wraps to `4294967295` and the link loop runs away writing a
pointer into every `block_size`-strided word across all of memory.

**Fix:** early-return on `capacity == 0` and rewrite the guard as
`while i + 1 < capacity`.

## Related finding (OPEN) — the existing spec tests a reimplementation, not the module

`test/03_system/feature/baremetal/allocator_spec.spl` opens with
`# --- Local stubs (module import doesn't resolve in interpreter mode) ---`
and then re-declares `BumpAllocator`, `FreeListAllocator`,
`FixedBlockAllocator` and `MultiPoolAllocator` as local `struct`s with
different bodies (its `FreeListAllocator.alloc` is a bump allocator with a
module-global free counter; there is no `BlockHeader` at all). All ~40 examples
are green against code that does not exist outside that file — which is exactly
why three defects survived in the real module.

The stated reason is stale: `use std.baremetal.allocator.{...}` **does** resolve
under `bin/simple test` today (verified below). The spec should import the real
module. Not done here to avoid rewriting a 838-line spec owned by another lane;
tracked as follow-up.

## Verification

Engine: `bin/simple test` (tree-walk interpreter). Note the binary currently
prints the Rust-seed banner — this is the known Stage-3 self-host blocker
(`t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`),
so this is **seed evidence**, not self-hosted evidence.

Regression spec: `test/01_unit/lib/baremetal/allocator_block_header_spec.spl`.

- **RED** (pre-fix, ad-hoc probe): `executed=1 passed=0 failed=1 dropped=0`,
  `semantic: unknown static method header_size on class BlockHeader`.
- **GREEN** (post-fix): `executed=2 passed=2 failed=0 dropped=0`.
- **SABOTAGE** (`static fn header_size` → `fn header_size`, fix otherwise
  intact): `executed=2 passed=1 failed=1 dropped=0`, the original
  `unknown static method` message returns. Restored afterwards.

### 2026-08-08 follow-up — closed a tautology gap in the Defect 2 proof

The example "reports a header size that covers the next-pointer field"
(`allocator_block_header_spec.spl`) asserted `header_size().to_i64() ==
12` — a literal compared to a literal, with no dependency on where `next`
is actually read/written. Reverting `next` to offset `+5` while leaving
`header_size()` at `12` (i.e. reintroducing the exact overlap this bug
reports) would leave that example green.

**Fix:** added `BlockHeader.next_offset() -> u32` (returns `8`) and routed
`from_addr`/`write_to_addr` through it instead of the literal `+8`, then
added a new example that derives the check from both static methods:
`next_offset() + 4 <= header_size()`, plus `next_offset() == 8`.

- **SABOTAGE** (`next_offset()` reverted to return `5`, everything else
  intact, run via `bin/simple run
  src/app/test_runner_new/test_runner_single.spl
  test/01_unit/lib/baremetal/allocator_block_header_spec.spl
  --no-session-daemon --sequential`): `Results: 4 total, 3 passed, 1
  failed` — only the new "keeps the next-pointer field fully inside the
  header (no payload overlap)" example fails; the old
  header_size()==12 example stays green, confirming it alone would have
  missed this regression. Restored afterwards.
- **GREEN** (restored): `Results: 4 total, 4 passed, 0 failed`.

This still proves the layout relationship structurally, not via an actual
MMIO write/read round-trip — see "Not verified" below, unchanged.

**Not verified.** Defects 2 and 3 are established by inspection only. They can
only be exercised through `mem_read_u32`/`mem_write_u32`, which lower to
`rt_mmio_*` — raw, unvalidated volatile pointer accesses
(`src/compiler_rust/compiler/src/interpreter_extern/memory.rs:745-808`). A spec
that calls `FreeListAllocator.init()` with the documented `base: 0x20000000`
faults the runner (observed: the whole spec file reports
`error: test-runner: no examples executed`), and the module's addresses are
`u32`, so a hosted `rt_alloc` address cannot be substituted on x86_64. Proving
these end-to-end needs a baremetal target with a real arena.

## 2026-08-08 follow-up — address-width blocker fixed, real-memory verification added

The "Not verified" gap above is closed. Widened every address-flavored field
in `allocator.spl` (`BlockHeader.next`, `base`, `free_list`, `offset`,
`allocated`, `num_blocks`, `capacity`, `block_size`, pool addresses, and the
`mem_*`/`align_up`/`sat_sub` helper signatures) from `u32` to `u64`. Chose this
over an mmap-backed extern or an injectable test backend because:

- Every sibling module in the same directory (`interrupt.spl`, `syscall.spl`,
  `vm_fault.spl`, `tss_syscall.spl`) and the real kernel heap code
  (`os/kernel/memory/heap.spl`, `riscv_noalloc_heap_init`) already use `u64`
  for addresses/base/size — `allocator.spl`'s `u32` was the outlier, not a
  deliberate 32-bit-target convention.
- `allocator.spl`'s public API (`heap_init`, `FreeListAllocator`, etc.) has
  zero callers anywhere else in the tree, so the signature change is
  zero-blast-radius.
- `mmap` is not a registered extern (confirmed) and an injectable backend
  would need to leak host FFI into the `nogc_async_mut_noalloc` tier, which
  its own conventions forbid.

`header_size()` is **unchanged at 16** and `next_offset()` unchanged at 8: with
`next` now `u64` (8 bytes), it occupies bytes 8..16 exactly — what used to be
4 bytes of tail padding is now the high word of the pointer. No new `extern`
was added or Rust runtime code touched: `BlockHeader.next` and the raw
free-list link words `FixedBlockAllocator`/`MultiPoolAllocator` write directly
into memory are stored as two `u32` words via new `mem_read_u64`/
`mem_write_u64` helpers (composed from the existing `rt_mmio_read_u32`/
`rt_mmio_write_u32` externs), not a widened MMIO primitive.

New spec `test/01_unit/lib/baremetal/allocator_real_memory_spec.spl` imports
the real module and drives it with a real host address from `rt_alloc`
(asserted `> 0xFFFFFFFF` to prove it's a genuine 64-bit pointer, not a small
literal that would also have fit the old `u32` width). It re-verifies:

- The free-list split fix (`73e99722000`) over real memory.
- All 3 `sat_sub` sites inside `FreeListAllocator`
  (`dealloc`'s `self.allocated`, `dealloc`'s coalesce-with-next
  `self.num_blocks`, `coalesce_with_prev`'s `self.num_blocks`) — each example
  directly forces the underflow condition (over-dealloc / `num_blocks` preset
  to 0 before a real coalesce fires) rather than only the non-underflowing
  path, and `1000000`-ceiling assertions catch a wraparound to a near-`u64::MAX`
  value.
- `FixedBlockAllocator`'s 2 `sat_sub` sites (`dealloc`, `available`) the same
  way.

Engine: `bin/simple test` (tree-walk interpreter; seed banner present — see
Stage-3 self-host blocker note elsewhere in this repo). Evidence:

- **GREEN** (module intact): `SPEC FILE VERDICT: ...allocator_real_memory_spec.spl
  declared>=7 executed=7 passed=7 failed=0 dropped=0`.
- **SABOTAGE 1** (reverted the split fix — `next_free = new_block_addr` ->
  no-op): the split-path example fails and the runner aborts after 3/7
  examples (`Results: 3 total, 2 passed, 1 failed`), proving the spec reaches
  live module code, not a cached/stale binary.
- **SABOTAGE 2** (`sat_sub` degraded to plain `a - b`): all 4 `sat_sub`-backed
  examples fail (`Results: 7 total, 3 passed, 4 failed`) — including both
  `FreeListAllocator` coalesce sites, which only fail once the test forces
  `num_blocks` toward the actual underflow condition (an earlier draft that
  only exercised the natural non-underflowing coalesce path passed under this
  same sabotage and was strengthened).
- **Restored, GREEN again**: `declared>=7 executed=7 passed=7 failed=0
  dropped=0`.
- Pre-existing regressions unaffected: `allocator_block_header_spec.spl`
  (`Results: 5 total, 5 passed, 0 failed`) and
  `noalloc_family_manifest_regression_spec.spl` (`Results: 4 total, 4 passed,
  0 failed`), the latter confirming the manifest/checker integration (which
  references `heap_init` only by module-path string, not by call) is
  unaffected by the signature widening.

**`test/03_system/feature/baremetal/allocator_spec.spl` (the 838-line
transcription spec) is intentionally left untouched**, same rationale as the
prior lane: rewriting it risks conflicting with whichever lane owns it, and
the new real-memory spec above already satisfies the actual gap that spec's
transcription left open (proving the REAL code against real memory). Not
"the existing spec was upgraded" — a new spec was added alongside it.

**Board-runnable:** unchanged from the original entry below — no QEMU-only
mechanism, no host-only capability was introduced. `mem_read_u64`/
`mem_write_u64` compose the existing `rt_mmio_read_u32`/`rt_mmio_write_u32`
externs, which already round-trip on real MMIO/RAM targets, so the widened
module remains runnable on the physical board, not just the host test harness.

**Board-runnable:** no QEMU-only mechanism is involved; this is a pure
`.spl` library change with no `-kernel` or `isa-debug-exit` dependency.
