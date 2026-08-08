# Baremetal FreeListAllocator was never callable; BlockHeader overlapped the payload it hands out

- **Date:** 2026-08-08
- **Status:** FIXED (three defects), one related finding left OPEN
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

**Not verified.** Defects 2 and 3 are established by inspection only. They can
only be exercised through `mem_read_u32`/`mem_write_u32`, which lower to
`rt_mmio_*` — raw, unvalidated volatile pointer accesses
(`src/compiler_rust/compiler/src/interpreter_extern/memory.rs:745-808`). A spec
that calls `FreeListAllocator.init()` with the documented `base: 0x20000000`
faults the runner (observed: the whole spec file reports
`error: test-runner: no examples executed`), and the module's addresses are
`u32`, so a hosted `rt_alloc` address cannot be substituted on x86_64. Proving
these end-to-end needs a baremetal target with a real arena.

**Board-runnable:** no QEMU-only mechanism is involved; this is a pure
`.spl` library change with no `-kernel` or `isa-debug-exit` dependency.
