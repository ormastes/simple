# M2 — sampled guard pages + hardened debug allocator: insertion-point design

Predecessor: `doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md`
(M2 scope). Builds on M1 attribution (`note_attr_alloc`/`set_current_owner`)
and L6 arena-generation diagnostics. Sources: `interpreter_extern/memory.rs`,
`src/runtime/runtime_memory.c`, `src/compiler_rust/runtime/src/value/heap.rs`,
`src/compiler/10.frontend/core/_AstExpr/nodes.spl` — the generation counter
(`ast_gen_slot`) lives in `nodes.spl`, not `module_state.spl` (lexer-position
slots only; corrected here).

## 1. Sampling hook per alloc path

One shared decision fn, `mem_guard_should_sample(size) -> bool`: 1-in-N via a
relaxed `AtomicU64` counter mod N (never `rand()` — determinism for
fixtures/CI). N from `SIMPLE_MEM_GUARD_RATE` (unset = disabled, §5).

- **Hosted `rt_alloc`** (`interpreter_extern/memory.rs:402`): hook right
  after the `size == 0` check, before `Layout::from_size_align`. On sample,
  branch to `guard_alloc_sampled(size)` (new `interpreter_extern/mem_guard.rs`)
  instead of `alloc_zeroed`; record in a separate `GUARD_SLOTS:
  Mutex<HashMap<usize, GuardSlot>>` (not `HOSTED_ALLOC_SIZES`) so `rt_free`
  (line 429) checks `GUARD_SLOTS` first, falls through to `hosted_free_take`.
- **Native C `rt_alloc`** (`runtime_memory.c:169`): mirror shape —
  `rt_mem_guard_should_sample(size)` (new `runtime_memory_guard.c`) gated
  before `calloc`; sampled pointers skip `rt_transient_raw_register` (guard
  slots are never transient-scope-owned). `rt_free` (line 179) checks
  `rt_mem_guard_is_slot(ptr)` before `rt_transient_raw_erase`.
- **Heap-registry `register_heap_ptr`** (`heap.rs:226`): objects here are
  already boxed by the interpreter's own allocator, so this path can't
  re-page after the fact — hook before `note_heap_alloc` (line 235) and, on
  sample, mark the pointer in a shadow set instead; `unregister_heap_ptr`
  (line 242) checks that set and on a hit runs poison-and-quarantine (§3)
  rather than an immediate free. True page-guarding here is deferred to M6
  (`std.mem.gen_arena`), which can allocate from a page-backed slab directly.

## 2. Guard-slot mechanism (malloc-backed: hosted + native C only)

`GuardSlot { user_ptr, page_base, page_count, size, owner: u32, right_align: bool }`.

- **Layout**: `mmap(NULL, (2+ceil(size/4096))*4096, PROT_READ|WRITE,
  PRIVATE|ANON)`. Page 0 and page N+1 are guard pages, `mprotect(PROT_NONE)`
  always; pages 1..N are usable.
- **Overflow placement**: right-align so the allocation's last byte lands on
  the last byte of the last data page (`user_ptr = page_base +
  PAGE_SIZE*data_pages - size`, GWP-ASan default) — a 1-byte overrun SIGSEGVs
  on the guard page instead of corrupting a neighbor. 1-in-8 samples use
  `right_align=false` (page-aligned start) to catch underflow instead.
- **UAF on free**: `rt_mem_guard_free(ptr)` does not `munmap`; it
  `mprotect(PROT_NONE)`s the whole slot (data pages too) and moves it to the
  quarantine ring (§3) instead of releasing address space, so any later
  read/write anywhere in the slot SIGSEGVs. `munmap` only happens when the
  ring evicts the slot.
- **Owner label on the trap**: a `sigaction`-installed
  `mem_guard_fault_handler` (async-signal-safe: no locks/alloc) binary-searches
  a copy-on-grow `Vec<(page_base, page_end, slot_idx)>` for the faulting
  address and prints size, overflow/underflow/UAF classification, free-site
  if UAF, and the **owner name from M1** — `slot.owner` was captured at alloc
  time from `ATTR_CURRENT_OWNER`, the same id `note_attr_alloc` reads
  (`heap.rs:618`); reuses `owner_report()`'s tab-separated format.

## 3. Quarantine ring (debug allocator, Zig-GPA-style)

Separate from page sampling — the always-on-when-debug-tier path for the
1-(1/N) of allocations NOT page-sampled, giving delayed (not instant) UAF
catch without per-alloc mmap cost.

- `QUARANTINE: Mutex<VecDeque<QuarantineEntry{ptr,size,owner,freed_at}>>`,
  capacity bound by **bytes** (`SIMPLE_MEM_QUARANTINE_BYTES`, default 16 MiB)
  not count, so one large free can't starve the ring.
- On free (debug tier, non-sampled path): `write_bytes(ptr, 0xDE, size)`
  (poison byte per the plan, distinct from the GC's white/gray/black flag
  bits), push onto the ring instead of calling `dealloc`; pop-and-really-free
  from the tail once the byte budget is exceeded (FIFO — oldest is least
  likely still reachable).
- Double free: `hosted_free_take`/`unregister_heap_ptr_checked` already
  refuse a pointer absent from the live map (`heap.rs:266-280`); the debug
  allocator additionally checks `QUARANTINE` on that miss and reports "double
  free of quarantined block, freed at <freed_at>" — a strict upgrade of the
  existing gate, not a new one.
- `mem_guard_looks_poisoned(bytes) -> bool` (a run of 0xDE) lets fixtures
  assert read-after-free without needing a real page fault.

## 4. Index-based arena equivalent (no page guards possible)

Extends L6 (`ast_gen_slot`, `ast_generation_bump()`, `ast_gen_check_index()`
at `nodes.spl:108,309,324`). L6 today is diagnosis-only (one arena-wide
generation, reports "stale" but doesn't block the read). Harden extension,
gated separately (`SIMPLE_AST_GEN_HARDEN=1`, debug-tier default):

- **Per-slot generation**: add `expr_slot_gen: [i64]` (mirrors
  `expr_tag`/`expr_left` at `nodes.spl:90-98`); `expr_alloc` stamps
  `expr_slot_gen[idx] = ast_generation()` at mint — the same value already
  threaded as `minted_gen` into `ast_gen_check_index`, now persisted per-slot.
- **Slot poison on recycle**: index arenas don't `free()`, they push the
  index onto a free-list. On recycle, write `expr_tag[idx] = TAG_POISON` (a
  tag value outside the live enum range) so a reader that skips the
  generation check still fails a *type* check instead of reading recycled
  data.
- **Delayed index reuse**: free-list pop moves from LIFO (worst case for
  catching stale reads) to a bounded FIFO delay window
  (`SIMPLE_MEM_ARENA_DELAY_SLOTS`, e.g. hold back the most-recent 64) — §3's
  quarantine idea, applied to indices.
- **Generation check on every deref**: promote `ast_gen_check_index` from a
  few probe sites to the actual read gate in `expr_owner_tag`/
  `expr_owner_left`/etc. (`nodes.spl:272-283`) under
  `SIMPLE_AST_GEN_HARDEN=1`, comparing `expr_slot_gen[idx]` against a
  `NodeRef{idx,gen}` pair threaded through the parser/HIR reader (debug-tier
  only; release keeps the bare `i64`). No `mprotect` here — an AST node isn't
  a page-aligned OS allocation; the analogous trap is type-poison +
  generation-mismatch instead of SIGSEGV.

## 5. Config gates (zero-overhead-when-off, hard rule)

Every gate is a cached `OnceLock<bool>` read once at start (mirrors
`heap.rs:546-551` `ATTR_ENABLED`, `nodes.spl:314-319`
`ast_gen_check_enabled`) — never a per-alloc env read:

| Feature | Env | Default | Off-path cost |
|---|---|---|---|
| Guard-page sampling | `SIMPLE_MEM_GUARD_RATE=N` | disabled | one atomic add+compare |
| Quarantine + poison | `SIMPLE_MEM_HARDEN=1` | off | one bool check before existing free |
| Arena gen-harden | `SIMPLE_AST_GEN_HARDEN=1` | off (L6's own `SIMPLE_AST_GEN_CHECK` diagnostic stays independent) | no `NodeRef` widening |
| GC-sweep poison | `SIMPLE_MEM_HARDEN=1` (shared) | off | skips memset in sweep loop |

`--mem-infra=harden[,guard=N]` (M3) becomes the CLI alias once M3 lands;
these envs are load-bearing now, same pattern as `SIMPLE_MEM_ATTR` (M1).
Debug-tier builds may default `SIMPLE_MEM_HARDEN`/`SIMPLE_AST_GEN_HARDEN` on
via the build profile (not a compiled-in branch), per the plan's
"debug-tier-default, individually disableable" clause — release stays
byte-identically zero-cost.

## 6. Test plan (seeded fixtures, one per model)

New `test/03_system/runtime/memory_analysis/`, SSpec style:

1. `guard_malloc_overflow_spec.spl` — `SIMPLE_MEM_GUARD_RATE=1`, `rt_alloc(37)`,
   write one byte past end; subprocess assert non-zero exit/SIGSEGV and
   stderr contains the owner set via `rt_mem_attr_set_owner`.
2. `guard_malloc_uaf_spec.spl` — alloc, free, read the freed pointer; assert
   trap (guard slots are `PROT_NONE`, not poisoned bytes — distinct from #3).
3. `harden_quarantine_uaf_spec.spl` — `SIMPLE_MEM_HARDEN=1`,
   `SIMPLE_MEM_GUARD_RATE=0`: alloc, free, read in-process (delay not
   page-protect, no crash); assert `mem_guard_looks_poisoned()`; separately
   assert double-free reports "double free of quarantined block".
4. `arena_stale_slot_spec.spl` — `SIMPLE_AST_GEN_HARDEN=1`: mint a node,
   capture `(idx, gen)`, bump generation + recycle `idx`, read through the
   stale pair; assert refusal (type-poison or gen-mismatch), not garbage.
5. `gc_sweep_poison_spec.spl` — debug tier: allocate, drop refs, force a
   sweep, assert the freed region reads poisoned before reuse (plan's
   "poison on sweep in debug tier" clause).
6. `guard_and_harden_overhead_spec.spl` — perf gate: representative compile
   with all M2 envs unset, wall time + RSS within noise of the M1 baseline —
   exit-criteria proof, not a defect fixture.

Owner attribution on every trap reuses M1 directly
(`interpreter_extern/memory.rs:98`, `heap.rs:591-611`) — no new plumbing,
only new consumers of the existing owner id at fault-report time.

## Status: native-C quarantine + poison portion (§3, `runtime_memory.c`)

Landed: `SIMPLE_MEM_HARDEN=1` gated (getenv checked once into a static
cached int), `rt_alloc`/`rt_free` in `src/runtime/runtime_memory.c` mirror
the hosted quarantine ring — 64-slot fixed FIFO of `{user_ptr, base_ptr,
size}`, `rt_free` poisons with `0xDE` and defers the real `free()` to ring
eviction, double-free of a still-quarantined pointer is refused (no-op),
and `rt_mem_harden_check_native()` scans the ring for non-`0xDE` bytes and
returns the tampered-block count. No `.spl` caller wired (adding new `rt_*`
externs needs a bootstrap rebuild, out of scope here) — C-level only.
Verified: standalone `cc -Wall -Wextra` (clean) and
`-fsanitize=address,undefined` builds of
`src/runtime/test/rt_mem_harden_selfcheck.c` + `runtime_memory.c`, run in
both off- and on-modes (poison-on-free, refused double-free, UAF tamper
detection, >64-alloc ring-eviction churn all pass, 0 failures, exit 0);
plus `cargo build -p simple-runtime` (which compiles this file via
`build.rs`) still builds clean with no new warnings. Guard-page sampling
(§1-§2) and the arena-generation harden extension (§4) are NOT part of
this lane.
