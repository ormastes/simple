# mimalloc + mold Pure-Simple Completion Plan

**Date:** 2026-05-07
**Status:** Architecture phase — milestones defined, implementation pending
**Related research:** `doc/01_research/domain/mold_linker_analysis.md`
**Related design:** `doc/05_design/mold_mimalloc_compatibility_surface.md`, `doc/05_design/mold_bundling_plan.md`

---

## Scope Decision

### mimalloc

The existing `src/lib/nogc_sync_mut/mimalloc.spl` (695 lines) is a real
implementation using a `[u8]` mock-pointer representation. The goal is to
progressively close the gap to upstream mimalloc semantics while keeping the
public API surface stable.

MDSOC+ does **not** apply here. mimalloc is infrastructure (allocator library),
not a userland service. The kernel heap path (`src/os/kernel/memory/heap.spl`)
stays MDSOC-only.

### mold

The existing `src/compiler/70.backend/linker/mold.spl` (613 lines) is a
complete external-delegation wrapper. `doc/01_research/domain/mold_linker_analysis.md`
§ 9.3 explicitly recommends **against** building a custom linker in Simple.

Two tracks are defined below:

- **Track A (recommended):** Wrapper hardening and ELF read-only inspection for
  compiler diagnostics. Low effort, high value, no scope risk.
- **Track B (contingent):** Pure-Simple ELF linker. Gated on an explicit scope
  decision and an estimated 4–6 month effort budget. Not started.

---

## mimalloc Milestones

### mimalloc M1 — Quick Wins + TLS Foundation

**Target files:**
- `src/lib/nogc_sync_mut/mimalloc.spl` (modify)
- `src/lib/nogc_sync_mut/mimalloc_tls.spl` (new)

**New structs / traits:**
- `MiThreadHeap` — per-thread heap handle wrapping a `ThreadLocal<MiHeap>`
- `MiTlsRegistry` — module-level registry mapping thread handle → `MiHeap`

**Key functions (signatures only):**
```
fn _size_class_index(size: usize) -> usize          # replace / with >>
fn mimalloc_thread_init() -> MiThreadHeap
fn mimalloc_thread_heap() -> MiHeap
fn mimalloc_thread_destroy()
fn mi_heap_new_thread() -> MiHeap                   # independent arena, not global shim
```

**Dependencies:**
- `std.nogc_sync_mut.mimalloc` → `std.compiler_rust.lib.std.infra.synchronization` (for `ThreadLocal<T>`, `rt_thread_local_*`)
- No new external runtime externs needed — `rt_thread_local_new/get/set/free` already exist

**Tasks:**
1. Remove L15 division workaround (`/ 4` → `>> 2`), run all mimalloc tests — hours
2. Add `MiThreadHeap` + `mimalloc_tls.spl` with `ThreadLocal<MiHeap>` backing
3. Update `mi_heap_new` to create an independent heap instead of returning the global heap
4. Add tests: per-thread heap isolation, `mimalloc_thread_destroy` reclaims

**Estimated effort:** 2–3 days

---

### mimalloc M2 — Delayed/Xthread Free + Page Policy

**Target files:**
- `src/lib/nogc_sync_mut/mimalloc.spl` (modify)
- `src/lib/nogc_sync_mut/mimalloc_page_policy.spl` (new)

**New structs / traits:**
- `MiDelayedFreeList` — MPSC list of cross-thread free requests
- `MiPagePolicy` — enum: `Commit | Decommit | Reset | Purge`
- `OsPageOp` — enum passed to the `os_page_alloc` hook for decommit/recommit

**Key functions:**
```
fn mi_free_delayed(ptr: [u8], heap_id: usize)       # cross-thread enqueue
fn _drain_delayed_free(heap: MiHeap)                 # called at alloc time
fn mi_page_decommit(page: MiPage, policy: MiPagePolicy)
fn mi_page_recommit(page: MiPage) -> bool
fn mimalloc_set_page_policy(policy: MiPagePolicy)
```

**Dependencies:**
- `mimalloc_tls` (from M1) — needs per-thread heap to route delayed frees
- `std.nogc_async_mut.actor_heap` — reference only (design contrast, no import)
- OS page provider hook (already present via `mimalloc_set_os_page_alloc`)

**Tasks:**
1. Extend `os_page_alloc` hook signature to carry `OsPageOp` (decommit/recommit)
2. Implement `MiDelayedFreeList` as atomic-linked list of `usize` heap IDs
3. Implement `_drain_delayed_free` called at each allocation fast path
4. Add `MiPagePolicy` enum + `mi_page_decommit`/`mi_page_recommit`
5. Tests: cross-thread free drains, decommit reduces `mi_raw_allocated`

**Estimated effort:** 3–5 days

---

### mimalloc M3 — Abandon/Collect + Secure Mode + Aligned Metadata

**Target files:**
- `src/lib/nogc_sync_mut/mimalloc.spl` (modify)
- `src/lib/nogc_sync_mut/mimalloc_secure.spl` (new)

**New structs / traits:**
- `MiAbandonedList` — segments abandoned by exited threads, available for reuse
- `MiGuardPage` — metadata for guard-page secure allocation
- `MiAllocMeta` — `usize` address + alignment + size, returned alongside `[u8]` for raw paths

**Key functions:**
```
fn mi_segment_abandon(seg: MiSegment)
fn mi_segment_collect_abandoned() -> i64            # returns count reclaimed
fn mi_collect_full(heap: MiHeap)                    # implements mi_collect hook
fn mi_malloc_secure(size: usize) -> [u8]            # guarded allocation
fn mi_malloc_raw_aligned(size: usize, align: usize) -> MiAllocMeta
```

**Dependencies:**
- `mimalloc_tls` (M1) — thread exit triggers `mi_segment_abandon`
- `mimalloc_page_policy` (M2) — abandoned segment decommit uses page policy
- Compiler runtime: `[u8]` → raw-pointer bridging blocked until language-level
  raw pointer representation is available; `MiAllocMeta` is an interim wrapper

**Blocked by:**
- True aligned-address verification requires raw pointer return from `mi_malloc`.
  `MiAllocMeta` provides a partial solution (usize address + alignment stored
  alongside the `[u8]`); full ABI parity deferred until language supports raw
  pointer types.

**Tasks:**
1. Implement `MiAbandonedList` (global list, protected by atomic swap)
2. Implement `mi_collect_full` — drains abandoned list, calls `mi_page_decommit`
3. Implement `mi_malloc_secure` — sandwiches allocation with guard pages via hook
4. Add `MiAllocMeta` and `mi_malloc_raw_aligned` as the aligned-metadata surface
5. Tests: collect reduces segment count, secure mode allocates/frees cleanly

**Estimated effort:** 5–7 days

---

## mold Milestones

### Track A (Recommended) — Wrapper Hardening + ELF Inspector

#### mold A-M1 — Wrapper Robustness

**Target files:**
- `src/compiler/70.backend/linker/mold.spl` (modify)

**Tasks:**
1. Add structured error types for linker failure: `LinkerError` enum with variants
   `NotFound`, `ExitFailure(i64)`, `Timeout`, `UnsupportedTarget`
2. Add `MoldDiagnostic` struct: linker stderr line parser returning structured
   diagnostics instead of raw text
3. Harden `write_elf_object`: detect GNU `as` absence and return
   `LinkerError::NotFound` instead of panic/silent failure
4. Tests: verify `SIMPLE_LINKER` alias table is complete; verify bundled binary
   priority over system binary

**Estimated effort:** 1–2 days

---

#### mold A-M2 — ELF Read-Only Inspector (Diagnostics)

**Target files:**
- `src/compiler/70.backend/linker/elf_inspect.spl` (new)
- `src/compiler/70.backend/linker/mold.spl` (modify — add diagnostic hook)

**New structs / traits:**
- `ElfHeader` — fields: `e_type`, `e_machine`, `e_entry`, `e_phoff`, `e_shoff`
- `ElfSectionHeader` — `sh_name`, `sh_type`, `sh_flags`, `sh_addr`, `sh_size`
- `ElfSymbol` — `st_name`, `st_value`, `st_size`, `st_info`, `st_shndx`
- `ElfInspector` — wraps `[u8]` buffer, provides section/symbol iteration
- `ElfInspectError` — enum: `TooShort`, `BadMagic`, `UnsupportedClass`, `UnsupportedEndian`

**Key functions:**
```
fn elf_inspect_open(bytes: [u8]) -> ElfInspector | ElfInspectError
fn elf_inspect_sections(insp: ElfInspector) -> [ElfSectionHeader]
fn elf_inspect_symbols(insp: ElfInspector) -> [ElfSymbol]
fn elf_inspect_entry(insp: ElfInspector) -> usize
```

**Dependencies:**
- No external deps — pure `[u8]` slice parsing
- `symbol_analysis.spl` (read-only reference for naming conventions)

**Estimated effort:** 3–5 days

---

#### mold A-M3 — ELF Inspector Integration + `mold_pure_spec` Cleanup

**Target files:**
- `test/unit/compiler/mono/mold_pure_spec.spl` (modify — replace placeholder)
- `src/compiler/70.backend/linker/mold.spl` (modify — call inspector for diagnostics)

**Tasks:**
1. Remove placeholder `it "skipped"` from `mold_pure_spec.spl`
2. Add real tests using `ElfInspector` against a known ELF fixture (linker output
   or a synthetic header constructed from `[u8]`)
3. Wire `ElfInspector` into `MoldBackend` post-link diagnostic check
4. Tests: bad magic, section count, symbol table presence

**Estimated effort:** 1–2 days

---

### Track B (Contingent) — Pure-Simple ELF Linker

**Status: NOT STARTED. Gated on explicit scope approval.**
**Estimated total effort: 4–6 months (one engineer).**

The research analysis (`doc/01_research/domain/mold_linker_analysis.md` § 9.3)
recommends against this due to complexity and maintenance cost. Track B should
only be approved if the project requires elimination of all external tool
dependencies at link time (e.g., fully self-hosted SimpleOS bootstrap without
GNU binutils).

#### mold B-M1 — Pure-Simple ELF Parser (Read + Write)

**Target files:**
- `src/compiler/70.backend/linker/elf_parser.spl` (new — superset of `elf_inspect.spl`)
- `src/compiler/70.backend/linker/archive_parser.spl` (new)

**New structs:**
- `ElfObject` — parsed ELF: sections, symbols, relocations, string tables
- `ElfRelocation` — `r_offset`, `r_info`, `r_addend`
- `ArObject` — archive member: name, data slice
- `ArReader` — iterates `!<arch>` archive members

**Estimated effort:** 4–6 weeks

---

#### mold B-M2 — Symbol Resolution + Relocation Engine

**Target files:**
- `src/compiler/70.backend/linker/sym_resolver.spl` (new)
- `src/compiler/70.backend/linker/reloc_engine.spl` (new)

**New structs:**
- `SymTable` — interned symbol name → `SymEntry` (defined/undefined, weak/strong)
- `SymEntry` — `section_idx`, `offset`, `size`, `binding`
- `RelocTarget` — resolved target address + addend
- `RelocEngine` — applies x86_64/aarch64/riscv32/riscv64 relocation formulas

**Estimated effort:** 6–10 weeks

---

#### mold B-M3 — ELF Output + Linker-Script Basics + Mach-O/COFF (Stretch)

**Target files:**
- `src/compiler/70.backend/linker/elf_writer.spl` (new)
- `src/compiler/70.backend/linker/linker_script.spl` (new)
- `src/compiler/70.backend/linker/macho_parser.spl` (new — stretch)
- `src/compiler/70.backend/linker/coff_parser.spl` (new — stretch)

**Estimated effort:** 8–16 weeks (includes Mach-O/COFF stretch)

---

## Module Dependency Map

```
mimalloc.spl
  └─> mimalloc_tls.spl (M1)
        └─> synchronization.spl [ThreadLocal<T>]
  └─> mimalloc_page_policy.spl (M2)
        └─> mimalloc_tls.spl
  └─> mimalloc_secure.spl (M3)
        └─> mimalloc_page_policy.spl

mold.spl
  └─> elf_inspect.spl (A-M2)
  └─> elf_parser.spl (B-M1, superset of elf_inspect)
        └─> archive_parser.spl (B-M1)
  sym_resolver.spl (B-M2)
        └─> elf_parser.spl
  reloc_engine.spl (B-M2)
        └─> sym_resolver.spl
  elf_writer.spl (B-M3)
        └─> reloc_engine.spl
  linker_script.spl (B-M3)
        └─> elf_writer.spl
```

No circular dependencies.

---

## Architecture Decisions

**D-1: Track A before Track B for mold** — The research analysis explicitly
recommends against a custom linker. Track A delivers immediate value
(diagnostics, error handling) with minimal risk. Track B requires a stakeholder
scope decision before any implementation begins.

**D-2: `MiAllocMeta` as interim aligned-address surface** — True address-aligned
allocation requires raw pointer returns from `mi_malloc`. Until the language
supports raw pointer types, `MiAllocMeta` (usize address + alignment field stored
alongside `[u8]`) provides a typed bridge for kernel/driver callers via
`mi_malloc_raw_aligned`. Public `[u8]` API is unchanged.

**D-3: `ThreadLocal<MiHeap>` for per-thread heaps** — `rt_thread_local_*` externs
already exist. `mimalloc_tls.spl` wraps them in `MiThreadHeap` typed over
`MiHeap`. No new compiler/runtime externs needed for M1.

**D-4: MPSC delayed-free list, not lock** — Cross-thread free enqueues to an
atomic-linked MPSC list. Drain happens at allocation time on the owning thread.
This matches upstream mimalloc's design and avoids locking on the free path.

**D-5: ELF inspector (`elf_inspect.spl`) is separate from ELF parser (`elf_parser.spl`)** —
The inspector (Track A) is read-only, diagnostic-focused, and shallow (~100 lines).
The parser (Track B) is a full round-trip parser required for linking. Keeping
them separate allows Track A to ship without Track B commitment.

**D-6: MDSOC+ not applicable** — mimalloc and mold are compiler infrastructure,
not userland services. MDSOC+ applies only to userland apps/services.

---

## Requirement Coverage

| Requirement | Covered by |
|---|---|
| REQ-1 (mimalloc API status table) | Captured in state file §2-research; this doc §mimalloc milestones |
| REQ-2 (aligned-address limitation documented) | D-2, M3 blocked-by note, `MiAllocMeta` design |
| REQ-3 (mold component status table) | Captured in state file §2-research; this doc §mold Track A |
| REQ-4 (mold scope clarification) | Scope Decision section; Track A vs Track B; D-1 |
| REQ-5 (fix mold_pure_spec.spl placeholder) | mold A-M3 |
| REQ-6 (end-to-end linking test) | mold A-M3 (ELF inspector tests against linker output) |
| REQ-7 (mimalloc gap list) | M1 (TLS + >> fix), M2 (delayed/xthread + page policy), M3 (abandon/collect/secure) |
| REQ-8 (mold gap list + scope decision) | Track A (wrapper + ELF inspect), Track B (gated) |
| REQ-9 (completion plan doc) | This document |

---

## Prioritized Execution Order

1. **mimalloc M1** — Quick wins (>> fix) + TLS foundation (2–3 days)
2. **mold A-M1** — Wrapper error handling (1–2 days)
3. **mold A-M2** — ELF inspector (3–5 days)
4. **mold A-M3** — `mold_pure_spec` cleanup (1–2 days)
5. **mimalloc M2** — Delayed/xthread free + page policy (3–5 days)
6. **mimalloc M3** — Abandon/collect + secure + aligned metadata (5–7 days)
7. **mold Track B** — Only after explicit scope approval (4–6 months)

Total Track A effort estimate: ~15–24 days
