# SimpleOS VMM Consolidation Plan

**Date:** 2026-08-06
**Status:** plan only — no kernel code changed by this document.
**Trigger:** `doc/08_tracking/bug/simpleos_vmm_kernel_pml4_phys_reads_zero_after_init_2026-08-06.md`
(fix `4575b4ce88d`, `vmm_publish_kernel_pml4()`, +35 lines). That fix is a
bridge across the split, not the cure for the split.
**TLDR:** `vmm_consolidation_plan_tldr.md`

---

## 0. Executive summary

x86_64 SimpleOS has **two page-table implementations that both call themselves
`[VMM]` on the serial console**:

| | module | role today |
|---|---|---|
| **A (arch)** | `src/os/kernel/arch/x86_64/paging.spl` (531 lines) | **builds** the kernel page tables at boot. Owns `g_vmm`. Reached via `hal_paging_init` → `arch_adapt/x86_64/paging.spl:paging_init` → `X86Paging.init` → `vmm_init` (`:215`). |
| **B (portable core)** | `src/os/kernel/memory/vmm_core.spl` (555 lines) | **mutates** those page tables at runtime. Owns `_vmm_pml4_phys` / `_vmm_hhdm_offset`. Every syscall/heap/DMA/COW mapping goes through `vmm_map_page` here. Its own `vmm_init*` has **zero callers**. |

The two halves each hold their own copy of the same two pieces of state
(`pml4_phys`, `hhdm_offset`) and each has its own `_phys_to_virt`,
`_alloc_table_page`, `_ensure_table_entry`, `_flags_to_pte_bits`, `_load_cr3`,
`_read_cr3`, `PTE_*` constant block, and `_identity_map_4gb`. **A writes its
copy; B is read by everyone.** The PML4 defect was that nothing bridged them.

The bridge now exists. What remains is that **the code that builds the tables and
the code that edits the tables are two different modules with two different
state copies, two different CR3 externs, and identical log output.** Any future
edit to one silently diverges from the other.

**Recommendation: B (`vmm_core.spl`) survives.** A's mapping surface is retired —
two of its three entry points are provably dead and the third is reached only by
specs (§1.2), so it is repointed at B rather than deleted. A shrinks to a
boot-time constructor that delegates into B. Rationale in §4.

---

## 1. Symbol table — defined where, called from where, live/dead

Liveness is **three-way**: `LIVE` = reached from the kernel boot/syscall path;
`TEST` = referenced only from `test/**` (this is the category that let the
defect survive — the tested implementation was not the shipped one); `DEAD` =
no reference outside its own defining file.

Method: repo-wide bare-symbol grep over `src/**` + `test/**` with the defining
file excluded, so `use`-list re-exports and `module.symbol` qualified calls are
both caught. The native-build closure tracer does **not** follow `export use`
shims, so grep — not the tracer — is authoritative here.

### 1.1 `src/os/kernel/memory/vmm_core.spl` (implementation B)

| symbol | kind | referenced from | verdict |
|---|---|---|---|
| `vmm_kernel_pml4_phys` | fn | `vmm_address_space.spl`, `vmm_copy.spl` | **LIVE** (the defect's read side) |
| `vmm_publish_kernel_pml4` | fn | *(written by `arch/x86_64/paging.spl` only — the bridge)* | **LIVE** (single caller, cross-impl) |
| `vmm_map_page` | fn | `heap.spl`, `memory_owned_pages.spl`, `vmm_address_space.spl`, `ipc/syscall.spl`, `ipc/syscall_device.spl`, `ipc/syscall_memory.spl`, `arch/x86_64/host_gpu_ivshmem_vmm.spl` + 11 specs | **LIVE** (the real mapping path) |
| `vmm_unmap_page` | fn | `memory_dma_pages.spl`, `ipc/syscall*.spl`, `lifecycle/task_cleanup.spl`, `host_gpu_ivshmem_vmm.spl` | **LIVE** |
| `vmm_read_pte` | fn | `vmm_copy.spl`, `ipc/syscall.spl`, `ipc/syscall_memory.spl`, `task_cleanup.spl` | **LIVE** |
| `vmm_translate` | fn | `vmm_copy.spl` (+5 specs) | **LIVE** |
| `vmm_active_root` | fn | `memory_leveling_runtime.spl`, `memory_leveling_vmm.spl`, `memory_owned_pages.spl`, `memory_swap_coordinator.spl`, `memory_swap_runtime.spl` | **LIVE** |
| `vmm_manager_snapshot` | fn | `vmm_address_space.spl:392` (`vmm_get_manager`) | **LIVE** |
| `vmm_phys_to_virt` | fn | `memory_leveling_vmm.spl` | **LIVE** |
| `g_next_as_id` | var | `vmm_address_space.spl`, `vmm_vma.spl` | **LIVE** (address-space id counter) |
| `_vmm_pml4_phys`, `_vmm_hhdm_offset`, `g_vmm_initialized` | var | in-file + written by the bridge | **LIVE** |
| `_phys_to_virt`, `_alloc_table_page`, `_ensure_table_entry`, `_read_pte`, `_write_pte`, `_pte_is_present`, `_pte_phys_addr`, `_pml4_index`/`_pdpt_index`/`_pd_index`/`_pt_index`, `_flags_to_pte_bits`, `_load_cr3`, `_read_cr3`, `_vmm_invalidate_tlb` | fn | imported wholesale by `vmm_address_space.spl:11-20` and `vmm_copy.spl:8-14` | **LIVE** (private-by-name, public in practice) |
| `PTE_*`, `PAGE_SIZE`, `ENTRIES_PER_TABLE` | val | `vmm_address_space.spl`, `vmm_copy.spl`, `vmm_vma.spl` | **LIVE** |
| `vmm_activate` | fn | `arch/riscv64/paging.spl` only | **LIVE (riscv64 only)** — never on the x86_64 path |
| `vmm_init` (`:299`) | fn | **none** | **DEAD** |
| `vmm_init_from_global_pmm` (`:308`) | fn | **none** | **DEAD** |
| `_identity_map_4gb` (`:356`) | fn | only from dead `vmm_init_from_global_pmm` | **DEAD** |
| `g_vmm` (`:173`) | var | *imported* by `vmm_address_space.spl:14` and `vmm_copy.spl:11` but **never read in either file** | **DEAD** (dead import — grep for `g_vmm.` in both: zero field accesses) |
| `vmm_bootstrap_pml4_entry0` / `_pdpt_entry0` / `_pd_entry0` | fn | **none** | **DEAD** |
| `_vmm_fallback_cr3`, `rt_read_cr3__fallback`, `rt_write_cr3__fallback` | var/fn | in-file only (host-test CR3 shim) | **TEST-only** |
| `vmm_init_sparse_for_test` | fn | 5 specs under `test/02_integration/os/` | **TEST** |
| `vmm_set_map_failure_after_for_test`, `vmm_clear_map_failure_for_test`, `_vmm_test_fail_map_after`, `_vmm_test_map_attempts` | fn/var | `memory_leveling_pmm_syscall_effects_spec.spl` | **TEST** |
| `VMM_KERNEL_SPACE_START` (per-`@cfg` arch), `VMM_VMA_*`, `VMM_MAX_VMAS`, `VMM_U64_MAX` | val | `vmm_vma.spl`, `vmm_shared.spl` | **LIVE** |

### 1.2 `src/os/kernel/arch/x86_64/paging.spl` (implementation A)

| symbol | kind | referenced from | verdict |
|---|---|---|---|
| `X86Paging` (struct + impl) | struct | `arch/x86_64/mod.spl`, `arch_adapt/x86_64/mod.spl`, `arch_adapt/x86_64/paging.spl` | **LIVE** |
| `vmm_init` (`:215`) | fn | `X86Paging.init` | **LIVE — the only init that actually runs on x86_64** |
| `_identity_map_4gb` (`:249`) | fn | `vmm_init` | **LIVE** |
| `g_vmm` (`:140`) | var | in-file: `_phys_to_virt`, `vmm_create_address_space`, `vmm_get_manager` | **LIVE** — this is the copy that holds the real root |
| `vmm_create_address_space` (`:373`) | fn | `X86Paging.create_address_space` ← `paging_create_address_space` ← `hal.spl:hal_paging_create_address_space`, which has **zero references anywhere** — the HAL is the only route in, and nothing uses it | **DEAD** (see the asymmetry note below; shadowed by `vmm_address_space.spl:34` — D5) |
| `vmm_switch_address_space` (`:397`) | fn | `X86Paging.switch_address_space` ← `paging_switch_address_space`, imported **directly from the adapter** by `vmm_address_space.spl:21`, bypassing `hal.spl` | **LIVE** |

> **The asymmetry is the interesting part.** `vmm_switch_address_space` and
> `vmm_create_address_space` are twins in the same module with the same HAL
> plumbing, yet one is live and one is dead — because `vmm_address_space.spl:21`
> reaches `paging_switch_address_space` through an **adapter side-door that skips
> `hal.spl` entirely**, while `create_address_space` has only the HAL route and
> nothing walks it. So A's page-table *construction* half is dead while its CR3
> *switch* half is load-bearing. Any liveness claim about this module that doesn't
> distinguish the two routes is unreliable.
| `vmm_get_manager` (`:424`) | fn | shadowed by `vmm_address_space.spl:392` of the same name | **DEAD in practice** |
| `vmm_map_framebuffer` (`:401`) | fn | shadowed by `vmm_address_space.spl:346` of the same name | **DEAD in practice** |
| `x86_64_vmm_map_page` (`:288`) | fn | `X86Paging.map_page` ← `paging_map` ← `hal.spl:hal_paging_map`. **`hal_paging_map` was chased one hop further** (the `export use`/alias shim the closure tracer does not traverse): its only `src/**` hit is `replay/checkpoint/container_restore.spl:78`, which is a **comment**, not a call. Remaining hits are 5 spec files (`multiarch/hardening_gates_spec.spl`, `os_harden_audit.spl`). | **TEST-only** — not reachable from any kernel path, but **not deletable without touching specs** |
| `x86_64_vmm_unmap_page` (`:330`) | fn | `hal_paging_unmap` has **zero** references outside `hal.spl`/`hal_current.spl` | **DEAD** |
| `x86_64_vmm_translate` (`:428`) | fn | `hal_paging_translate` has **zero** references outside `hal.spl`/`hal_current.spl` | **DEAD** |
| `_phys_to_virt`, `_alloc_table_page`, `_ensure_table_entry`, `_read_pte`, `_write_pte`, `_pte_*`, `_*_index`, `_flags_to_pte_bits` | fn | in-file only | **DEAD-by-duplication** — byte-equivalent twins exist in `vmm_core` |
| `_invlpg` (`:475`) | fn | **none** in-file or out | **DEAD** |
| `_load_cr3` (`:479`), `_read_cr3` (`:483`) | fn | in-file (`vmm_switch_address_space`) | **LIVE** — but on *different externs* than core's, see §2.4 |
| `extern rt_read_cr3` / `rt_write_cr3` (`:30-31`) | extern | in-file | **LIVE** |
| `struct VirtMemManager` (`:62`) | struct | in-file | **LIVE-but-duplicate** — field-identical to `vmm_core:93` |
| `PTE_*`, `PAGE_SIZE`, `ENTRIES_PER_TABLE`, `TABLE_SIZE`, `IDENTITY_MAP_END` | val | in-file | **DEAD-by-duplication** — numerically identical to `vmm_core`'s |

### 1.3 `src/os/kernel/arch_adapt/x86_64/paging.spl` (44 lines, pure wrapper)

| symbol | referenced from | verdict |
|---|---|---|
| `paging_init` | `arch_adapt/hal_current.spl:117` ← `hal.spl:327 hal_paging_init` | **LIVE** — the boot entry |
| `paging_switch_address_space` | `vmm_address_space.spl:21` (direct import, bypassing `hal.spl`) | **LIVE** |
| `paging_map` | `hal.spl`/`hal_current.spl` → `hal_paging_map` → 5 spec files only (the sole `src/**` hit, `container_restore.spl:78`, is a comment) | **TEST-only** |
| `paging_unmap`, `paging_translate`, `paging_create_address_space`, `paging_levels` | only `hal.spl` + `hal_current.spl` trait tables; the `hal_paging_*` wrappers above them have **zero** references anywhere | **DEAD** — declared in the HAL surface, never dispatched to on x86_64 |

> **Method note.** The `paging_*` layer is *not* the end of the chain: `hal.spl:60`
> aliases `hal_paging_init as current_hal_paging_init` and `hal.spl:327` re-wraps it,
> so every `paging_*` symbol has a `hal_paging_*` shim above it. Liveness verdicts
> here were re-derived after grepping that second hop. Stopping at `paging_*` would
> have mislabelled `x86_64_vmm_map_page` as DEAD and produced a Step 2 that broke
> 5 specs.

**Headline:** of implementation A's ~25 functions, **exactly three are
load-bearing** (`vmm_init`, `_identity_map_4gb`, `vmm_switch_address_space`).
One more (`x86_64_vmm_map_page`) is TEST-only. Everything else is either dead or
a byte-equivalent duplicate of a `vmm_core` symbol.

---

## 2. The divergence family — every instance of this shape

The PML4 case is **one member of a family of nine**. Enumerated:

### D1 — kernel PML4 root *(the known instance; bridged, not cured)*
`arch:g_vmm.pml4_phys` vs `core:_vmm_pml4_phys`. Bridged by
`vmm_publish_kernel_pml4`. **Residual risk:** the bridge is a one-shot push at
init. If A ever reallocates or relocates the root, B goes stale silently again.

### D2 — HHDM offset *(same shape, same severity, currently masked)*
`arch:_phys_to_virt` reads `g_vmm.hhdm_offset` (`arch:145-147`); `core:_phys_to_virt`
reads `_vmm_hhdm_offset` (`core:187-189`). **Two independent HHDM offsets.** They
agree today only because `vmm_publish_kernel_pml4` happens to push both scalars in
the same call. Before commit `4575b4ce88d`, `_vmm_hhdm_offset` was **0**, meaning
every `core:_phys_to_virt` returned `phys` unchanged.

**Premise verified:** `g_hhdm_offset` (`boot/limine_boot.spl:168`) is written from
the Limine HHDM response at `:179` and surfaced as `boot_info.hhdm_offset` at
`:396`, so the real offset is nonzero on this boot path — the two copies genuinely
disagreed.

**Mechanism, precisely — this was latent, not lucky.** A zero offset in
`core:_phys_to_virt` was survivable *only because `arch:_identity_map_4gb`
identity-maps the low 4GB*: every core page-table walk against a table allocated
below 4GB silently worked, and would have faulted for the first table allocated
above it. So D2 was a **scaling bug armed and waiting on PMM pressure**, not a
harmless accident, and it strengthens §4 reason 1 — the runtime-mutation half was
walking tables through an offset nobody had ever initialized.

### D3 — initialized flag
`g_vmm_initialized` exists **only in core**. Implementation A has no init flag at
all; it signals "initialized" implicitly by `g_vmm.pml4_phys != 0`. So there are
two different, non-equivalent liveness predicates for the same subsystem, and the
one consumers check (`vmm_address_space.spl:76` reads `vmm_kernel_pml4_phys() == 0`,
not `g_vmm_initialized`) is a *third* one.

### D4 — CR3 access uses two different runtime externs
- core: `extern rt_read_cr3_raw` / `rt_write_cr3_raw` (`core:532-533`), **gated on
  `mmio_test_mode_enabled()`** with a `_vmm_fallback_cr3` shadow register.
- arch: `extern rt_read_cr3` / `rt_write_cr3` (`arch:30-31`), **no test gate at all**.

In `runtime_native.c` `rt_write_cr3_raw` merely forwards to `rt_write_cr3`, so on
hardware they coincide. Under host test mode they **do not**: core writes a fake
register, arch writes the real one. `vmm_switch_address_space` (arch) is therefore
the one CR3 writer that is invisible to `vmm_active_root()` (core) in tests. This
is the exact failure mode of D1, one register over, and it is **not yet bridged**.

### D5 — address-space creation is triple-implemented
Three functions named `vmm_create_address_space`:
1. `arch/x86_64/paging.spl:373` — copies kernel half from `g_vmm.pml4_phys`.
2. `memory/vmm_address_space.spl:34` — copies kernel half from `vmm_kernel_pml4_phys()`.
3. (riscv32/riscv64/x86_32 each have their own.)

`create_user_address_space` calls #2. #1 is reachable **only** through
`hal_paging_create_address_space`, which has zero callers — so #1 is an **armed
duplicate with no current caller**, the same shape D2 had before it fired. Same
name, same semantics, different source of truth: the moment anything routes
through the HAL it gets a differently-rooted — possibly zero-rooted — address
space, with no compile error and no log difference to announce it.

### D6 — address-space ids exist on only one side
`g_next_as_id` (core:185) is the monotonic AS id allocator. A's
`vmm_create_address_space` returns a bare physical root with **no id**. So
`AddressSpace{phys_root, id}` can only be minted by B; anything created via the
HAL path has no identity and cannot be tracked by `vmm_vma.spl`.

### D7 — framebuffer mapper is double-implemented, same name, same log line
`arch:401 vmm_map_framebuffer` (maps via `x86_64_vmm_map_page`, arch tables) vs
`vmm_address_space.spl:346 vmm_map_framebuffer` (maps via `core:vmm_map_page`).
Both emit the byte-identical string `[VMM] Mapped framebuffer: {n} pages at virt 0x…`.

### D8 — manager snapshot is double-implemented
`arch:424 vmm_get_manager` returns `g_vmm` (the struct global); `vmm_address_space.spl:392
vmm_get_manager` returns `vmm_manager_snapshot()` (built fresh from core scalars).
Field-identical `VirtMemManager` structs (`core:93` / `arch:62`), so the type system
cannot tell them apart. **Verified for the bridge:** `vmm_manager_snapshot` reads the
scalars, *not* `core:g_vmm` — so the scalar-only bridge is sufficient and complete
for this consumer. `core:g_vmm` is genuinely dead.

### D9 — duplicated constant blocks and helper set
`PAGE_SIZE`, `ENTRIES_PER_TABLE`, `TABLE_SIZE`, `PTE_PRESENT..PTE_NO_EXECUTE`,
`PTE_ADDR_MASK`, `IDENTITY_MAP_END` are declared twice with **numerically identical
values today** (verified). `_alloc_table_page`, `_ensure_table_entry`,
`_flags_to_pte_bits`, `_read_pte`/`_write_pte`, `_pte_*`, `_*_index` are duplicated
line-for-line. One consequential asymmetry already exists: `core:_flags_to_pte_bits`
carries a 7-line comment recording the *native-cranelift property-access miscompile*
(`flags.present` vs `flags.present()`); `arch:_flags_to_pte_bits` has the same code
but none of the knowledge. The next person to "clean up" the arch copy into
property style reintroduces a #PF(P=0) on first user fetch.

**Cross-arch note (scope, not this plan's work):** riscv64, riscv32 and x86_32 each
carry a fourth/fifth clone of this same structure (`arch/riscv64/paging.spl`,
`arch/riscv32/paging.spl`, `arch/x86_32/paging.spl`) with their own `g_vmm`. riscv64
is the only arch that calls `core:vmm_activate`. Consolidating those is a named
follow-on lane, not part of the ordered sequence below.

---

## 3. Banner audit

**Nine string pairs are byte-identical between the two x86_64 implementations.**
A serial log showing `[VMM] PML4 at physical 0x…` tells you nothing about which
module printed it — that ambiguity is precisely what cost two lanes a day.

Convention to adopt: **the one already in the tree.** `arch/riscv32/paging.spl`
tags itself `[VMM-RV32]`. Extend that, do not invent a new scheme.

| # | current string | file:line | proposed |
|---|---|---|---|
| 1 | `[VMM] Initializing virtual memory manager...` | arch/x86_64:221 | `[VMM-X64] Initializing virtual memory manager...` |
| | *(identical)* | vmm_core:310 | `[VMM-CORE] Initializing portable VMM...` |
| 2 | `[VMM] FATAL: Could not allocate PML4` | arch/x86_64:228 | `[VMM-X64] FATAL: could not allocate PML4` |
| | *(identical)* | vmm_core:317 | `[VMM-CORE] FATAL: could not allocate PML4` |
| 3 | `[VMM] PML4 at physical 0x{pml4_phys}` | arch/x86_64:241 | `[VMM-X64] kernel PML4 at physical 0x{pml4_phys}` |
| | *(identical)* | vmm_core:323 | `[VMM-CORE] kernel PML4 at physical 0x{pml4_phys}` |
| 4 | `[VMM] Identity-mapping first 4GB...` | arch/x86_64:244 | `[VMM-X64] identity-mapping first 4GB...` |
| | *(identical)* | vmm_core:326 | `[VMM-CORE] identity-mapping first 4GB...` |
| 5 | `[VMM] VMM initialization complete` | arch/x86_64:247 | `[VMM-X64] init complete (root=0x{pml4_phys}, hhdm=0x{hhdm})` |
| | *(identical)* | vmm_core:329 | `[VMM-CORE] init complete` |
| 6 | `[VMM] FATAL: Could not allocate PDPT for identity map` | arch/x86_64:260 | `[VMM-X64] FATAL: …` |
| | *(identical)* | vmm_core:362 | `[VMM-CORE] FATAL: …` |
| 7 | `[VMM] FATAL: Could not allocate PD for identity map` | arch/x86_64:269 | `[VMM-X64] FATAL: …` |
| | *(identical)* | vmm_core:369 | `[VMM-CORE] FATAL: …` |
| 8 | `[VMM] Identity-mapped 4GB with 2MB pages (2048 entries)` | arch/x86_64:282 | `[VMM-X64] identity-mapped 4GB / 2MB pages / 2048 entries` |
| | *(identical)* | vmm_core:381 | `[VMM-CORE] …` |
| 9 | `[VMM] Mapped framebuffer: {n} pages at virt 0x…` | arch/x86_64:418 | `[VMM-X64] mapped framebuffer: …` |
| | *(identical, different file)* | vmm_address_space:359 | `[VMM-AS] mapped framebuffer: …` |
| 10 | `[VMM] portable VMM published kernel PML4 0x…` | vmm_core:297 | `[VMM-CORE] published kernel PML4 0x{p} hhdm 0x{h} (from VMM-X64)` — **already unambiguous; only add the hhdm value (D2 needs it visible)** |
| 11 | `[VMM] create_user_address_space: VMM not initialized — legacy AS=1` | vmm_address_space:76 | `[VMM-AS] create_user_address_space: kernel PML4 is 0 — legacy AS=1` — **name the actual predicate, not "not initialized"** |
| 12 | `[VMM] create_user_address_space: alloc failed — legacy AS=1` | vmm_address_space:81 | `[VMM-AS] create_user_address_space: PML4 alloc failed — legacy AS=1` |
| 13 | `[VMM] NVMe BAR mapped at higher-half …` | vmm_address_space:386 | `[VMM-AS] NVMe BAR mapped …` |

**Cross-arch ambiguity (same fix, follow-on lane):** `arch/riscv64/paging.spl`
(8 strings) and `arch/x86_32/paging.spl` (6 strings) also emit bare `[VMM]`.
Propose `[VMM-RV64]` and `[VMM-X32]`, matching the existing `[VMM-RV32]`.

**This is Step 1 of the plan and it stands alone.** It is a pure string change with
zero semantic risk, and it is the single change that converts this class of defect
from a day of bisection into a `grep` of the serial log.

---

## 4. Which implementation survives, and why

**Survivor: `src/os/kernel/memory/vmm_core.spl` (B).**

Five reasons, strongest first:

1. **B is what the kernel actually uses at runtime.** Every mapping, unmapping,
   PTE read, translate, COW clone, heap grow, DMA pin and syscall copy goes
   through B (§1.1). A's entire mapping surface (`x86_64_vmm_map_page`,
   `_unmap_page`, `_translate`) has **zero callers** (§1.2). Deleting A's mapping
   half removes dead code; deleting B's would require rewriting seven modules.

2. **B is the tested one; A has no tests at all.** B carries
   `vmm_init_sparse_for_test`, `vmm_set_map_failure_after_for_test`,
   `_vmm_fallback_cr3` and is exercised by 11 spec files. A has no test hooks and
   no spec references. **The implementation that ships the boot-time page tables
   is the one nothing tests.** Making B the survivor closes that gap by
   construction rather than by adding tests to a module slated for deletion.

3. **B is portable; A is x86_64-only.** B carries the `@cfg`-per-arch
   `VMM_KERNEL_SPACE_START` and the arch-neutral VMA/flags vocabulary consumed by
   `vmm_vma.spl` and `vmm_shared.spl`. riscv64 already calls `core:vmm_activate`.
   Consolidating *onto* B is the same direction the other arches are already
   drifting.

4. **B holds the accumulated defect knowledge.** `core:_flags_to_pte_bits` documents
   the cranelift property-access miscompile; `core:_alloc_table_page`'s raw-ABI
   choice and the scalar-vs-struct-global rule from `vmm_publish_kernel_pml4`'s
   docstring are both B-side. A's twins have the same code and none of the reasons.

5. **B's state representation is the one that survives freestanding codegen.**
   B stores `pml4_phys`/`hhdm_offset` as **scalar module vars** (zeroed `.bss`);
   A stores them in a **struct global with a constructor initializer**, which is
   the category the bug write-up identifies as unreliable under freestanding
   native codegen. Keeping A's `g_vmm` as the source of truth keeps the fragile
   representation on the critical path.

**A does not disappear.** `arch/x86_64/paging.spl` shrinks to what an arch module
should be: the x86_64 `PTE_*` bit layout, `X86Paging`, the CR3/invlpg primitives,
and a `vmm_init` that allocates the root and hands it to B. Target: ~531 → ~150
lines.

---

## 5. Ordered consolidation sequence

Each step is independently landable, independently verifiable, and leaves the tree
green. **Do not batch.** Push each step separately (standing rule: push per fix).

> **Gate vocabulary used below**
> - **G-build** — `bin/simple build` completes AND the freestanding stub baseline
>   for `simpleos_ssh_ring3_uefi128.elf` is **still exactly 56 rows** in
>   `config/freestanding_fabricated_stub_baseline.sdn`. See §6.
> - **G-ovmf** — `scripts/os/scp_retrieve_over_ssh_uefi.shs` run to the L4 rung,
>   accepted **only** on the positive marker line
>   `[oo-nvme] persist /hello.o -> OK` appearing in the transcript.
>   *Acceptance is never "no failure line appeared."* A truncated, hung, or
>   SIGTERM'd run produces no failure line and must read as FAIL.
> - **G-spec** — `bin/simple test test/02_integration/os/memory_*_spec.spl` and
>   `test/01_unit/os/kernel/ipc/syscall*_spec.spl`, with a **stated pass count**;
>   "no failures" alone is not a pass (a zero-tests-found run has no failures).
> - **G-serial** — QEMU boot transcript inspected for the specific banner set the
>   step is supposed to produce.

---

### Step 1 — Disambiguate every banner *(strings + their four consumers)*
**Change:** apply §3 rows 1–13 in `arch/x86_64/paging.spl`, `vmm_core.spl`,
`vmm_address_space.spl`. Add the hhdm value to the publish line (row 10) and
name the real predicate in row 11.

**⚠ Risk is NOT "~none" — the consumer grep was run and it hit. Four consumers
match on the literals this step renames, and one of them is the OVMF gate
itself.** Every one must be updated *in the same commit*:

| consumer | current match | breakage | required edit |
|---|---|---|---|
| `scripts/os/scp_retrieve_over_ssh_uefi.shs:236` | `grep -qaE "spawn\] FAIL user-AS\|spawn returned rc=-1\|**VMM not initialized**"` | **Row 11 renames exactly this string.** The gate's ring-3-spawn *failure detector* would stop firing → a real spawn failure gets misreported as a timeout. This is the highest-consequence line in the whole plan. | widen to `VMM not initialized\|kernel PML4 is 0` |
| `scripts/os/scp_retrieve_over_ssh_uefi.shs:238` | `grep -aoE "\[VMM\][^;]{0,70}\|…"` | `\[VMM\]` requires `]` immediately after `VMM`; `[VMM-X64]` does **not** match. The diagnostic context dump on failure goes empty. | widen to `\[VMM[^]]*\]` |
| `test/03_system/os/qemu/os/memory/vmm_qemu_spec.spl:93` | `expect(output).to_contain("[VMM]")` | fails after rename | change to a specific producer-tagged string |
| `test/system/qemu/os/memory/vmm_qemu_spec.spl:93` and `test/01_unit/qemu_standalone/os/memory/.spipe_matchers_vmm_qemu_spec.spl:85,93` | same | same | same |

Note also: those specs' docstrings claim the kernel logs `[VMM] cow-clone`.
**No such string exists anywhere in `src/os/kernel/`** — the assertion is
`to_contain("[VMM]")`, which any of the ten ambiguous banners satisfies. That
spec is vacuous today and is a second instance of the same "evidence that cannot
name its producer" failure. Give it a producer-specific string while you're here.

**Revised risk: medium** — no kernel control flow changes, but it edits the
acceptance gate that every later step depends on. Land and re-run G-ovmf before
touching anything else.
**Gate:** G-build + G-ovmf (must still reach `[oo-nvme] persist /hello.o -> OK`,
proving the widened matchers didn't break the script) + G-serial (transcript must
show **both** `[VMM-X64] init complete` and `[VMM-CORE] published kernel PML4 …
hhdm 0x…`, and must **not** show any bare `[VMM]` from an x86_64 module).
**Why first:** every later step is verified by reading this transcript.

### Step 2 — Delete implementation A's dead mapping surface
**Change:** delete `x86_64_vmm_unmap_page` (`:330`), `x86_64_vmm_translate`
(`:428`), `_invlpg` (`:475`) — all three proven callerless through both the
`paging_*` and the `hal_paging_*` hop. **Do not delete `x86_64_vmm_map_page`:
it is TEST-only, not dead** (5 specs reach it via `hal_paging_map`). Instead
*repoint* `X86Paging.map_page`/`unmap_page`/`translate` at `vmm_core`'s
equivalents, which keeps those specs passing while removing the second mapping
implementation — and, usefully, makes those specs exercise the code that actually
ships. Delete `arch:vmm_get_manager` (`:424`) and `arch:vmm_map_framebuffer`
(`:401`), both shadowed and unreachable (D7, D8).
**Risk:** medium — the re-export trap already bit once here (see the method note
in §1.3). Re-verify every deletion by bare-name grep across `src/**` **and**
`test/**`, at **both** the `paging_*` and `hal_paging_*` levels, and never by
build success alone: a symbol removed while still referenced becomes a fabricated
stub, not a build error, unless the ratchet in §6 catches it.
**Gate:** G-build (stub baseline still 56 — a deletion that breaks a source file's
build now *fails loudly* instead of shipping no-op stubs) + G-spec + G-ovmf.

### Step 3 — Make the HHDM offset single-sourced (D2), before any code sharing
*(Must precede Step 4 — see the ordering hazard there.)*
**Change:** `arch:vmm_init` publishes `hhdm_offset` into core **as its first
action**, before `_alloc_table_page` is ever called. `arch:_phys_to_virt` becomes
`vmm_core.vmm_phys_to_virt`. `arch:g_vmm.hhdm_offset` is retired.
**Risk:** medium-high — this is the live boot path. The failure mode is a bad
phys→virt at the exact moment the PML4 is zeroed, i.e. an immediate triple fault.
Mitigation: the publish happens before the first allocation, and Step 1's banner
now prints the hhdm value so the transcript proves the ordering.
**Gate:** G-ovmf (must reach `[oo-nvme] persist /hello.o -> OK`) + G-serial
(`[VMM-CORE] published … hhdm 0x…` must appear **before** `[VMM-X64] kernel PML4
at physical 0x…`).

### Step 4 — Collapse the duplicated constants and helpers (D9)
*(Executes after Step 3. Numbered to match execution order and the SDN graph.)*
**Change:** `arch/x86_64/paging.spl` imports `PAGE_SIZE`, `ENTRIES_PER_TABLE`,
`TABLE_SIZE`, `PTE_*`, `PTE_ADDR_MASK`, `IDENTITY_MAP_END`, `_read_pte`,
`_write_pte`, `_pte_is_present`, `_pte_phys_addr`, `_*_index`,
`_flags_to_pte_bits`, `_ensure_table_entry`, `_alloc_table_page` from
`vmm_core` instead of redeclaring them. Values verified numerically identical
today, so this is a no-op by construction.
**Risk:** medium — this is the first step that changes which code the boot path
executes. Two specific hazards: (a) `_flags_to_pte_bits` must keep the explicit
`flags.present()` call form (property access miscompiles under freestanding
cranelift — see D9); (b) `arch:_alloc_table_page` and `core:_alloc_table_page`
call the same `pmm_alloc_page_raw` but resolve `_phys_to_virt` differently —
**this step must not land before Step 3 (HHDM single-sourcing)**, or the shared
`_alloc_table_page` will zero the new table through core's `_vmm_hhdm_offset`,
which is still 0 at the moment `vmm_init` allocates the PML4. That is a triple
fault at boot, not a subtle regression.
**Gate:** G-build + G-ovmf + a serial diff of the pre/post `[VMM-X64]` line set
(must be identical).

### Step 5 — Make the kernel root single-sourced (D1), retire `arch:g_vmm`
**Change:** `arch:vmm_init` stops writing `g_vmm.pml4_phys`; it calls
`vmm_publish_kernel_pml4` and nothing else. `arch:vmm_create_address_space`
(D5) is deleted — it is **dead**, not live (§1.2), so this is a removal with no
repoint risk — and `X86Paging.create_address_space` is pointed at
`vmm_address_space.spl:34`, which already reads `vmm_kernel_pml4_phys()` and
already mints an id from `g_next_as_id` (disarming D5 and D6 together). Delete
`arch:struct VirtMemManager` and `arch:g_vmm` entirely. Delete the now-dead
`core:g_vmm` and its two dead imports in `vmm_address_space.spl:14` /
`vmm_copy.spl:11` (D8).
**Risk:** medium-high, and concentrated in one place. The AS-creation half is
low-risk (deleting a dead duplicate). The risk is retiring `arch:g_vmm`: it is
still the struct that `arch:vmm_init` writes and `arch:_phys_to_virt` reads at
the moment the PML4 is allocated, and it sits on the FS-exec ring-3 spawn path —
the exact path the original defect broke.
**Gate:** G-ovmf **plus an explicit ring-3 spawn witness** — the transcript must
show a successful FS-exec spawn (rc == 0, not rc == -1) and must **not** contain
`[VMM-AS] create_user_address_space: kernel PML4 is 0`. G-spec with stated counts.

### Step 6 — Unify CR3 access (D4)
**Change:** delete `arch:extern rt_read_cr3`/`rt_write_cr3` and
`arch:_load_cr3`/`_read_cr3`; `arch:vmm_switch_address_space` calls
`vmm_core._load_cr3`, inheriting the `mmio_test_mode_enabled()` gate and the
`_vmm_fallback_cr3` shadow.
**Risk:** medium. On hardware `rt_write_cr3_raw` forwards to `rt_write_cr3`, so
behaviour is unchanged; in host tests, CR3 writes become observable to
`vmm_active_root()` for the first time — expect previously-silent specs to start
asserting, which is the point.
**Gate:** G-spec (stated counts; a spec that newly *fails* here is a real defect
found, not a regression to paper over) + G-ovmf.

### Step 7 — Retire the two dead inits and the dead bootstrap probes
**Change:** delete `core:vmm_init` (`:299`), `core:vmm_init_from_global_pmm`
(`:308`), `core:_identity_map_4gb` (`:356`), `core:vmm_bootstrap_pml4_entry0`,
`_pdpt_entry0`, `_pd_entry0`. Keep `core:vmm_activate` (riscv64 uses it) with a
comment saying so.
**Risk:** low — all proven callerless in §1.1. Deleting them removes the last
copy of the byte-identical banner set, so the ambiguity cannot regrow.
**Gate:** G-build (stub baseline still 56) + G-spec + G-ovmf.

### Step 8 — Lock it: a guard that fails when the split regrows
**Change:** add a repo check (under `scripts/check/`) that fails when **two
distinct `.spl` files under `src/os/kernel/` emit the same `[VMM…]` literal**, and
when more than one module declares a `pml4_phys`/root-of-page-table global for the
same arch. Fail-closed on cwd, and with a positive verdict line stating how many
strings/globals it examined (`PASS — n strings, m globals checked`) per the
existing guard convention — a vacuous run must exit non-zero, not 0.
**Risk:** none to the kernel. The risk is writing a fail-open guard; require a
`--selftest` with fixtures that reproduce the pre-Step-1 duplicate banner set and
prove the guard flags it.
**Gate:** guard `--selftest` passes; guard run against the pre-Step-1 tree
(`git stash`/worktree at the parent commit) must **FAIL** — a guard that has never
been seen to fail has not been shown to work.

### Follow-on lanes (named, not scheduled here)
- **L-RV64 / L-X32 / L-RV32:** apply Steps 1–7 to `arch/riscv64/paging.spl`,
  `arch/x86_32/paging.spl`, `arch/riscv32/paging.spl`. Each carries its own `g_vmm`
  and its own duplicate helper set; riscv64 and x86_32 also emit bare `[VMM]`.
- **L-HAL:** `paging_map`/`paging_unmap`/`paging_translate`/`paging_create_address_space`
  are declared in the HAL surface and dispatched to by nobody on x86_64. Either wire
  the kernel through the HAL or delete the trait methods — the current state is a
  third path that looks live and isn't.

---

## 6. Use the fabricated-stub ratchet as a tool, not just a gate

`simpleos_ssh_ring3_uefi128.elf` is now baselined at **56 fabricated-stub rows** in
`config/freestanding_fabricated_stub_baseline.sdn`.

This matters for every deletion step above. Historically, a consolidation step that
made a source file fail to build did not fail the build — the freestanding lane
substituted weak no-op stubs and the kernel shipped, silently, with the deleted
function replaced by a stub that returned 0. That is *exactly* the failure shape of
the original PML4 defect (a read that returns 0 and looks initialized), so this
refactor is the highest-risk possible workload for that hazard.

With the ratchet in place:
- **Any step whose stub count rises above 56 is rejected outright.** Do not
  re-baseline to make a step land. The rise is the signal that a source file
  stopped building.
- **Steps 2, 5 and 7 should each *lower* the count or hold at 56.** A deletion step
  that leaves the count unchanged is fine; one that raises it means a symbol was
  deleted that something still references through a path grep missed — most likely
  an `export use` re-export the closure tracer doesn't traverse.
- **Record the count in each step's commit message.** `stubs: 56 → 56` is a
  one-token proof that the deletion was clean.

---

## 7. What this plan explicitly does not do

- Does not touch riscv64/riscv32/x86_32 paging (named follow-on lanes, §5).
- Does not resolve the HAL dead-surface question (L-HAL).
- Does not add tests to implementation A — A is being deleted, not tested.
- Does not remove `vmm_publish_kernel_pml4`. It stays through Step 4 as the
  ordering-explicit publish point, and is the natural home for the single write
  after Step 5.

## 8. Cross-references

- Bug: `doc/08_tracking/bug/simpleos_vmm_kernel_pml4_phys_reads_zero_after_init_2026-08-06.md`
- Related freestanding-codegen defects cited in-source:
  `doc/08_tracking/bug/baremetal_option_field_unwrap_faults_class_2026-07-18.md`,
  `doc/08_tracking/bug/desktop_e2e_entry_paging_alloc_crash_no_hhdm_2026-07-20.md`
- Gate script: `scripts/os/scp_retrieve_over_ssh_uefi.shs` (L4 marker
  `[oo-nvme] persist /hello.o -> OK`)
- Stub ratchet: `config/freestanding_fabricated_stub_baseline.sdn`
- Board rule: `.claude/rules/board-runnable.md` — every gate above is the OVMF
  real-firmware proxy, never `-kernel`/`isa-debug-exit`.
