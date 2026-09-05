# SimpleOS VMM Consolidation — TLDR

Full plan: `vmm_consolidation_plan.md` (2026-08-06). Analysis only — no kernel code changed.

- **Two x86_64 VMM impls print byte-identical `[VMM]` banners.** `arch/x86_64/paging.spl` **builds** the page tables at boot (owns `g_vmm`); `memory/vmm_core.spl` **mutates** them at runtime (owns `_vmm_pml4_phys`). Nothing bridged them → the PML4=0 defect. `4575b4ce88d` is a bridge, not the cure.
- **Evidence that can't name its producer isn't evidence.** 9 string pairs are byte-identical across the two modules; a 10th collides with `vmm_address_space.spl`. Step 1 tags them `[VMM-X64]`/`[VMM-CORE]`/`[VMM-AS]`, extending the `[VMM-RV32]` convention already in the tree.
- **Step 1 is NOT zero-risk — the consumer grep was run and hit.** The OVMF gate itself matches `\[VMM\]` (`scp_retrieve_over_ssh_uefi.shs:238`) **and the literal `"VMM not initialized"` in its ring-3 spawn-failure detector (`:236`)**. Four consumers must widen in the same commit, or Step 1 blinds the gate every later step depends on. A qemu spec asserting `to_contain("[VMM]")` is vacuous today for the same reason.
- **Liveness is 3-way, and must be chased through the `hal_paging_*` shim** the closure tracer doesn't traverse. Of impl A's ~25 fns only **3** are load-bearing (`vmm_init`, `_identity_map_4gb`, `vmm_switch_address_space`); `x86_64_vmm_map_page` is TEST-only (stopping at the `paging_*` hop would have mislabelled it DEAD and broken 5 specs). Sharp asymmetry: `vmm_switch_address_space` is live only via an **adapter side-door that skips `hal.spl`**, while its twin `vmm_create_address_space` has only the HAL route and is therefore **dead**. B's `vmm_init`/`vmm_init_from_global_pmm`/`g_vmm`/3 bootstrap probes are dead too.
- **Divergence family = 9, not 1.** D1 PML4 (bridged) · **D2 HHDM was also 0 — survivable only because arch identity-maps the low 4GB, i.e. a scaling bug armed on PMM pressure, fixed by accident** · D3 three different "initialized" predicates · **D4 CR3 on two different externs, arch half ungated in test mode — not yet bridged** · D5 `vmm_create_address_space` triple-implemented, the arch copy an armed duplicate with no current caller · D6 AS ids on one side only · D7/D8 shadowed framebuffer + manager twins · D9 duplicated `PTE_*`, only core's copy carrying the cranelift property-access-miscompile warning.
- **Survivor = `vmm_core.spl`**: it's what runtime uses, it's the tested one, it's portable, it holds the defect knowledge, and its scalar `.bss` state survives freestanding codegen (A's struct-global does not). A shrinks 531 → ~150 lines.
- **8 steps, numbered in execution order.** Step 3 (HHDM single-source) **must** precede Step 4 (shared helpers) or the shared `_alloc_table_page` zeroes the PML4 through a 0 offset → triple fault at boot.
- **Gates:** G-ovmf accepts **only** the positive marker `[oo-nvme] persist /hello.o -> OK`, never absence-of-failure. G-spec requires a stated pass count. Step 8's regrowth guard must be *seen to fail* on the pre-Step-1 tree.
- **Stub ratchet as a tool:** 56 rows baselined for `simpleos_ssh_ring3_uefi128.elf`. Count rising = a source file stopped building. Never re-baseline to land a step; record `stubs: 56 → 56` per commit.
- **Follow-ons named, not scheduled:** riscv64/riscv32/x86_32 each carry a clone (riscv64 + x86_32 also emit bare `[VMM]`); the HAL `paging_*` surface is a third path that looks live and isn't.

```sdn
graph: {
  S1_banner_disambiguate: []
  S2_retire_A_mapping_surface: [S1_banner_disambiguate]
  S3_hhdm_single_source: [S2_retire_A_mapping_surface]
  S4_collapse_dup_constants: [S3_hhdm_single_source]
  S5_root_single_source_retire_g_vmm: [S4_collapse_dup_constants]
  S6_unify_cr3: [S5_root_single_source_retire_g_vmm]
  S7_delete_dead_inits: [S6_unify_cr3]
  S8_regrowth_guard: [S7_delete_dead_inits]
  L_RV64_X32_RV32: [S8_regrowth_guard]
  L_HAL_dead_surface: [S8_regrowth_guard]
}
```
