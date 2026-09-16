# GPU lib specs red: removed / never-landed lib APIs (2026-09-16)

## Observed
21 specs under `test/01_unit/lib/gpu/` fail with `semantic: ... not found` for
symbols that do NOT exist anywhere in `src/lib/**` (verified by /usr/bin/grep
census + `git log -S` history probes):

- `SoftwareBackend.read_pixels_damaged_with_checksum`,
  `SoftwareBackend.read_pixels_regions_packed`
  (`backend_software_damage_checksum_spec.spl`,
  `backend_software_damage_spec.spl`) — lib has only `read_pixels_damaged`
  (backend_software.spl:1632).
- `Engine2D.preferred_backend_order` static
  (`engine_backend_preference_spec.spl`) — added by 502200c0f35, gone after
  377405b767b ("perf(gui): integrate backend and glyph parallel lanes").
- `preferred_graphics_backend` (`graphics_context_spec.spl`).
- `simd_blit_rect_u32`, `simd_scroll_region_u32`
  (`simd_kernels_owned_copy_spec.spl`).
- object_vm group (`gpu_mmu_placement_planner_spec.spl`,
  `gpu_mmu_placement_rss_spec.spl`, `gpu_mmu_placement_contracts_spec.spl`,
  `gpu_mmu_store_recovery_spec.spl`, `object_vm_descriptor_spec.spl`):
  `placement_object_state`, `placement_modeled_peak_host_rss`,
  `ArenaResidency`, `hash128` (in placement_contracts.storage),
  `GpuCasStore`, `DescriptorTable` — none in
  `src/lib/common/compute/placement_contracts/**`.
- `TextBlitCache` (`helpers_text_cache_spec.spl`) — lane commits
  c7d0bb3b98e / 16411a5d843 reference it; current tree has no definition.
- `font_vertex_bytes_checked` (`engine3d/font_hud_material_spec.spl`).
- `FontRenderer.staged_reject_reason` / `FontRenderBatch.atlas_owner_sequence`
  fields (`font_runtime_config_spec.spl`, `draw_ir_adv_branch_coverage_spec.spl`).
- `BackendProbeResult.is_hardware()/summary()/memory_mb`
  (`backend_probe_strict_spec.spl`) — lib has free fn
  `backend_is_hardware(name)` in helpers_availability.spl only.
- `GENERATED_2D_GLYPH` constant and entry `"simple_2d_glyph_raster_u32"`
  (`generated_kernel_args_spec.spl`) — only
  `GENERATED_2D_GLYPH_ARG_BYTES` exists.

## Impact
Specs that pin these contracts stay RED; the behaviors they document
(damage checksums, packed region readback, placement planner, CAS store,
descriptor generations, text blit cache, font vertex checks) are unguarded.

## Expectation
Either restore the APIs (they were deliberate lane deliverables per the
commit subjects) or update the specs to the replacement APIs — each needs an
owner decision per lane; not spec-side typos.

## Unblock condition
For each symbol: land the owning lib change (or its successor API) and make
the corresponding spec green; keep `git log -S <symbol>` as the audit trail.
