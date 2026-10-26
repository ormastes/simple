# Phase 3 re-export diagnostic amplification

Status: open; measured symptom, CPU cause not yet isolated.

The interrupted Phase 3 run emitted 61,596 `hir-reexport-chase-unresolved`
warnings while reaching declaration completion for 492 distinct modules.
Declaration completion does not prove valid HIR, MIR, or emitted objects.
Primitive names such as `i64`, `bool`, and `text` appear in these warnings.
Investigate incorrect primitive routing and repeated re-export traversal before
suppressing diagnostics: unresolved user symbols must still report errors.

Evidence: `build/native_probe/vulkan-nested-or-owner-20261010/phase3-restart/ROOT_TERMINAL_DIAGNOSTICS.json`.
The final compiler log SHA-256 is
`772cf87b7bc607a90bed6862622046856e44cd3af232ee9554eab0cb4a43b196`.
The run stopped on the volume-wide 3 GiB free-space reserve, not a natural
compiler exit. Its output was 26,557,861 bytes; process-tree peak RSS was
3,450,424 KiB. Owned artifact growth was 338,817,200 bytes. Other volume
consumption has not been attributed.

Relevant owner: `src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl`.

Acceptance:

- Reproduce primitive imports and genuine missing re-exports with real HIR tests.
- Preserve missing-symbol failures and valid export resolution.
- Measure traversal count, diagnostic count, elapsed time, and peak RSS on the
  same pinned baseline/candidate source and producer.
- If memoizing, include module identity, source generation, import scope, and
  relevant export changes in the key; test invalidation and concurrent readers.
- Do not infer 40 active workers from the requested worker setting.

No workaround has been applied. No performance improvement is claimed.
