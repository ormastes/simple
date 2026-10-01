# Native GUI HIR loses nested field owner types

Status: OPEN compiler issue; application-side source checkpoint `819a85c67a9` is pushed but has no GUI runtime PASS.

The Windows Phase 2 IDE-provider native build reported `gui_shell.spl`: declared `text` return expected `TypeId(12)`, found `i64` `TypeId(5)`. The strongest source candidate was `_drag_hit_zone_tab` returning `panels[tab_index].id`: `DockPanel.id` is `text`, while another visible dock type has numeric `id`. Native HIR can lose the receiver's element/owner type and select a field by name from an unrelated struct. The original diagnostic did not include a function/line, so this attribution is high-confidence, not proven from that message alone.

A focused no-stub build using the admitted exact424 Stage 2 compiler (SHA-256 `510d70d22d0e909e04bb0f6e37087cea8c1fa1e0af6c8e89340db08b7168f7eb`) then exposed `struct 'ANY' field 'file_tree_visible'` in `gui_shell_run_profile` and `struct 'ANY' field 'session'` in the direct regression when GUI state owner imports were absent. Explicit `DockPanel`/GUI owner imports and typed locals reached native linking on the third bounded cycle. Linking failed on missing SDL/DAP and other GUI symbols, so no executable or drag runtime assertion passed. Evidence is retained under `build/mini_builds/gui-typed-drag/` in the publication checkout; the final test click was corrected by source review without another build.

Compiler follow-up: resolve nested fields from the actual receiver/array element type and reject ambiguous `ANY` field lookup instead of choosing a same-named field from another struct. Add a small positive/negative native HIR regression independent of the full GUI closure. The app annotations preserve behavior but do not prove the general compiler defect fixed.
