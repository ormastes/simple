# Phase4 GUI/browser unresolved owner imports

Status: source repair authored; current-producer compilation UNRUN.

The frozen916be Phase4 full CLI build completed2592 HIR modules with2583
successful and9 failed. This patch owns only3 failed modules, not the six
MCP/T32 failures handled separately. Evidence: early-p4-full-cli-916be/
hir-failure-diagnostics.json and owner/build.log in the Windows restart packet.

gui_shell.spl had10 unresolved call names: outline_panel_render,
gui_render_tab_bar_html, gui_render_file_tree_html, gui_render_settings_html,
gui_render_editor_area_with_diagnostics_and_hover_delay, editor_mode_name,
md_stats_to_status_bar, editor_layout_compute_rects, md_buffer_content,
md_compute_stats. Each is now imported explicitly from its implementation owner.
The stats owner is services.md_doc_stats, returning MdDocStats as required by
EditorDocument.cached_md_stats; the same-named md_commands function returns
text and must not be selected merely by leaf name.

gui_sdl_bridge.spl had3 unresolved char_from_code uses. The UTF8 owner is
imported explicitly; all three existing calls are guarded to ASCII ranges,
where its conversion agrees with the canonical character conversion contract.
paint_layout.spl had1 unresolved draw_ir_rect_clipped use; it is added to the
existing explicit draw_ir owner import, retaining clipping behavior unchanged.

These are missing lexical dependencies in the consumers. Unresolved facade
chase messages alone do not prove a compiler reexport defect; no such claim is
made here. No rendering, SDL input, clipping, or markdown computation is stubbed
or excluded. Explicit owner imports remain valid after a full rebuild; remove
them only if an intentional supported facade replaces the dependency contract.

Validation: exact symbol declarations and caller types reviewed; working/staged
environment guard and diff checks required before commit. Existing module
behavior tests need no mirror import-string tests. Next bounded current-producer
compile must use a fresh owned source overlay and preserved private caches for
these modules; all native execution is UNRUN in this checkpoint. No frozen
source916be, active build, or previous failure receipt was modified.
