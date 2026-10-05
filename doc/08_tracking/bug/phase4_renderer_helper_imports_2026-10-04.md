# Phase4 renderer helper imports

Status: source repair prepared; native verification pending.

The completed full-CLI HIR pass at source 9737d1217bc4 failed in
`simple_web_html_layout_renderer_decl_apply`, `paint_layout`, `paint_raster`,
and `paint_primitives`. The first three modules call existing declarations or
foundation helpers without importing them. Import those exact owners rather
than duplicating their parsing, declaration dispatch or geometry behavior.

The fourth module already imports `engine2d_simd_fill_row_u32` from the no-GC
async facade, but that facade omits this existing export from its synchronous
owner. Restore it alongside the existing buffer/rows exports. The native row
regression requires five exact high-bit color pixels and an empty zero-width
row; it cannot pass by silently returning an empty fallback for nonempty work.

Validation still required: compile all four renderer modules and execute the
existing paint-primitives coverage spec plus the new SIMD row facade spec on
the rebuilt native runtime. The original HIR diagnostics are capped per module;
these repairs do not prove that no further names or semantic errors remain.
The separate missing DrawIR v4 contract is not repaired by this change.
