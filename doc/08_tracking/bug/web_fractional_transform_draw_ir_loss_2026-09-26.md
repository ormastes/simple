# Web fractional CSS and transform semantics lost before DrawIR

Status: OPEN. Found while reviewing C/N2 corpus evidence on 2026-09-26.

`02-fractional-edges.html` specifies fractional offsets and dimensions plus
`translate(.25px,.25px) rotate(7deg)`. Web layout uses integer box geometry,
and `simple_web_html_layout_renderer_decl_apply.spl` applies only integer
translation, percentage scale, and quarter-turn rotation to box dimensions.
The seven-degree rotation does not become a DrawIR raster transform. A command
count and accepted UiIr lowering therefore cannot prove that the Web producer
preserved the source scene.

The C/N2 corpus receipt now reports cases tagged `subpixel` or `transform` as
`blocked`, including cases 02, 07, 08, and 29. This is an evidence guard,
not the implementation of those CSS features.

Resolution requires computed fractional layout coordinates and transform
matrices to reach the shared DrawIR contract without rounding, explicit
preflight by both Vulkan consumers, and independent pixels for the pinned
cases. Until then, no producer or dual-backend PASS may be recorded for them.
