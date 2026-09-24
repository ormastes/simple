# Web fractional CSS geometry and transform loss

Status: OPEN — selected C/N2 Simple 2D, Web and GUI hardening.

The pinned `02-fractional-edges` corpus page authors decimal `left`, `top`,
`width`, and a `translate(.25px,.25px) rotate(7deg)` transform. In
`simple_web_html_layout_renderer_decl_apply.spl`, declaration application
stores the box dimensions and offsets in `i32`, adds parsed translation to
those integers, and only swaps dimensions for a recognized quarter turn.
`simple_web_html_layout_renderer_style.spl` has integer box fields and no
authoritative general transform payload. The Web DrawIR emitter uses the
integer layout boxes. Therefore a rectangle projection of this page would
lose authored geometry and the seven-degree rotation.

Expected behavior: resolve CSS geometry and transform in source order into
typed values before rounding; preserve fractional box coordinates in DrawIR;
reject unsupported transforms before any GPU command is submitted. Once an
affine and antialiasing contract exists on both Vulkan paths, qualify this
case with a fixture-specific comparison policy and a physical Linux device.

Regression evidence to add: decimal authored values survive Web producer to
DrawIR/SDN/UiIr; the current unsupported rotation rejects the complete scene;
the later affine implementation verifies transform order, origin and clip
space; both backends produce completed pixels within a tolerance declared
before viewing output. Current corpus manifest status remains `not-run`.

## Provenance guard added

The Web `Style` now retains the winning normalized raw `transform`,
`translate`, `scale`, and `rotate` declarations across cascade copies and
layout style reconstruction. Source DrawIR computed style carries all four.
The existing opaque-rectangle admissions require each to be `none`, so a
future transformed source cannot be accepted after its integer fallback
geometry loses semantics. A focused real-producer spec checks the retained
values and rejection, but has no trustworthy Simple runtime PASS because the
isolated verifier build reached the repository's three-attempt cap and failed
at native linking. Decimal geometry and affine rendering remain open.

## Decimal box guard added

The Web producer now records raw box-length tokens before the full or fast
integer declaration path and computes a scene-level unresolved-geometry
reason from all computed styles before DrawIR visibility culling. The three
pinned rectangle admissions reject that reason. Decimal lengths, expressions,
unsupported units and legacy `clip` are blocked; border shorthands and sizing
constraints are included in the conservative capture. A focused source spec
covers decimals, the fast path, subpixel culling, ancestor positioning and
`clip:rect(...)`. It has no runtime PASS. Resolved f64 CSS boxes and affine
rendering remain open, so corpus case 02 is still `not-run`.

## Bounded f64 producer mode added

`simple_web_layout_render_html_draw_ir_fractional_result` now uses the real
Web parse/cascade/layout pipeline and resolves eligible absolute leaf boxes
from authored `px` tokens before integer culling. It emits DrawIR v3 f64
geometry with zero legacy coordinates; unsupported whole scenes produce an
explicit reason and zero batches. Applied CSS declarations are retained for
a strict allowlist, while pseudo-elements and unresolved external CSS reject.
The real-producer spec checks f64 transport, subpixel visibility and negative
paint cases, but has not run on a trustworthy Simple runner. The seven-degree
rotation, full case 02 pixels and physical Linux Vulkan evidence remain open.
