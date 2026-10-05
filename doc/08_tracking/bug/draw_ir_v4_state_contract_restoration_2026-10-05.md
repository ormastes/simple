# Restore the missing DrawIR v4 state contract

## Evidence and scope

The completed 9d484 early Phase 4 full-CLI build reported a missing
`draw_ir_command_has_unsupported_v4_state` in Engine2D. Final log SHA-256:
`0850b659da9f5a612051ed073f9062414329818219bce1f96c3f044b6be01340`.
The existing Ganesh provider also reads fractional geometry, affine transforms
and raster policy, while the shared DrawIR owner still contained only v2 fields.
A constant predicate would hide lost state rather than repair the contract.

The record shapes and policy names are attributed to the preserved, unfinished
`C:/dev/simple-draw-ir-v4-contract-20261004` draft. That worktree is unchanged.
Its diff/patch/SDN files were identical to its base and carried no v4 state.
The existing design is
`doc/03_plan/ui/unified_surface_draw_ir_and_html_css_conformance.md`; existing
fractional producer specifications are `web_fractional_case02_v4_spec.spl` and
`web_fractional_leaf_producer_spec.spl` under the system UI feature tests.

## Contract

The new fields are optional fractional geometry, optional affine transform, and
raster policy with the legacy aliased-pixel-center default. Integer constructors
and legacy SDN output retain their previous semantics. Batches/compositions
promote to the v4 schema when actual command payload requires it.

Copy/embedding, Engine2D geometry copying, SDN, diff detection, patch application
and its equality oracle retain the three fields. SDN carries finite binary64
values as fixed-width IEEE-754 hex, avoiding display-format rounding. Invalid
width/digits and non-finite values are rejected explicitly; the checked scalar
decoder returns an error. The full `sdn_to_draw_ir_checked` decoder validates
presence flags, complete payloads, duplicate/unknown fields and explicit empty
raster policies before constructing any composition; it rejects contradictory
state rather than treating it as legacy absence. The established non-Result
SDN API reports a
panic rather than silently converting malformed v4 geometry to zero. The
existing v2 parser's broader permissive input behavior is not redesigned here.

Patch damage uses transformed rectangle corners and outward rounding before
integer conversion. Non-finite/out-of-range bounds or extents are rejected,
not truncated into a smaller accepted damage region. A changed fractional,
affine or raster payload creates a full-command update even when legacy
integer geometry is unchanged.

The shared `unsupported_v4_state` predicate retains its existing consumer
meaning: the Skia scalar wire accepts fractional geometry independently but
cannot consume affine/raster extensions. Legacy Engine2D additionally rejects
fractional geometry before occlusion, clipping and raster execution; strict
integer device paths reject it too. The tracked integer v2-to-v3 and mxGraph
adapters reject v4 input instead of silently discarding the new state. No
unsupported renderer is relabeled as supporting v4.

## Missing historical API and validation limits

At pinned base `57e9744fdb48877091d9f9a98be1c19748140587`, tracked source has no
`ui_ir` path, `struct UiIr` or `fn draw_ir_to_ui_ir`; a bounded history lookup of
the claimed common UI path also found no implementation. The design and older
system specs refer to this absent API. This repair does not invent a new backend
execution representation or claim those tests can run. The tests' named
`simple_web_layout_render_html_draw_ir_fractional_result` producer likewise has
no definition in tracked browser-engine source at this base. Actual tracked v3
and mxGraph conversions are guarded as described above.

Nine pure contract cases and four real CPU executor cases are authored but
**UNRUN**. They cover defaults, SDN roundtrip, binary64 edge representations,
invalid scalar payloads, legacy SDN, state-only diff/patch, embedding, transformed
damage, full-decoder malformed records, and explicit CPU rejection through
normal, prepared-damage and direct damaged replay. The spatial index classifies
v4 commands as uncertain because `_engine2d_draw_ir_plain_fill` rejects them;
both indexed and linear damage selectors retain those commands before the
render loop reports their unsupported state. New cases use off-screen stale
integer bounds with fractional/affine geometry inside the damage region. Source checks are not bootstrap, graphical
output, performance or release qualification. Full native verification and the
existing fractional producer system tests remain pending.
