# GUI Retained Idle Frame Evidence — 2026-08-12

Status: **CORRECTNESS PASS / ZERO-WORK IDLE PATH / 8K80 UNPROVEN**

The hosted GUI producer continues to lower its widget semantic tree directly to
the canonical `DrawIrComposition`; no GuiIR schema or private drawing path was
added. After a retained surface has been seeded, a canonical
`DAMAGE_PLAN_NONE` now returns an idle Engine2D outcome before
`UISession.submit_widget_draw_ir` is called.

The focused regression passed 2/2 examples. It seeds a real widget session,
builds an empty `DirtyTilePyramid` plan, and asserts that the idle frame has
zero rendered operations, zero rendered tiles, no requested readback, and an
unchanged `draw_ir_submission_revision`. The unchanged revision is the producer
oracle: widget-to-DrawIR lowering did not run. With production
`readback_frame=false`, the idle helper performs no raster, batch submission,
presentation, or device transfer. An explicit evidence caller may request
retained pixels; the CPU test verifies `cpu_mirror` provenance and 512 pixels,
but Vulkan readback/transfer provenance is not covered by this row.

This is structural frame-switching evidence, not an 8K/80 timing claim. The
focused interpreter command took about 32 seconds including compiler/test-runner
startup and the initial font-backed seed, none of which is an idle-frame timing.
A production native 8K row remains unavailable until the no-stub self-hosted
compiler artifact can be produced.
