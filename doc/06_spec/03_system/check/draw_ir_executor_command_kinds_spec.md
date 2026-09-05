# Draw IR executor command-kind admission

Executable companion:
`test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_executor_command_kinds_spec.spl`.

Requirement: AC-5.

`step("Execute or reject every Draw IR command kind")` invokes
`expect_draw_ir_kind_result`.

The receipt requires real execution for RECT, TEXT, and a resolved IMAGE, with
their pixels present in the CPU target. EDGE, PATH, GROUP, and PORT remain
schema-admitted but are explicitly counted as typed fallback rather than being
silently rendered or ignored.
