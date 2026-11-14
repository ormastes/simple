# AOP failure publication regression

Source: `test/02_integration/compiler/aop_failure_publication_spec.spl`.

The real `CompilerDriver.stage_emit_object` receives saved HIR advice with an
unsupported selector and advice form. It must return the first AOP diagnostic
as `CompileResult.CodegenError` before backend dispatch. The backend deliberately
cannot provide a successful artifact. Run with optional MIR transforms enabled.

Status: authored, **not executed** with the full compiler test runtime. The
separate native probe of extracted production gates does not prove this scenario.
