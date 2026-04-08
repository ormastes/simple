# Examples Check

## examples/browser/test/compat

- Total: `10`
- Ok: `7`
- Error: `3`
- Timeout: `0`
- Crash: `0`

### Failures

- `examples/browser/test/compat/compare_render_pair.spl` `error` code=1 failed without diagnostics
- `examples/browser/test/compat/compat_tools_spec.spl` `error` code=1 2026-04-08T03:56:22.053641Z  WARN ThreadId(01) run_file_interpreted_with_args{path=examples/browser/test/compat/compat_tools_spec.spl}:evaluate_module:load_and_merge_module{path=["std", "spec"]}:load_and_merge_module{path=["matchers"]}: simple_compiler::interpreter::interpreter_module::module_evaluator::evaluation_helpers: 642: Export statement references undefined symbol name=be_true
- `examples/browser/test/compat/simple_render_html.spl` `error` code=1 2026-04-08T03:56:23.807943Z ERROR ThreadId(01) run_file_interpreted_with_args{path=examples/browser/test/compat/simple_render_html.spl}:evaluate_module:load_and_merge_module{path=["common", "render_scene", "engine2d_executor"]}:load_and_merge_module{path=["std", "gc_async_mut", "gpu", "engine2d", "engine"]}:load_and_merge_module{path=["std", "gpu", "engine2d", "backend_cuda"]}: simple_compiler::interpreter::interpreter_module::module_loader: 500: Failed to parse module path="/Users/ormastes/simple/src/std/gc_async_mut/gpu/engine2d/backend_cuda.spl" error=Unexpected token: expected Colon, found Comma

