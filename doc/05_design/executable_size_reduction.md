# Executable Size Reduction Detail Design

Codex design, 2026-04-23.

## Runtime Symbol Retention

The linker reads global defined symbols from the selected runtime archive/object and global undefined symbols from generated objects, the main stub, and the generated init caller. It keeps only undefined symbols that the runtime actually defines, avoiding `-u` roots that would create new unresolved link failures.

Additional roots cover runtime lifecycle and indirect lookup paths: `__simple_runtime_init`, `__simple_runtime_shutdown`, `rt_set_args`, `rt_function_not_found`, string creation/access, and array creation/length.

## Release Size Check

The size script accepts explicit artifact paths or defaults to common local artifacts. It checks bytes with `wc -c`, classifies the artifact with `file`, applies basename-based budgets, and rejects unstripped release/package executables.

## Tests

Rust unit coverage builds tiny C objects and verifies that the runtime-retention set includes object undefineds and required roots while excluding unused runtime symbols.
