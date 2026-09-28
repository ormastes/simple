# Target 5 diagnostic compiler cannot link with staged core runtime bundle

Status: open; blocks a current-source diagnostic compiler and full CLI Stage4
qualification. The focused 48-unit declaration accessor regression passes.

Using the staged pure-Simple compiler with `--entry-closure`, `--threads 8`,
`--source src/compiler`, `--source src/lib`, and entry
`src/compiler/80.driver/main.spl` got past source compilation but failed at
native link. The linker reported 122 generated-code runtime references without
definitions, including `rt_cranelift_*`, `rt_file_view_*`,
`rt_pinned_archive_*`, `rt_driver_*`, and `rt_process_run_with_limits`. The
bounded run ended after 133.36 seconds with 3,558,148 KiB peak RSS. No
diagnostic compiler binary was produced, so the full CLI was not run.

An earlier eight-thread compile stopped in `pipeline_fn.spl` because the
staged LLVM compiler could not materialize `OptimizationConfig` through the
`compiler.mir_opt` facade. Importing the enum from its defining
`mir_opt_integration.spl` module got compilation to the link boundary. A
four-thread attempt timed out at 180 seconds before link; it did not yield a
verdict on the enum or runtime bundle.

Next step: select or build an admitted runtime bundle that actually defines
the listed symbols for this compiler entry, then rebuild with entry closure
and run the full CLI parse, Stage4 symbol, size, and startup checks. Do not
use `SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1`: that would leave NULL GOT entries and
could crash at first use. Keep the PR draft until the end-to-end run passes.

## Bundle-path check

The available `libsimple_native_all.a` defines 108 of the 122 missing names,
but passing its directory with `--runtime-bundle host-gpu --runtime-path` to
the September 8 staged compiler still produced exactly the same 122-symbol
link failure (17.22 seconds, 1,369,464 KiB peak RSS). The staged tool did not
admit that archive as a provider for this entry. A newer September 27 Rust
seed was used only for bootstrap of a current-source diagnostic compiler; it
passed JIT setup but timed out at 240 seconds before native output, with RSS
near 1.3 GiB. Neither run produced a diagnostic compiler or full CLI proof.

The next build route needs a current, admitted pure-Simple bootstrap compiler
and an explicitly verified runtime provider binding. Merely supplying a path
to the old staged tool does not fix the link.
