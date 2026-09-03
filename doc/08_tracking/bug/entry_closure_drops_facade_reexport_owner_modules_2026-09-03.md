# Phase-1 entry closure never loads a facade's re-export OWNER modules

- Date: 2026-09-03
- Status: OPEN (compiler fix not landed — see "Why not fixed here")
- Platform: platform-independent (measured on Windows x86_64-pc-windows-msvc)
- Severity: blocks native-build of any program importing an `__init__.spl` facade

## Symptom

`native-build` of a 7-line program dies in phase 3 with `unresolved name` for
symbols that exist and resolve fine interpreted. Write this to
`build/tmp_dh/min1.spl`:

    use std.json.{json_parse, json_array_length}

    fn main() -> i64:
        val v = json_parse("[1,2,3]")
        print("{json_array_length(v)}")
        0

then run (exit status read directly on the next line, never through a pipe):

    /d/win-p3-mmap/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-admitted/simple.exe \
      native-build build/tmp_dh/min1.spl -o build/tmp_dh/min1.exe

(admitted binary sha256
`fcf473728180d790bc6e15892c59cadf2f12600b4825575b30e3ff91c20bcf86`)

rc=1, ~0.3 s. The log states the cause plainly: **`[build] parse 2/2`** — only
the entry and `src/lib/common/json/__init__.spl` were ever parsed. Not one json
submodule entered the closure, so every name the facade re-exports is
unresolved.

## Root cause — two spellings, both dropped

A facade declares its re-export owners in two ways, and phase 1 follows
NEITHER:

1. **`export <submodule>.*`.** The scanner DOES compute this edge —
   `_driver_entry_sibling_path`
   (`src/compiler/80.driver/driver_source_loading.spl:673`) turns
   `export array_ops.*` into `.array_ops`, and
   `_driver_cached_entry_source_scan` (:651) returns it as the 3rd tuple
   element. The phase-1 closure walk then **throws it away** —
   `src/compiler/80.driver/driver_source_pipeline_loading.spl:280`:

       val (_, cached_closure_imports, _, _) = _driver_cached_entry_source_scan(closure_src.path)

   `grep -n sibling` over that whole file returns zero hits. The CLI BFS
   (`src/app/io/_CliCompile/native_build_closure.spl:206-215`) consumes the
   same tuple element correctly — only the driver path is broken.

2. **`# Re-exported from X.spl` COMMENT directives.** HIR parses these as real
   export-origin records (`module_surface_export_origin_hints`,
   `src/compiler/20.hir/hir_lowering/module_surface_declarations.spl:137-168`),
   but no closure scanner reads comments, so the named owner never loads and
   `register_imported_symbol_inner` fails closed with `invalid export origin`
   (`src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:206`).

## Proof of the causal chain

Adding `use common.json.builder.{JsonBuilder}` to the test program — i.e.
forcing the owner into the closure by hand — removes the
`invalid export origin` errors and HIR passes. Nothing else changed.

## Blast radius

`git ls-files 'src/**/__init__.spl'` = 1118 facades carrying 2083
`# Re-exported from` lines. Several name files that **do not exist**
(`src/lib/common/json/mod.spl`, `src/compiler/99.loader/runtime/*.spl`,
`src/app/test_runner_new/*.spl`, `src/compiler/70.backend/ffi.spl`), so a fix
must NOT emit a closure edge for an unresolved marker: the closure loop calls
`ctx.add_error` on an unresolved dotted module, which would turn today's silent
drop into a hard failure of the whole-compiler closure that builds the stage
binaries.

## Fix sketch (unverified — needs a stage2 redeploy to test)

1. `driver_source_pipeline_loading.spl:280` — capture the siblings element and
   feed it into the same loop, deriving the dotted module path as
   `parent(closure_src.module_name) + sibling` (equivalent to resolving
   `"." + base` against `closure_dir`; both `_driver_module_name_from_path` and
   `_driver_try_entry_import_rel` agree on that mapping).
2. Extend `_driver_entry_sibling_module_paths` to also emit `.X` for
   `# Re-exported from X.spl`, matching what HIR already reads.
3. **Guard, mandatory:** resolve first, emit only on success; an unresolved
   sibling/marker edge must be `log_phase`-only, never `add_error`. Unlike a
   `use`, these are hints and 2083 of them exist, some stale.

## Why not fixed here

The change lives in the compiler; the only Windows compilers available in this
session are prebuilt (`bin/simple.exe` is the Rust seed and cannot native-build
even a hello world here; the stage2 binary is read-only). A FAIL->PASS proof
therefore needs a stage2 redeploy, which is blocked separately. Two affected
facades were repaired data-side instead (`6014aa5385d`, `0a3963ca0d5`), which
took `native-build src/app/devhub/main.spl` from 175 HIR errors to 21.

`src/lib/nogc_sync_mut/io/__init__.spl` is the same shape and still broken
(`unresolved name: time_now_unix_micros` from
`src/app/devhub/cmd_daily_debug.spl:11`); it was deliberately NOT patched
data-side because `export use` edges there would pull audio/cuda SFFI into
every closure.

## Not fixed upstream

Both defect sites are byte-identical at `origin/main` (verified 2026-09-03 with
`git show origin/main:<path>` while this tree was 83 commits behind):
`driver_source_pipeline_loading.spl:280` still discards the siblings element,
and `src/lib/common/json/__init__.spl` still carries
`# Re-exported from mod.spl` with no `mod.spl` in the tree.

## Cross-platform

Nothing platform-specific: this is the shared driver closure walk. Both landed
data fixes are stdlib content with no platform code, and the interpreter lane
was re-verified after each (`bin/simple run src/app/devhub/main.spl --version`
-> `devhub 0.1.0`).
