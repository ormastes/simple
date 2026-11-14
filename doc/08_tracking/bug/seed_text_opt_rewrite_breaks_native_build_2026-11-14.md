# Seed native-build rewrote `text?` to `text`, breaking Option matches (2026-11-14)

Status: partial (verification-pending for the rewrite fix; stall still open)

## Symptom
Seed `native-build` of devhub / llm_caret / mail_credentials timed out at 900 s.
A `match s: case Some(v)` over a `text?` param/local failed SPL-PAT-001
("expects Option<T>, found text").

## Root cause
`compile_file_to_object` (src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs)
unconditionally did `source.replace("text?", "text")` on the non-bootstrap path,
erasing the Option type.

## Fix
New helper `normalize_text_opt_if_unparseable`: parse the pristine source first;
rewrite only if the parse fails (same parse-first rule as the module loader).

## Evidence
Tests in native_project/tests.rs (`cargo test --profile bootstrap -p simple-compiler --lib text_opt_`):
- with fix: 2 passed, 0 failed.
- helper forced to the old unconditional rewrite: `text_opt_kept_when_source_parses` FAILED, other passed.
- fix restored: 2 passed.

## Resolution of the stall (2026-11-14, same day)
The 600/900 s timeouts were NOT compile time. Without `SIMPLE_NATIVE_BUILD_RUST=1`
the seed's dispatch (`driver/src/main.rs`, `native_build_rust_override`) treats
`native-build` as a pure-Simple tool and INTERPRETS `src/app/cli/native_build_main.spl`
— the path `misc_commands.rs` already documents as pathological (28 GB RSS,
killed at 5508 s). Diagnostic: no `[native-build] parallelism:` line is ever
printed even with `SIMPLE_NATIVE_BUILD_TRACE=1`; one core at 100 %, 1.6 GB RSS,
log frozen after `workarounds: incomplete coverage`.

With `SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NATIVE_INCREMENTAL=1 --cache-dir <stable>`
and the llvm-mingw UCRT toolchain first on PATH (the system
`C:\Program Files\LLVM` clang has no `libclang_rt.builtins.a` for
`x86_64-w64-windows-gnu`, so linking fails there), measured on this host:

| Target | compile | link | run |
|---|---|---|---|
| devhub | 300 files, ~60 s cold; 1 rebuilt / 299 reused warm | OK, 5.8 MB | `--help` exit 0, 61 lines |
| mail_credentials | 131 files | OK, 2.6 MB | exit 2 "Unknown credential operation" (no `--help`; native dispatch works) |
| llm_caret | 662 files; 1 failing | — | blocked by the bare-name enum collision below |

Real compile defects found and fixed on the Rust path (each had hidden behind
the stall):
- `src/lib/nogc_sync_mut/http_client/types.spl` called the imported
  `nogc_sync_mut.http.url.url_decode(encoded:)` with the named arg `text:`
  (copied from the `gc_async_mut` twin, which defines its own
  `url_decode(text:)`): `hir: call to url_decode names unknown parameter text`.
  Fixed to positional calls; spec
  `test/01_unit/lib/http_client/sync_query_string_decode_spec.spl` (3/3).
- `src/lib/nogc_async_mut/container/providers/windows/simple_container_adapter_v2.spl`:
  10 two-arg `rejected(action, reason)` calls relied on the default
  `status = RUNTIME_STATUS_BLOCKED`, which the seed cannot evaluate
  cross-module ("default is not a call-site constant"). Made explicit.
  Seed limitation stays open: a module-level constant default should be
  inlinable at the call site.

Still open (seed): `llm_caret/main.spl` `HttpStatus.Ok` resolves to
`nogc_sync_mut.io.http_client_types.HttpStatus` (variant `OK`) instead of the
explicitly imported `nogc_sync_mut.http_server.types.HttpStatus` (variant `Ok`)
— the seed registers enums by bare name (`warning[enum-bare-name-ambiguous]`,
`evaluation_helpers.rs:1062`) and the MIR lowering takes the last one. Tracked
in `seed_enum_bare_name_collision_native_2026-11-14.md`.
