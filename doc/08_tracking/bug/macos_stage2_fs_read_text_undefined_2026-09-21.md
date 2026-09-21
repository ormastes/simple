# macOS Stage2 links an unsupported filesystem alias

Status: source fix committed; native regression execution blocked by the
installed self-hosted compiler's HIR crash. Full bootstrap remains unverified.

## Failure and fix

The `fix/astra-stage3-hir-20260921` Stage2 native link reports the single
undefined symbol `_rt_fs_read_text`, referenced by
`_lib__nogc_sync_mut__sffi__fs__fs_read_text` in `libspl_objects.a(mod_860.o)`.
Its Stage2 runtime authority archive exports `_rt_file_read_text` and
`_rt_file_read_text_rv`, but does not export `_rt_fs_read_text` (`nm -g`).
The alias exists in `src/runtime/runtime_native.c`; that does not make it
available in the archive admitted for this bootstrap.

`std.nogc_sync_mut.sffi.fs.fs_read_text` now delegates to the existing
`std.nogc_sync_mut.io_runtime.file_read_nullable` owner. This uses the supported
read ABI, preserves nil versus empty text, and applies the existing native
host-path conversion. The compatibility function's nullable signature remains
the same; it no longer declares a separate runtime alias.

## Focused regression

`test/fixtures/compiler/native_fs_read_text_nullable.spl` calls the production
facade and returns nonzero for incorrect content, a missing path accepted as
readable, or an empty file treated as missing. Its empty-file fixture is
`test/fixtures/compiler/native_fs_read_text_empty.txt` (zero bytes).

From the repository root, with the admitted Stage2 archive directory supplied:

```sh
SIMPLE_LIB=src SIMPLE_RUNTIME_PATH="$STAGE2_RUNTIME_DIR" \
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_BOOTSTRAP=1 "$SELF_HOSTED_SIMPLE" native-build \
  --source src/lib --entry-closure \
  --entry test/fixtures/compiler/native_fs_read_text_nullable.spl \
  --runtime-bundle core-c-bootstrap --output build/native_fs_read_text_nullable
build/native_fs_read_text_nullable
```

Observed on 2026-09-21 with
`/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple`
(`Simple v1.0.0-rc.1`): native compilation exits 139 during HIR lowering of the
fixture, after parsing 18 modules. Diagnostics immediately before the crash
report an unresolved `Option` dependency in the imported filesystem facade.
The initial compatibility-facade import attempt also exited 139; the final
direct owner import avoids relying on facade re-export closure discovery but
does not resolve the installed compiler's crash. No Rust-seed fallback or full
bootstrap was run for this focused change.

The broader compiler/core/lib and MCP smoke gates must run after an executable
self-hosted compiler is available; this record does not claim verify PASS.
