# SimpleOS x86_64 kernel link gate reports ERROR: 10 files fail to compile (2026-11-23)

Gate: `scripts/check/check-simpleos-x86_64-kernel-link.shs --link-only`
(seed native-build, LLVM backend, `SIMPLE_NO_STUB_FALLBACK=1`, `--entry-closure`,
entry `examples/09_embedded/simple_os/arch/x86_64/os_entry.spl`).
Seed: LLVM-enabled build of release/1.0.0 `f3311bb8185`; release/1.0.0 `9d19b0be237`.

Verdict: `ERROR - nothing was checked (kernel native-build failed (rc=1))`.
`compiled=911 reused=0 failed=10`. The build aborts before link, so there is no
undefined-symbol count for x86_64.

## Failing files

| File | Error |
|------|-------|
| `src/os/kernel/loader/x86_64_simplebox_catalog_media_boot_v1.spl` | cannot resolve import `x86_64_auth_trust_config` (module exists nowhere in the tree) |
| `src/os/kernel/loader/x86_64_authenticated_media_fixture.spl`, `x86_64_scr2_native_catalog_policy_v1.spl`, `x86_64_signed_artifact_receipt_boot_policy_v2.spl` | same missing module, imported as `use x86_64_auth_trust_config.{...}` |
| `src/os/compositor/browser_compositor_backend.spl` | cannot resolve import `os.drivers.framebuffer.fb_font` (module missing; also "path segment `os` not found") |
| `src/os/kernel/loader/installed_artifact_boot_composition_v1.spl`, `simplebox_catalog_media_boot_v1.spl`, `simplebox_pinned_catalog_image_v1.spl`, `simplebox_signed_catalog_boot_ingestion_v1.spl` | hir: call to `_fail_v1` / `_pinned...` omitted (Unsupported feature) |
| `src/os/apps/terminal/terminal.spl` | hir: cannot infer field type: `BufferingTerminal.cols` (declared fields: buffer) |
| `src/os/apps/shell/_ShellTools/system_tools.spl` | llvm codegen: cannot resolve method call `str.parse_u64` |
| `src/os/tools/shell/ls/ls_tool.spl` | hir: cannot infer field type while lowering `tool_ls`: struct `ANY` field `name` |
| `src/os/userlib/_Window/client_methods.spl` | hir: cannot infer field type while lowering `WindowClient.create_window_with_process_id`: struct `ANY` field `value` |

## Also: `--entry-closure` does not narrow this build

The x86_64 entry pulls in shell, terminal, compositor, loader and userlib
modules; 911 files are compiled. The riscv64 entry reaches link with the same
flags. Either the x86_64 entry legitimately reaches all of this, or the closure
is over-approximating (e.g. via `use` of whole modules); this needs a closure
report to decide.

## To do

1. Create or restore `x86_64_auth_trust_config` and `os.drivers.framebuffer.fb_font`, or remove the imports.
2. Fix the HIR/type-inference errors above (compiler or source typing).
3. Re-run the gate; then handle whatever undefined symbols appear at link.

Until then the gate stays an honest ERROR (never a pass).
