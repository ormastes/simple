# SMUX Windows native provider composition

Status: authored source composition; native selection, execution, and SSpec
docgen remain **TEST_BLOCKED** pending a qualified rebuilt Pure-Simple producer.
This guide is not an admission receipt.

Requirement: `REQ-SMUX-WINDOWS-NATIVE-PROVIDER-SELECTION`.

Windows native SMUX selects explicit provider source roots. Keep the stable
`std.sys.pty` and `std.nogc_sync_mut.sosix.network` imports in applications.
Place `src/providers/windows_native/lib` before `src/lib` in the Windows native
command only. Other products and interpreter/Rust execution continue using
their existing source facades and runtime handlers. No OS-dependent app branch,
global GC-family override, runtime symbol-presence test, or compiler cfg change
participates in this selection.

| Stable module | Selected overlay leaf | Provider |
|---|---|---|
| `std.sys.pty` | `src/providers/windows_native/lib/sys/pty.spl` | `std.nogc_sync_mut.io.windows_pty_owner` |
| `std.nogc_sync_mut.sosix.network` | `src/providers/windows_native/lib/nogc_sync_mut/sosix/network.spl` | `std.nogc_sync_mut.io.windows_tcp` |

The TCP overlay preserves all 23 existing SOSIX export aliases and changes no
HTTP/UDP provider. The PTY overlay preserves the existing facade API and exposes
the native incremental-write/resize operations required by the owner service.
The native provider modules remain responsible for their real Win64 ABI,
resource ownership, bounds, backpressure, and cleanup semantics.

## Canonical ordered native commands

Use the current native Windows host. Set `$qualifiedProducer` to the exact
qualified Pure-Simple compiler and `$productCache`/`$productExe` to a new isolated
Phase2 row. Record its SHA-256, frozen source revision, linked runtime, command,
exit code and logs. After actual Phase2 qualification, repeat using the qualified
Phase3 producer and separate output/cache paths. The commands below are pending
templates; no old diagnostic compiler is evidence for current source.

```powershell
& $qualifiedProducer native-build --source src/providers/windows_native/lib --source src/os --source src/lib --source src/app/hosted_apps --entry-closure --entry src/app/hosted_apps/smux_client.spl --backend=llvm --cache-dir $productCache --output $productExe
```

The source root order is the product selection manifest. There are four explicit
roots, within the focused CLI's five-root limit. Do not pass this Windows-only
root to another target or to interpreter test execution. Native Windows linker
support already includes Kernel32 and Winsock libraries; successful linking and
real system scenarios must establish that the selected provider ABI works.

Compile the independent selection fixture with the same composition:

```powershell
& $qualifiedProducer native-build --source src/providers/windows_native/lib --source src/lib --source test/fixtures/compiler_entrypoint/windows_native_provider_selection --entry-closure --entry test/fixtures/compiler_entrypoint/windows_native_provider_selection/main.spl --backend=llvm --cache-dir $selectionCache --output $selectionExe
& $selectionExe
```

Required fixture compile/run exits are zero; expected stdout is
`windows native provider selection PASS` followed by a newline. Preserve selected
physical module paths in closure/HIR evidence and require that the PTY source
closes over `windows_pty_owner`, and the SOSIX network source closes over
`windows_tcp`. This fixture checks source selection and invalid-handle contracts;
live shell, TCP round trips, detached draining and resize still require the
smux/provider system scenarios.

## Existing selection path and lifetime

`bootstrap_focused_native_build.spl` preserves ordered CLI sources as scalar
arguments to `aot_native_project_with_backend_fixed`. That API writes them in
order to `options.input_files` and `bootstrap_input_0..4`, appends the entry, and
sets `options.mode = CompileMode.Aot`.

`driver_source_pipeline_loading.spl` captures those inputs as
`closure_source_roots` before entry closure reduces the input scan to the entry
alone. Explicit `options.native_source_roots` and snapshot identity, when
present, supply the same root contract through `native_source_root_paths_v1`.
`_driver_resolve_source_root_entry_import_from_v1` searches these roots before
checkout fallback. A root ending in `lib` recognizes both `std` and `lib`
prefixes. The selected physical owner must agree with any already-loaded owner;
a mismatch fails instead of restoring a default provider.

The source loader records the selected physical content/path and aliases it to
the requested logical import name. `driver_hir_pipeline_lowering.spl` builds
frozen module surfaces from those same `ctx.modules` and `ctx.sources`; HIR does
not independently choose a new provider. Existing composition and family-owner
specs cover this mechanism, and the new Windows composition spec asserts the
actual selected paths with overlay present, absent and reordered.

Native/interpret mode exists accurately in `CompileContext.options.mode`, and
the parser driver observes `CompileMode.Aot` (or explicit CLI `aot`) while
managing parser scope lifetime. However, cfg evaluation receives only OS/arch
target facts. `_pp_preprocess_conditionals_target_receipted_v1` temporarily sets
process globals for target OS/arch and resets them after each preprocessing
call. Neither its receipt nor `cfg_eval_key_value` carries execution mode;
feature predicates are always false. Adding `@when(native)` would therefore
require a future compiler/context/cache-identity design. The existing explicit
source composition avoids that unrelated compiler change.
