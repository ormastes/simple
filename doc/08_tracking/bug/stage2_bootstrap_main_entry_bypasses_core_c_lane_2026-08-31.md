# Stage 2's `bootstrap_main` entry silently overrides `--runtime-bundle core-c-bootstrap`, leaving 103 `rt_*` undefined

- **Date:** 2026-08-31
- **Status:** ROOT-CAUSED, not fixed — the fix is an architectural choice, set out below
- **Supersedes the open half of** `bootstrap_stage2_windows_link_unresolved_rt_and_dup_kernel32_2026-08-24.md` (Blocker A)

## Where the lane now stands

On `x86_64-pc-windows-msvc`, Stage 2 **compiles every `.spl` file** and reaches
the native link, which fails:

```
LNK2019 x151   (103 distinct rt_* names)
LNK2005 x18    (duplicate import descriptors -- separate blocker)
LNK1120        151 unresolved externals
```

## Root cause

Stage 2 is invoked with `--runtime-bundle core-c-bootstrap`, the lane whose
whole purpose is to build and link the **C** runtime archive. That request is
**silently discarded**.

`native_project/config.rs:357-363` returns early:

```rust
if is_bootstrap_main_entry(&self.entry_file) {
    if let Some(native_all) =
        bootstrap_hosted_native_all_runtime(self.config.runtime_path.as_deref(), native_all_name, temp_dir)
    {
        return Ok(Some((native_all, true)));
    }
}
```

Stage 2 compiles `src/app/cli/bootstrap_main.spl`, so this fires first and pins
the runtime to `simple_native_all.lib`. The core-C branch that would honour the
requested bundle sits **27 lines further down** (`config.rs:384`) and is never
reached.

## Evidence

`simple_native_all.lib` (354,268,764 bytes) does not contain the symbols:

| symbol | defined in native_all |
|---|---|
| `rt_iocp_create` | **0** |
| `rt_event_ports_create` | **0** |
| `rt_cpu_count` | **0** |
| `rt_io_udp_bind` | 1 |

They are defined in `src/runtime/runtime_native.c`, and that file is compiled by
**no lane in this build**: the only matching object anywhere under the output
tree is `runtime_native_gpu_stub.o`. It is absent from the Rust runtime crate's
`build.rs` list and is compiled only by `build_c_runtime_library`
(`tools.rs`) — the core-C path that the early return skips.

Note the ordering of two facts, because they were confused before:
`runtime_native.c` **now compiles cleanly under clang-cl** (fixed earlier in
this branch). That was necessary and is not sufficient — nothing invokes it.

## Why Linux does not show this

The undefined families are platform-selected: `rt_iocp_*` (Windows),
`rt_kqueue_*` (BSD/macOS), `rt_event_ports_*` (Solaris). A Linux build emits
references to the epoll family instead, and those *are* satisfied. The early
return is equally wrong on Linux; it simply has no visible consequence there.

## The fix is a choice, and it is not mine to make silently

1. **Honour the explicit bundle.** Let `--runtime-bundle core-c-bootstrap` win
   over the entry-name heuristic. Most faithful to the request. Risk: the
   `bootstrap_main` branch exists to supply bootstrap-CLI symbols from
   native_all; dropping it may trade one undefined set for another.
2. **Link both archives.** Keep native_all, add the core-C archive. Risk is
   measured and severe: `8ca87866c6` recorded **475 symbol collisions** when
   `runtime_native.c` was merely added to the Rust runtime build, and both
   archives define overlapping `rt_*`.
3. **Narrow the early return** to fire only when the bundle was NOT explicitly
   requested (i.e. keep it as a default, not an override). Smallest change,
   preserves existing behaviour wherever no bundle is named.

Option 3 looks strictly safest, but all three change a lane-selection contract
that every platform shares, and this host cannot test Linux or macOS. Recorded
rather than applied.

## Not to be confused with

The 18 `LNK2005` duplicate import descriptors are a **separate** blocker with
its own record (`windows_whole_archive_duplicate_import_descriptors_2026-08-30.md`)
and its own cause (unconditional `/WHOLEARCHIVE`). Fixing either does not fix
the other; both must clear before Stage 2 links.

## Verification appendix — spl_* / _abi_timestamp_* / _fltused group (2026-08-31, second pass)

The C-runtime symbol group flagged before the two-archive supplement landed
(`c83d2325deb` supplement, `45fdcd42cf0` clang-cl compile fixes,
`c41a37c3f73` /FORCE:MULTIPLE layering) was re-verified per symbol with
`llvm-nm --defined-only` against the archives the Stage 2 link actually
consumes (`stage2-runtime-authority/simple_native_all.lib`, 343,351 defined
symbols; `core_c_bootstrap_supplement/simple_runtime.lib`, 2,228 defined
symbols; both nm exits 0), and against the 2026-08-31 08:27 Stage 2 link log
(`build/w/logs/x86_64-pc-windows-msvc/stage2-native-build.log`), which reaches
LNK1120 with 98 unresolved — none of them in this group:

| symbol (referenced by libspl_objects.a) | defining .c | native_all | core-C supplement |
|---|---|---|---|
| spl_dlopen_checked / spl_dlsym / spl_dlsym_checked / spl_dlsym_process_checked / spl_dlclose | runtime_native.c fallback copy (`!SIMPLE_RUNTIME_DYNLOAD_OWNER`, :7240) | yes | yes |
| spl_dynlib_snapshot_linux | runtime_native.c:7283 | no | **yes** (sole provider) |
| spl_str_ptr | runtime_native.c:11721 | yes | yes |
| spl_thread_cpu_count | runtime_legacy_core.c:126 | yes | yes |
| spl_wffi_* (6 referenced: call_i64, call_i64_checked, call_bool0/1_checked, try_call_i64_out, i64_checked_result) | runtime_native.c | yes | yes |
| spl_backend_plugin_run_v1 | runtime_backend_plugin.c (list 3 / build.rs) | **yes** | no — deliberately not added |
| _abi_timestamp_* (9) | none — Simple codegen weak defs (`W`) in libspl_objects.a from src/lib/common/time_utils.spl:185-210 `@export` wrappers | n/a | n/a |
| _fltused | none — MSVC CRT data symbol, `D` in msvcrt.lib (14.38.33130), pulled by /MD defaultlib directives | n/a | n/a |

Deliberate NON-additions, each because adding would duplicate an existing
provider (the 8ca87866c6 collision class):

- `runtime_dynload.c` to the core-C list: runtime_native.c's fallback copies
  already ship in the same archive; adding it without also defining
  `SIMPLE_RUNTIME_DYNLOAD_OWNER` duplicates spl_dlopen/dlsym/dlclose INSIDE
  one archive.
- `runtime_backend_plugin.c` to the core-C list: native_all already defines
  `spl_backend_plugin_run_v1` (measured `T`).
- `runtime.c` to the core-C list: would intra-archive-duplicate `spl_str_ptr`
  (runtime.c:1268 vs runtime_native.c:11721) among others.
- A source definition for `_fltused`: it is a CRT symbol; its earlier
  appearance as unresolved means that link ran without CRT defaultlibs, a
  link-flags condition, not a missing source.
- `spl_dlclose_checked`: zero references anywhere in the tree — nothing to fix.

`SIMPLE_BOOTSTRAP_TIMESTAMP_COMPAT` (runtime/build.rs) is the seed-side C
compat for the `rt_timestamp_*` ABI and is unrelated to the `_abi_timestamp_*`
names, which exist only as the internal names of time_utils' exported wrappers.

**Status update: partially fixed.** The supplement resolves every symbol in
this group and every rt_* that HAS a C definition in a core-C member. The
residual 98 unresolved at 08:27 are a different class — e.g. `rt_cpu_count`,
`rt_time_now`, `rt_uuid_v4`, `rt_simd_add_f32x4`, `rt_iocp_deregister` are
defined in NEITHER archive and have no C definition anywhere non-test
(interpreter-only shims in `src/compiler_rust/compiler/src/interpreter_extern/*.rs`);
`rt_readdir` et al. live only in `runtime.c` (list-2-only). This matches the
31-build-config / 37-implement split of `8a740c40f9` and is owned by the
sibling lanes, not this record.
