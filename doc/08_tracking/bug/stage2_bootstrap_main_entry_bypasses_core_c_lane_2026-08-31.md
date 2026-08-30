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
