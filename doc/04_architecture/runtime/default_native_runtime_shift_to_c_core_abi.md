# Default Native Runtime Shift To C-Core ABI

## Decision

Native app builds now distinguish two host runtime lanes:

- `simple-core`: the preferred pure-Simple lane when an ABI-complete pure-Simple core runtime archive is present. It links `libsimple_runtime.a` only and satisfies the narrow C-compatible host ABI.
- `core-c-bootstrap`: the C bootstrap lane when `simple-core` is not present or not ABI-complete yet. It also links `libsimple_runtime.a` only.

## Rationale

- Native builds must not silently escalate to the broad hosted runtime root.
- Host tools and small native apps need an auditable closure guard so size and dependency regressions fail loudly.
- Compiler/bootstrap entries must either build on the Simple/C lanes or fail closed; Rust-hosted/native_all fallback is not a supported runtime lane.

## Link-Selection Contract

1. `--runtime-bundle auto` resolves to `simple-core` when that lane is ABI-complete; otherwise it resolves to `core-c-bootstrap`.
2. `--runtime-bundle simple-core` forces the pure-Simple core lane and fails clearly if the lane archive is not installed yet or is ABI-incomplete.
3. `--runtime-bundle core-c-bootstrap`, `core-c`, `core`, `core_c`, and `runtime` all force the C bootstrap core lane.
4. `--runtime-bundle rust-hosted`, `hosted`, `hosted-runtime`, `rust-runtime`, and `all` are removed and fail closed.
5. The `simple-core` and `core-c-bootstrap` lanes may not fall back to `libsimple_native_all.a`; doing so is a hard error.

## Diagnostics

- If any native-build path would pull `libsimple_native_all.a`, the build fails with an explicit Simple/C-lane diagnostic.
- If a selected core lane link fails with unresolved hosted-only runtime symbols, port the missing ABI to `simple-core` or `core-c-bootstrap`; do not opt into a Rust-hosted lane.

## Amendment (2026-09-06): the `dynamic-runtime` lane for the Stage4 compiler entry

This document's Link-Selection Contract contemplated two hosted lanes and said
compiler/bootstrap entries "must either build on the Simple/C lanes or fail
closed". A third lane now exists, and it is a **deliberate departure recorded as
an owner directive**, not a reinterpretation of the text above.

**Directive.** Simple does not use unwinding; the self-hosted compiler must link
the dynamic runtime library.

**Why the contract could not simply be satisfied instead.** The Stage4 compiler
entry was hard-pinned to the core-C archive by `selected_runtime_library`
(`pipeline/native_project/config.rs`), which returned before any other runtime
could be considered. That archive carries only the Simple/C core ABI, so the
Stage4 link failed with 167 unresolved `rt_*` symbols, and rule 5 forbade the
only in-contract alternative. "Port the missing ABI to `simple-core` or
`core-c-bootstrap`" (see Diagnostics above) is a real path but a large one: the
missing surface is the Rust runtime's, not a handful of entry points.

**What the lane is.** `--runtime-bundle dynamic-runtime` links
`libsimple_runtime.so` and appends the core-C archive after it as a supplement.
The two are additive, not alternatives: measured on aarch64 Linux the `.so`
exports 1,646 `rt_*` that the archive never had, while 121 of the 122 symbols
the Stage4 closure demands but the `.so` lacks are the C-only entry points
(`rt_iocp_*`, `rt_kqueue_*`, `rt_event_ports_*`, `rt_alloc`, `rt_mmap_raw`) that
the archive still provides. A static definition never collides with a
shared-object one, so this needs no `--allow-multiple-definition`.

**What is preserved.** The two operative concerns of the decision above still
hold. There is no silent escalation: the lane is never inferred, only selected
by an explicit `--runtime-bundle dynamic-runtime`, and it is REFUSED for any
entry that is not the Stage4 compiler, so `auto`, `simple-core`,
`core-c-bootstrap`, `host-gpu`, and every freestanding/bare-metal target resolve
exactly as before. The closure stays auditable: one named shared object with a
readable `DT_NEEDED` list. `libsimple_native_all.a` remains barred everywhere
rule 5 barred it.

**Unwinding — corrected 2026-09-06.** An earlier draft of this amendment said the
shared runtime had "no unwind dependency". That was wrong and is retracted.
Measured: `libsimple_runtime.so` lists `libgcc_s.so.1` in `DT_NEEDED` and carries
**12 undefined `_Unwind_*`** symbols. `libgcc_s` IS the unwinder.

What is actually true, and is what the link change rests on, is narrower: the
`-lunwind` entry resolves nothing. On this host `libunwind.so.8` defines **0**
`_Unwind_*` while `libgcc_s.so.1` defines **18**, so the LLVM libunwind the
Stage4 link was being dragged toward could never have satisfied those symbols --
which is why chasing them was a dead end. `linker.rs`'s existing `omit_unwind`
already drops that entry on precisely this lane shape. Simple code does not
unwind; the Rust runtime it links against still carries the personality-routine
references every Rust cdylib does, and those resolve through `libgcc_s` like any
other Rust binary on the platform. No mismatched-ABI unwinder is symlinked
anywhere.

**Is the core-C supplement permanent, or a bridge? Both, in measured
proportion.** Of the 201 `rt_*` the Stage4 object closure demands that the `.so`
does not export, only **32** are compiled into the `.so` but bound local -- the
export defect recorded in
`doc/08_tracking/bug/cdylib_hides_c_runtime_exports_2026-09-06.md` (rustc passes
a `--version-script`; there is no `-fvisibility=hidden`). The other **169 are
absent from the `.so` entirely**: C-only entry points (`rt_close_fd`,
`rt_cpu_count`, `rt_call_ptr_*`, `rt_iocp_*`, `rt_kqueue_*`, `rt_simd_*`) that
were never in the Rust runtime and are properly the core-C archive's
responsibility.

So the supplement is **the permanent design for the 169** and a **bridge for the
32**. Fixing the version script would let those 32 come from the `.so` instead;
it would not remove the need for the archive. Do not read the supplement as a
workaround to be deleted when that bug closes.

**Dependency.** The `$ORIGIN` RUNPATH approach assumes the shared runtime gains a
`SONAME`. The artifact measured for this lane carries none, which is why the
linker passes `-L`/`-l` rather than a bare path -- a bare path would record the
build directory as `DT_NEEDED`. The packaging lane has since landed a real
`DT_SONAME` (`libsimple_runtime.so.0`) with an install script; once a build picks
that library up the caveat is discharged, and the `-L`/`-l` form is correct
either way.

Gate: `scripts/check/check-stage4-dynamic-runtime-lane.shs`.

## Amendment (2026-11-23, accepted by the owner): `host-gpu-native-all`

**Status: accepted (owner decision 2026-11-23).** Implemented in the seed and
the pure-Simple linker's bundle table so the GB10 qualification evidence has a
sanctioned build path. It admits `libsimple_native_all.a` for a non-bootstrap
entry, but only when the bundle is named explicitly (never inferred).

**Problem.** Blocker 8 in
`doc/08_tracking/bug/linux_gb10_n2_qualification_executable_blockers_2026-11-18.md`:
an ordinary GPU entry such as `src/app/test/vulkan_2d_qualification` calls the
synchronous Rust Vulkan runtime (`rt_vulkan_*`, `rt_engine2d_*`) and the C
provider registry (`rt_gpu_provider_*`, `runtime_dynload.c`). No sanctioned
lane links either of them.

- `core-c-bootstrap` links only `runtime_native.c`'s weak stubs. Measured: a
  3-line probe links cleanly and reports `vk_devices=0` on the GB10. The value
  is silently wrong.
- `host-gpu` is the core-C loader plus the hosted rlib. The Vulkan provider DSO
  path (`SIMPLE_VULKAN_PROVIDER_PATH`, `runtime_dynload.c`) has a 47-name
  required list (`simple_vulkan_required`). The qualification calls 84
  `rt_vulkan_*`, and `rt_vulkan_selected_device_identity_v1` is not in that
  list.
- `dynamic-runtime` is limited to the Stage4 entry. Two problems, *expected but
  not measured*:
  - the executable's weak C stubs would win over the `.so`;
  - without `native-all-provider`, the `.so` registry is the fail-closed Rust
    twins (`gpu_provider_twins.rs`, `runtime/build.rs`).

**What the lane is.** `--runtime-bundle host-gpu-native-all` (also accepted
through `SIMPLE_NATIVE_RUNTIME_BUNDLE`) links two archives, in this order:

1. `<runtime-path>/libsimple_native_all.a`, built with
   `cargo build --release -p simple-native-all --features vulkan`.
2. The core-C supplement, for the C-only names.

Native-all goes first so that one owner holds the argv family. The lane fails
closed when the archive does not define `rt_vulkan_init` and
`rt_gpu_provider_loaded`. It omits the external `libsqlite3` unless the entry
references sqlite. It needs no `-z muldefs`: the 12 `rt_vk_*` noop stubs in
`native_all` are compiled out under `vulkan`.

**What is preserved.** The lane is never inferred. `auto`, `simple-core`,
`core-c-bootstrap`, `host-gpu` and `dynamic-runtime` resolve exactly as before.
Rule 5 still holds for the two core lanes.

**Exit.** The lane retires when the Vulkan provider DSO covers the whole
synchronous surface and `host-gpu` can link these entries through the loader.
