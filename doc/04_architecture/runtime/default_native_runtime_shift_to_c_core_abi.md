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

**Unwinding.** `linker.rs`'s existing `omit_unwind` already drops the unwind
library on precisely this lane shape, and the shared runtime's own `NEEDED` list
is `libm`/`libgcc_s`/`libc`/`ld-linux` with no LLVM `libunwind`. The directive
and the code agree.

**Dependency.** The `$ORIGIN` RUNPATH approach assumes the shared runtime gains a
`SONAME`; it carries none today, which is why the linker passes `-L`/`-l` rather
than a bare path. Library packaging (SONAME, versioning, install layout) is owned
by a separate lane and must land alongside this one.

Gate: `scripts/check/check-stage4-dynamic-runtime-lane.shs`.
