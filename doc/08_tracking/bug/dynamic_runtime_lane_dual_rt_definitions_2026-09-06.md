# Dynamic-runtime lane links 509 rt_* twice (executable + .so), and an ABI seam shows

Status: OPEN — top residual risk of the `dynamic-runtime` lane
Component: `pipeline/native_project/linker.rs` (dynamic lane), `src/runtime`

## What was built

The Stage4 compiler DRIVER entry (`src/compiler/80.driver/main.spl`) linked
successfully on `--runtime-bundle dynamic-runtime`: 813 modules, 16 MB binary,
`ldd -r` reports **0 undefined symbols**, RUNPATH `$ORIGIN:$ORIGIN/../lib`,
DT_NEEDED `libsimple_runtime.so`, no libunwind. It runs and prints from a
three-line hello world under the interpret path.

## The defect

The lane links the shared runtime AND appends the core-C archive as a
supplement (the archive supplies ~169 C-only entry points the `.so` never had).
Measured on the produced binary:

- `rt_*` defined **inside the executable** (pulled from the core-C archive): 628
- of those, also **exported by `libsimple_runtime.so`**: **509**

A static definition does not collide with a shared-object one — the
executable's copy simply wins process-wide — so the link succeeds. But it means
Rust runtime code inside the `.so`, compiled against Rust's value
representation, now binds to the **C** implementations for those 509 names.
Where the two representations differ, that is a live ABI seam.

It is observable, not theoretical. Both the interpret and AOT paths emit:

```
[simple-runtime][error] rejected invalid array handle before dereference;
probable compiler/FFI ABI mismatch (value_bits=0x...)
```

emitted by `src/runtime/runtime_native.c` — i.e. the C copy in the executable
rejecting a handle it does not recognise. The interpret path still prints the
program's output; the AOT path (`-c`) fails with `ERROR=1`.

## Why the obvious fix does not apply

Archive members resolve at OBJECT granularity: pulling `runtime_native.o` to
satisfy `rt_iocp_create` drags in every other symbol that TU defines, which is
where the 509 come from. Reordering does not help — static always wins over
dynamic.

## Designed fix (not implemented)

Project the core-C supplement the way
`build_stage4_rust_runtime_projection_archive` projects the Rust runtime, but in
the opposite direction: retain only the symbols the `.so` does not export and
localize the rest, so the archive contributes exactly the ~169 C-only entry
points and nothing that the shared runtime already owns. That removes the seam
by construction rather than relying on precedence.

## Related

- `doc/08_tracking/bug/cdylib_hides_c_runtime_exports_2026-09-06.md` — 32 of the
  201 gap symbols are hidden by the cdylib version script; fixing that shrinks
  the supplement but does not remove it.
- `scripts/check/check-rt-dual-implementation-ratchet.shs` — the repo's existing
  position on parallel `rt_*` implementations.
