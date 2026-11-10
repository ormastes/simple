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

## 2026-11-11 status — P3 rt2 lane triage (worktree simple-p3-rt2-20261111)

**Verdict: LIVE (structural, by source audit at base 790b54f7c4fc);
reproduction BLOCKED — heavy native build, exact commands below.**

The designed fix (project the core-C supplement so it contributes only the
C-only gap symbols and localizes everything the `.so` already exports) is
NOT implemented at this base:

- `build_core_c_runtime_supplement_library`
  (`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:925`)
  still builds the FULL core-C archive (`build_c_runtime_library(.., false,
  true, false, ..)` — no projection/localization flag exists in that
  signature).
- The dynamic-runtime lane still appends that archive AFTER the shared
  runtime (`linker.rs:2203-2237`), and the block comment explicitly
  preserves the reported seam's mechanism: "a static definition never
  COLLIDES with a shared-object one — the executable's copy simply wins for
  the whole process, **including calls made from inside the runtime**."
  That is the ABI seam this doc reports (Rust-side `.so` callers binding to
  C implementations wherever the two representations differ).
- `git log --grep` over this lane since filing finds no fix commit;
  `bug_db.sdn` still registers this doc OPEN (P3). The 2026-11-07 child
  `hosted_native_all_rust_argv_overrides_c_array_owner_2026-11-07` fixed
  one concrete argv instance in the native_all composition; it does not
  project the dynamic-lane supplement.
- `scripts/check/check-rt-dual-implementation-ratchet.shs` does not
  mention/scoped-cover the dynamic lane (grep 'dynamic' → no match), so no
  ratchet currently pins the dual-definition count down.

Reproduction is not possible inside this lane: no `libsimple_runtime.so` /
`simple_runtime.dll` exists anywhere in this worktree (find: none; `build/`
holds only `review/`), and producing one plus the Stage4 driver link is a
heavy entry-closure native build — forbidden here. Exact commands needing
grant (Linux ELF lane, per the doc's measurement method):

```bash
# 1. build the shared runtime cdylib (aarch64/x86_64 linux, from repo root)
cargo build --profile bootstrap -p simple-runtime --features runtime-symbol-table \
  --manifest-path src/compiler_rust/Cargo.toml
# 2. link the Stage4 driver against it via the dynamic lane
SIMPLE_RUNTIME_PATH=src/compiler_rust/target/bootstrap \
  bin/simple.exe native-build --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/compiler/80.driver/main.spl \
  --runtime-bundle dynamic-runtime --output build/review/dyn_rt_driver
# 3. measure the dual-defined rt_* set
nm build/review/dyn_rt_driver | grep ' [Tt] rt_' | awk '{print $NF}' | sort -u > /tmp/exe_rt.txt
nm -D --defined-only src/compiler_rust/target/bootstrap/libsimple_runtime.so \
  | grep ' rt_' | awk '{print $NF}' | sort -u > /tmp/so_rt.txt
comm -12 /tmp/exe_rt.txt /tmp/so_rt.txt | wc -l   # doc-era value: 509
# 4. seam symptom oracle: run a 3-line array-handle hello under interpret + AOT paths
```

Labels: host-independent-source (static composition audit at pinned base);
blocked-repro (needs-grant commands above). No change made in this lane —
the fix is a linker/projection feature in the compiler/native_project
lane, deliberately not attempted here under the no-heavy-build constraint.
