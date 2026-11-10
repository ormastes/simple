# arm64 `arm64-desktop-engine2d` media phase: seed native codegen cannot compile two `src/os/apps/dbd/` bodies (2026-09-01)

Status: **OPEN**. Fifth blocker in the chain behind the arm64 WM+Vulkan pixel
gate. Found after clearing three earlier prerequisites in a fresh
`origin/main` worktree.

## Prerequisites cleared first (each was a separate hard stop)

1. `build/os/sysroot-aarch64/lib/crt0.o` missing.
   `sh scripts/os/simpleos-sysroot-aarch64.shs` -> rc 0,
   `[sysroot-aarch64] done`. (Confirms the `wchar.h` `__WCHAR_TYPE__` fix.)
2. `build/os/simple-core-simpleos-aarch64/libsimple_runtime.a` missing.
   `SIMPLE_BINARY=<fresh seed> sh scripts/os/simpleos-core-archive.shs --target
   aarch64-unknown-simpleos --out-dir build/os/simple-core-simpleos-aarch64
   --backend cranelift` -> `parts_built=19 parts_failed=0`, rc 0.
   (`--backend llvm`, the script default, still fails every part.)
3. The payload build selected a compiler with the **stale** parser and died with
   `failed to parse src/os/apps/dbd/dbd.spl during discovery: expected
   expression, found Newline`. Cleared by
   `SIMPLE_BUILD_COMPILER=<fresh seed>`, an escape
   `scripts/lib/simple-compiler-select.shs:269` honours explicitly (it warns
   `artifacts built with it will FAIL the provenance guards` — accepted here,
   because this lane is a firmware-handover probe, not an attested artifact).

## The blocker

With the fresh seed selected, the parse error is gone and the failure moves to
**native codegen**:

```
[CODEGEN BODY] Function 'DbdProvisioningOwnerV1.ready' body compilation failed:
  GlobalLoad: unresolved identifier 'provider'
  (not a global, function, const-data name, or import)
[CODEGEN BODY] Function 'DbdLiveClientSessionV1.create' body compilation failed:
  GlobalLoad: unresolved identifier 'DbdTransactionOwnerV1'
  (not a global, function, const-data name, or import)
...
[scenario][arm64-desktop-engine2d] phase=media FAILED   (rc=1)
```

Both sources are ordinary, valid Simple:

- `src/os/apps/dbd/dbd_provisioning.spl:114` — `provider.configured` inside
  `pub fn ready()`, i.e. **implicit-self field access** in a class method.
- `src/os/apps/dbd/dbd.spl:208` — `DbdTransactionOwnerV1.new()`, a **static
  call on a class imported by `use`** at `:45` and already used as a field type
  at `:197`.

So the seed's native backend fails to resolve (a) an implicit-`self` field and
(b) an imported class name in static-call position, and reports both as
`GlobalLoad: unresolved identifier`. It is a compiler gap, not a source defect;
the sources were deliberately NOT rewritten to appease it.

`SIMPLE_ALLOW_STUB_FALLBACK` was **not** set — the runner offers it and it is
forbidden by the lane rules; emitting empty stubs for a DB daemon's session
constructor and readiness predicate would produce a silently wrong image.

## Consequence

`build/os/fat32-arm64.img` is not produced, so
`build/os/simpleos_arm64_desktop_engine2d.elf` is never reached and
`scripts/check/check-simpleos-arm64-wm-vulkan-pixel-evidence.shs` still returns
`ERROR — nothing was checked` (rc 2).

Blocker 2 of `arm64_wm_vulkan_real_firmware_lane_blocked_2026-09-01.md` — the
AAVMF -> `BOOTAA64.EFI` -> `kernel.elf` `protocol: linux` handover — therefore
remains **UNPROVEN**. No boot was attempted.

## Host prerequisites verified present (so they are not the blocker)

`/usr/share/AAVMF/AAVMF_CODE.fd` + `AAVMF_VARS.fd`, `vendor/limine/BOOTAA64.EFI`
(274432 bytes), `qemu-system-aarch64`, `mkfs.vfat`, and a real host Vulkan
(`NVIDIA TITAN RTX`, `apiVersion 1.4.312`, `driverName NVIDIA`).
The gate's own `--selftest` is green with the fresh seed:
`PASS — 25 selftest fixture(s) checked, ... renderer=n/a`.

## Closure (2026-11-09): premise stale — (a) is not a compiler gap, (b) no longer reproduces

Re-examined against the canonical language rule before touching the seed.

**(a) `provider.configured` without `self.` is INVALID Simple, not valid
Simple.** "Implicit self" means the `self` *parameter* is implicit; the field
receiver is never implicit. Sources of truth, all agreeing:

- `doc/07_guide/language/coding_style.md` — `this.x` -> `self.x (implicit
  self)`; "`self.x` works, but `self` parameter is implicit"; rule 3 "In
  methods, do not write `self` as a parameter."
- Pure-Simple HIR lowering,
  `src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl:326-346`:
  a non-static method gets exactly one injected symbol, `self`. Field names
  are never injected into the method scope, so a bare `provider` is an
  unresolved name in the self-hosted compiler too — the seed's
  `variable provider not found` / `GlobalLoad: unresolved identifier` IS parity.
- The already-landed contract for the assignment form:
  `scripts/check/check-implicit-self-field-assignment.shs` records "the chosen
  fix direction is a hard error, not implicit-self resolution" and pins it on
  both engines; `test/01_unit/compiler/hir/implicit_self_field_hir_probe_spec.spl`
  pins the self-hosted lowering hard-error.
- The source was fixed where the defect actually was: `dbd_provisioning.spl`
  now reads `self.provider.configured` in `pub fn ready()` (`:169-172`) and
  `boot_owner.provider.configured` in `admit_boot_owner` (`:139`); no bare
  `provider` remains (landed with 711c590347f).

Measured on the current seed (`bin/simple.exe`, release/1.0.0 at 27e65c24371):
the bare-read probe is rejected on BOTH engines with a diagnostic naming
`provider`; the explicit `self.provider.configured` probe runs and prints
`true` on both. The guard above grew READ probes (`interpreter/read`,
`jit/read`) so a future compiler that silently *accepts* a bare field read is
caught as a contract drift, the same way a silently-accepted bare write is.

**(b) `DbdTransactionOwnerV1.new()` on a `use`-imported class** does not
reproduce on the current seed: a two-module repro (class exported from module
A with `static fn new()`, called inside a `static fn create()` constructor in
module B that imports it) prints the field value under both
`SIMPLE_EXECUTION_MODE=interpreter` and `=jit` with no `jit-compile-error`
demotion. Pinned by
`test/01_unit/bugs/dbd_implicit_self_read_and_imported_static_call_spec.spl`
(+ `dbd_transaction_owner_shape_helper.spl`), which mirrors both dbd shapes
exactly (self-less `pub fn ready()` nested read; imported static call in a
static constructor): 2 examples, 0 failures.

Not re-run here: the full arm64 engine2d media phase (needs the aarch64
sysroot + QEMU lane on a Linux host). If that lane still fails on the dbd
bodies, it is a different defect and should be filed with its current output.

Status: **closed** (stale premise, evidence above). No seed change was made or
needed; changing the seed to resolve bare fields would have BROKEN parity with
the self-hosted compiler and the recorded contract.

## Triage 2026-11-10 (P3 compiler-seed lane, work/p3-seed-20261110)

Verdict: **SUPERSEDED (closed 2026-11-09 closure confirmed)**. Closure evidence
verified present in this worktree (base `origin/release/1.0.0`,
1504212d788b): `test/01_unit/bugs/dbd_implicit_self_read_and_imported_static_call_spec.spl`
and `test/01_unit/bugs/dbd_transaction_owner_shape_helper.spl` both exist; the
source fix (`self.provider.configured`, landed with 711c590347f) is the recorded
contract direction (hard error on bare field read, pinned on both engines by
`scripts/check/check-implicit-self-field-assignment.shs`). No seed change made
or needed; a bare-field-resolving seed would break parity with the self-hosted
compiler. The full arm64 media phase re-run remains a Linux/QEMU-lane item per
the closure note.
