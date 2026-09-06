# SimpleOS WM Vulkan smoke rows: blockers per arch (2026-08-31)

Goal item: "SimpleOS window manager with Vulkan-backed smoke tests on x86_64,
aarch64 and riscv64" — three rows. This record states, per arch, exactly what
blocks a **non-vacuous** pixel-evidence gate, so no later lane re-derives it.

## Architecture (do not misquote)

There is **no in-guest Vulkan in SimpleOS** and there never was. What exists is
a guest -> host **offload**: the guest WM encodes draw IR, publishes it through
an ivshmem BAR, and the host daemon (`src/app/simpleos_gpu_host/`) executes it
on a real host GPU. "Vulkan-backed" therefore means *the host daemon rendered
it and the guest holds a verified receipt*. The dual receipt is
`HOST_GPU_DAEMON_DRAWIR` (`daemon_runner.spl:413`, printed only when
`device_backed` holds) matched against the guest serial receipt on the nonce
`(frame, submit_id, fence_id)`.

Host capability was measured on this box, not assumed: TITAN RTX + RTX A6000,
Vulkan **1.4.312**; `ivshmem-plain` present in both `qemu-system-x86_64` and
`qemu-system-aarch64`; OVMF, AAVMF and `QEMU_EFI.fd` all installed;
`vendor/limine/BOOTAA64.EFI` present. **None of these is the blocker for any
row.** Any claim of "no GPU on this host" is false.

## x86_64 — blocked on build cost, not on a defect

The closure is complete: PR #188 restored
`std.common.contracts.os.server_data_namespace_v1` and added the previously
missing producer
`scripts/os/build-simpleos-x86-64-desktop-engine2d-kernel.shs`; PR #186 fixed
the gate's unsatisfiable classifier. The gate's own selftest is green here:

    PASS — 17 selftest fixture(s) checked, classifier and pixel bar behave
    (no boot attempted), renderer=n/a

The `vulkan,cuda,runtime-symbol-table` runtime archive builds clean
(`RUNTIME_RC=0`, 101 MB). The remaining cost is the host daemon
`native-build`, which on this shared box (load 10-15) advanced 4 of 96
surfaces in 8.5 minutes — hours, not minutes. The prior lane's failure
(`daemon-build4.log`, "native-build worker exited with code 1") was **not**
reproduced: with the correct invocation — the one
`check-simpleos-qemu-host-gpu-2d.shs` uses, `--runtime-bundle core-c-bootstrap`
plus `SIMPLE_LINK_OBJECTS=<vulkan/cuda archive>` — the build proceeds normally.

Nothing here needs a code fix. It needs a machine and a long enough timeout.

## aarch64 — HARD blocker: no compiler on this host can build the kernel

Two real source defects were found and **fixed** (see commits below); the row
is still blocked behind a third thing that is not fixable in source.

`examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl` was a
casualty of clobber `4edef8fab8e` — 525 lines against 589 pre-clobber:

1. **Did not parse at all.** Lines 433-438 duplicated the
   `WmAction.FocusWindow` arm at +4 indent and every later arm inherited the
   wrong indentation. Fixed surgically (not by restore: the two blobs diverged
   in *both* directions, 196 lines only in pre against 132 only in current).
2. **Dangling references from a half-finished rewrite.** The file replaced the
   `Arm64ProductionWmProducer` publication path with direct surface
   materialization but left `published_snapshot` (used, never declared) and
   `animation_surface_id` (never declared) behind. All 16 blobs in git history
   carrying the rewrite marker, and the copies in three other worktrees, have
   no `published_snapshot` declaration — the text was never written, so it is
   not recoverable. Repaired minimally: the three dead vars at 315-317 are
   deleted (declared, never read), `animation_surface_id` -> `editor_id`.

3. **The remaining blocker.** With both fixed, the Rust seed still fails:

       hir: Unsupported feature: cannot infer field type while lowering
       gui_entry_desktop_start: struct 'ANY' field 'delivered_key_sequence'

   The source is correct — `Arm64VirtioInputBackend.create(i64, i64) ->
   Arm64VirtioInputBackend` is declared at
   `src/os/compositor/arm64_virtio_input_backend.spl:108` and
   `delivered_key_sequence: i64` is a real field at `:78`.

   Two candidate workarounds were tried and **both failed**, which is what
   makes this a compiler limitation rather than a source problem:

   - An explicit type annotation on the binding
     (`var input_backend: Arm64VirtioInputBackend = ...`). The compiler's
     guess merely changed from `RocmFfi` to `ANY`; it still failed.
   - Restoring the pre-clobber call form
     `create_with_poller(w, h, arm64_virtio_input_poll, false)` — the
     hypothesis being that `create` collides with the `static fn create` on
     other structs (e.g. `HostedInputBackend`) while `create_with_poller` is
     unique, so the pre-clobber form would resolve. It **fails identically**,
     with the same `struct 'ANY' field 'delivered_key_sequence'`. The
     name-collision hypothesis is therefore **disproven**: inference fails on
     this struct regardless of which constructor is called.

   Both experiments were reverted rather than left in as workarounds that do
   not work. (Note in passing: the file still imports `arm64_virtio_input_poll`
   at line 17 and never uses it — more evidence the rewrite is unfinished — but
   wiring it changes nothing here.)

   This is consistent with, and is the concrete mechanism behind,
   `check-simpleos-arm64-unified-live.shs:70` refusing a `Rust-built` compiler
   outright (`fail compiler-is-bootstrap-seed`). That lane needs the
   pure-Simple compiler.

   **And no pure-Simple compiler is deployed on this host.**
   `bin/release/x86_64-unknown-linux-gnu/simple` resolves to a binary that
   itself prints "this Rust-built Simple binary is a bootstrap seed only", and
   there is no `.provenance.env` beside it. So the aarch64 row cannot be built
   by any compiler currently on this machine.

   Unblocking needs a bootstrap deploy of a pure-Simple full CLI, or a seed HIR
   fix for this inference case. Not a gate-authoring problem.

Note separately: even once it builds, `check-simpleos-arm64-unified-live.shs`
boots with QEMU `-kernel`, which `.claude/rules/board-runnable.md` forbids. The
kernel-side half of the EFI migration is already done
(`check-simpleos-arm64-unified-boot-contract.shs`); the lane edit is not.

## riscv64 — NOT feasible; needs new code, not a gate

Three independent layers are missing. A gate written today would be vacuous,
so none was written.

1. `examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl:118`
   calls `create_host_gpu(...)` with `SIMPLEOS_HOST_GPU_BACKEND_METAL` and
   `backend_required=false`. It degrades silently to CPU and can never emit a
   `backend=vulkan` DrawIR receipt. No `SIMPLEOS_HOST_GPU_BACKEND_VULKAN`
   reference exists anywhere under `arch/riscv64/`.
2. **No producer builds a riscv64 desktop/WM kernel ELF at all.**
   `scripts/os/build-simpleos-riscv64-components-kernel.shs` builds components,
   not the GUI entry. The only thing that touches a riscv64 desktop entry is
   the PowerShell `check-simpleos-qemu-rv64-desktop-evidence.ps1`, and it
   builds `desktop_service_entry.spl` — a different, non-WM entry.
3. No riscv64 QEMU lane passes `ivshmem`. Every lane that does
   (`arm64-unified-live`, `x86-64-wm-host-vulkan-pixel-evidence`,
   `qemu-host-gpu-2d`, `qemu-guest-gpu-passthrough`, `io-audio-qemu`) is
   x86_64 or arm64.

The bridge itself is **not** the obstacle: `src/os/lib/gpu_bridge/
host_gpu_ivshmem.spl` has no arch conditionals — ISA is a wire field (`:185`,
`:197`) — and `arch/common/host_gpu_ivshmem_probe_entry.spl` is arch-generic
with backend/required as parameters (`:162-165`).

Order of work: (a) switch the riscv64 entry to VULKAN/required, mirroring
arm64's parameterized `gui_entry_desktop_start`; (b) add a
`scripts/os/build-simpleos-riscv64-desktop-engine2d*.shs` producer; (c) add
ivshmem + QMP to a riscv64 OpenSBI `-bios fw_payload` lane. Only then is a gate
worth writing.

Related: `doc/08_tracking/bug/board_vulkan_cross_arch_boundary_only_x86_64_proven_2026-08-11.md`
already records that `check-simpleos-riscv64-opensbi-real-firmware-boot.shs`
boots OpenSBI with **no guest payload** and proves nothing Vulkan-relevant.

## Status

| arch | row | blocker |
|---|---|---|
| x86_64 | not yet proven | daemon `native-build` wall time on a loaded box; no defect found |
| aarch64 | not done | seed HIR inference failure + no pure-Simple compiler deployed on this host |
| riscv64 | not done | METAL-hardcoded entry, no producer, no ivshmem lane — new feature work |

No vacuous gate was authored for any row.

## x86_64 update (measured after the first daemon build attempts)

The earlier "no defect found — needs wall time" line above is **superseded**.
The daemon build fails for real reasons, reproduced twice with the prior lane's
exact signature. Two defects, in order:

### 1. `unknown extern function: rt_heap_ref_wellformed` — FIXED

Recovering the dropped middle of the worker's truncated stderr gave exactly one
cause. The symbol is defined in `src/runtime/runtime_native.c:7975`,
`src/runtime/simple_core/core_enum.spl:103`, `runtime/src/value/objects.rs:363`
and `common/src/runtime_symbols.rs:658`, but `interpreter_extern/mod.rs` is a
THIRD, independent registry that lacked it. Registered it there; the repo's own
`check-interpreter-extern-registry-gap.shs` went from `1 new` to `0 new`. The
build then advanced from failing in *semantic* to reaching *HIR 95/96*.

### 2. 772 `unresolved type` HIR errors — OPEN, and the row's real blocker

Phase 3 then failed behind
`phase 3 FAILED (diagnostics unreadable: error array did not survive transport)`
— a deliberate degradation in `driver_orchestration.spl:257-259`, where
`self.errors` at offset `0xb8` faults because an aggregate-returning method
receives a zeroed `self`, so the driver declines to read diagnostics rather than
SEGV. Registering `rt_heap_ref_wellformed` is what makes that guard *work*: it
converted a silent corruption into a detected one.

`SIMPLE_BOOTSTRAP_DEBUG=1` (`driver_orchestration.spl:220`) unlocks the real
list. There are **772** errors, all of one kind:

    [bootstrap-phase3-errors] count=772
    HIR lowering error in src/app/simpleos_gpu_host/daemon_runner.spl:
        unresolved type: BackendCapability
    ... FramePacingCounters, Engine2DFontOwner, ComputeDispatchResult,
        BaremetalBackend, VirtioGpuBackend, BackendProbeResult

**The file attribution is wrong and must not be chased.** `daemon_runner.spl`
and `platform_all.spl` reference every one of those type names **zero** times
textually. The types are defined under `src/lib/gc_async_mut/gpu/engine2d/`
(`backend_capability.spl`, `wm_frame_pacing.spl`, `font_owner.spl`,
`compute_dispatch.spl`, `backend_baremetal.spl`, `backend_virtio_gpu.spl`,
`backend_probe.spl`) and are referenced by
`src/lib/gc_async_mut/gpu/engine2d/engine.spl`, which IS in the closure and DOES
import them (`engine.spl:35,36,57,58,60`). Their defining modules are NOT in the
closure — only 3 of the `gc_async_mut/gpu/engine2d/*` modules appear in it.

So the defect is in **entry-closure pruning**, not in the import paths: the
closure walker does not follow `engine.spl`'s `use std.gpu.engine2d.<mod>`
imports. Note `src/lib/gpu/` does not exist — `std.gpu.*` is served by the
`surface_alias` step (111 aliases), and **91 files** repo-wide import in that
style, so the style is an established convention rather than breakage.

### Disproved lead: PR #198 (`-> ()` compiles to a trap)

Worth recording because the hypothesis was reasonable and is now closed.
PR #198 fixes `Type::Tuple(vec![])` resolving to a non-`VOID` TypeId, so
`-> ()` emitted `ud2` with no `ret`. The hypothesis was that the same
return-type misclassification drove the sret/receiver ABI and explained the
zeroed `self` above. **Measured, not assumed:** `type_resolver.rs` from
`0f8ff6aa96e` applied cleanly, the seed rebuilt clean, and the daemon build was
rerun from a deliberately cleared cache. The failure is **byte-identical** —
same 772 unresolved-type errors. #198 does not touch this path. Its own
evidence was a freestanding-guest SIGILL; this is a host-side unresolved-type
failure with no trap. Two bugs that rhyme, not one.

### Status

x86_64 kernel: **built** (`KERNEL_RC=0`), 8.1 MB x86-64 ELF, statically linked.
`nm`: `rt_undefined=0 rt_weak=29 rt_text_defined=407` — the unverified
"53 undefined rt_*" figure measures **0**. Absent `rt_vulkan_provider_*` in the
guest is correct: there is no in-guest Vulkan.

x86_64 daemon: **not built**. No `simpleos_gpu_host` binary exists anywhere on
this host, so the gate cannot run and the row is honestly RED at its
`host GPU daemon missing` precondition. No vacuous pass was manufactured.

## x86_64 daemon — corrections to the section above (measured)

Two claims in the previous section were wrong. Both are corrected here rather
than edited away, because each cost a build cycle and the next lane should not
repeat them.

### CORRECTION 1: it is NOT entry-closure pruning

The previous section concluded "the defect is in entry-closure pruning ... the
closure walker does not follow engine.spl's `use std.gpu.engine2d.<mod>`
imports". **Disproved.** Rebuilt the daemon with `--entry-closure` removed
entirely (`daemon-noclosure.log`, cold cache): **identical 772 errors**, same
types, same counts. Pruning is not the cause.

### CORRECTION 2: `std.gpu.engine2d.*` resolves fine

An earlier probe appeared to show `std.gpu.engine2d.backend_probe` was
unresolvable under every `SIMPLE_LIB` value. That was a **repro artifact**: the
fixture lived in `/tmp`, so `project_root` was not the repo, and `std.*` is
deliberately anchored to project stdlib roots only
(`module_resolver/resolution.rs:670`). Re-run from inside the tree it resolves
cleanly and prints `ok`. The alias machinery is correct:
`resolve_stdlib_from_root` (`resolution.rs:397`) tries `<root>/<segments>` then
each of `STDLIB_FAMILY_DIRS` — which includes `gc_async_mut` — so
`src/lib/gc_async_mut/gpu/engine2d/<mod>.spl` is found. `src/lib/gpu/` not
existing is not a defect.

Anyone re-probing module resolution must place the fixture **inside the repo**.

### What the failure actually looks like

Counting the full unresolved-type census in both daemon logs:

    82 FramePacingCounters      55 Mutex        44 BackendProbeResult
    82 ComputeDispatchResult    48 Option       42 VirtioGpuBackend
    82 BaremetalBackend         26 ByteSpan     42 Engine
    18 DynLib                   14 Result       42 BackendCapability

`Option`, `Result` and `Mutex` are **core stdlib types**. Their failing to
resolve means this is not an engine2d-specific import problem at all — the
daemon build's stdlib type environment is not being established. Any fix aimed
only at `gpu/engine2d` would be aimed at a symptom.

### A 4-line native-build repro (adjacent defect, NOT the same one)

    use std.gpu.engine2d.backend_probe.{BackendProbeResult}
    fn main():
        print "ok"

`run` prints `ok`. `native-build` fails phase 3 with:

    HIR lowering error in src/lib/gc_async_mut/gpu/engine2d/helpers_availability.spl:
        unresolved name: renderer_priority_order

**Stated honestly: this is NOT the daemon's failure.**
`renderer_priority_order` appears **zero** times in both daemon logs. It is a
second, much smaller defect in the same neighbourhood, and it is valuable only
because it reproduces a phase-3 failure from 4 lines instead of 96 modules.
Note `renderer_select.spl` is byte-identical pre- and post-clobber, and bare
`fn` (813 occurrences vs 46 `pub fn` under `gpu/engine2d/`) is the normal,
importable convention — so this is not a clobber casualty and not a visibility
error. `renderer_select.spl` is a documented **variant seam** with mirrors under
`variants/ui/renderer/<value>/std/gpu/engine2d/`, which is the first place to
look.

### Row verdict

x86_64 WM row: **RED, not done.** The kernel half is complete and verified; the
host daemon does not build, so the gate stops at its `host GPU daemon missing`
precondition and no pixel evidence exists. No gate was run to a green verdict,
no classifier or fixture was weakened, and no vacuous row was produced.

### Scoping the daemon failure: hosted native-build itself is FINE

The obvious next question is whether every hosted `native-build` on this seed
fails phase 3, or only the daemon's import chain. Measured, using the **exact
daemon invocation shape** — same env (`SIMPLE_LINK_OBJECTS`, `SIMPLE_LIB`,
`SIMPLE_NO_STUB_FALLBACK=1`), same `--runtime-bundle core-c-bootstrap`, same
`--runtime-path`, same `--source src/app --source src/lib --entry-closure`:

    fn main():
        print "ok"

    HELLO_RC=0  ->  build/hellorepro/h.bin, 8.5 MB, runs and prints `ok`
    unresolved-type errors: 0

So the seed's hosted native-build pipeline, the core-c-bootstrap runtime bundle
and the vulkan/cuda archive link are all working. The failure is **specific to
the daemon's import closure**, not general. That narrows the next lane's search
to what `src/app/simpleos_gpu_host/main.spl` pulls in — and, given `Option`,
`Result` and `Mutex` are among the unresolved types, most likely to a module in
that closure whose failure cascades into the shared type environment, rather
than to the engine2d types the error messages name.

## x86_64 daemon — ROOT CAUSE FOUND (2026-09-01), two MIR-lowering defects

Everything above about the daemon's *import closure* is retired. The failure
was never closure-specific and never about type resolution.

### Retire the "772 unresolved type" framing

Measured on a seed freshly built from `origin/main` (`ea48917812b`, which
carries #197 and #198): a 4-line fixture importing
`std.gpu.engine2d.backend_capability` **reaches HIR cleanly** —
`[hir-cache] hits=0 misses=2 stores=2`, `unresolved type` count **0** — and
fails two phases later, at `native_compile` (step 5/6). The 772 figure was
measured on the older seed and does not reproduce. Do not chase it.

The record's "hosted native-build itself is FINE" contrast was also
misleading, for a mundane reason: the hello world used as the control
contains no `if`. That is exactly what it needed to contain.

### Defect 1 — `_sffi_tuple_get` is declared non-nil but must return nil

`fn _sffi_tuple_get(tuple: i64, index: i64) -> Any`
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:48`, and a second
copy at `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:112`)
reads HIR enum payload tuple slots. `HirExprKind.If`'s slot 2 is the OPTIONAL
else block; the decoder binds it to `HirBlock?` (`:3313`) and explicitly
tolerates nil. But the helper's non-optional `-> Any` return contract rejects
that nil first:

    error: semantic: nil is forbidden by the non-optional return contract of '_sffi_tuple_get'

**Minimal repro — 5 lines, one file, no imports:**

    fn main():
        var x = 0
        if 3 > 0:
            x = 1
        print "{x}"

`native-build` rc=1 pre-fix, rc=0 post-fix. Any `if` without an `else`, in any
module, anywhere, failed. Fixed by declaring the helper `-> Any?` at both
sites. The same helper serves the IfChain, Cast and NamedVar optional slots.

### Defect 2 — nil `finally_stack` on every `return` inside `if/else`

With defect 1 fixed, the ladder moved to a second, independent abort:

    error: semantic: method `len` not found on type `nil` (receiver value: nil)

`MirLowering.finally_stack` (`src/compiler/50.mir/mir_lowering_types.spl:56`)
is declared but **never initialized on any construction path**, so a function
with no try/finally region still holds nil there. A `return` inside a nested
block calls `emit_pending_finally_for_transfer()`
(`expr_dispatch.spl:1815`), whose `self.finally_stack.len()` then aborts the
whole build. An absent stack is exactly an empty stack; guarded accordingly.

**Minimal repro — 7 lines:**

    fn f(op: i64) -> bool:
        if op > 0:
            return true
        else:
            return false
    fn main():
        print "{f(3)}"

### How the exact frame was found (reuse this, do not re-derive)

The error carries no span and the misattributed `HIR lowering error in <file>`
banner is worthless here. The repo already has the right probe:

    SIMPLE_INTERP_OOB_DEBUG=1 SIMPLE_DEBUG_FIELD_ACCESS=1 <native-build ...>

prints `[mnf-debug-spl]` — the interpreted **.spl** frame list — which ended
exactly at `... -> lower_return_expr -> emit_pending_finally_for_transfer`.
One 60-second run replaced an open-ended source hunt. Note the full worker
stderr is truncated in the MIDDLE; the untruncated copy is written to
`/mnt/data/tmp/native-build-stderr-<pid>.log` and the log names the path.

Also note `SIMPLE_HIR_UNRESOLVED_TYPE_TRACE=1` (`types.spl:988`) prints
`span_file` for a genuine unresolved type — the fix for the wrong-file
attribution complained about above already exists.

### Measured ladder, all with the same daemon invocation shape

| fixture | pre-fix | post-fix |
|---|---|---|
| hello world (no `if`) | rc=0 | rc=0 |
| bare `if`, single file | rc=1 `_sffi_tuple_get` | **rc=0** |
| `if` in imported free fn | rc=1 `_sffi_tuple_get` | **rc=0** |
| `if`/`elif` | rc=0 | rc=0 |
| `if`/`else`, no return | rc=0 | rc=0 |
| `return` in both `if`/`else` arms | rc=1 `len` on nil | **rc=0** |
| verbatim copy of `backend_capability.spl` | rc=1 | **rc=0** |
| `use std.gpu.engine2d.backend_capability` | rc=1 | **rc=0** |

Both defects are in the pure-Simple compiler, not the Rust seed, and neither
is engine2d-specific — they blocked essentially every non-trivial
`native-build` on this lane.
