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

## 2026-09-01 — the 772 unresolved types were NOT a symptom of the MIR defects

The two MIR fixes above are real, but they are **not** what blocked the daemon.
They live in `70.backend/_MirToLlvm` (pipeline step 5/6); the daemon build dies
in **step 1/6 -> 2/6**, which never reaches them. The build log taken *after*
both fixes landed (started ~01:46, both fixes committed 00:17 and 00:34) ends at
the identical `errors=770->772`. Reclassify them: correct fixes, wrong blocker.

### Actual root cause: the closure import scanner desynced byte and char cursors

`text.len()` and `text[a:b]` are **BYTE**-indexed; `text.char_code_at(i)` is
**CHAR**-indexed. Measured directly:

```
s = "ab—cd\nef"   # 8 chars, 10 bytes
s.len()            -> 10          (bytes)
s.char_code_at(2)  -> 8212        (chars — the em-dash)
s[0:5]             -> "ab—"       (bytes)
```

`_driver_line_end` (`src/compiler/80.driver/driver_source_loading.spl`) scanned
for `\n` with `char_code_at`, returning a CHAR offset, and both of its callers
sliced that offset as BYTES. The two cursors therefore diverged at the FIRST
multi-byte character in a file, and every line after it was mis-sliced, so no
`use` line was recognised.

`src/lib/gc_async_mut/gpu/engine2d/engine.spl` has an em-dash on **line 2**.
Probing `_driver_cached_entry_source_scan` on it directly:

| file | imports found | expected |
|---|---|---|
| `engine.spl` (as tracked) | **1** | 39 |
| same file, non-ASCII folded to ASCII | 39 | 39 |
| `platform_all.spl` (pure ASCII, control) | 9 | 9 |

Losing 38 of engine.spl's 39 imports dropped 28 modules from the native-build
source closure. `module_surface_registry_index` then resolved those imports to
`target_index = -1`, the callable-dependency sweep in
`module_reexport_materialization.spl:766` found no route, and each missing type
resurfaced as `unresolved type: X` attributed to whichever module imported the
CALLABLE — `daemon_runner.spl` and `platform_all.spl`, neither of which names
those types. That is the whole of the "772 unresolved types incl.
`Option`/`Mutex`/`Result`", and it explains why disabling entry-closure pruning
changed nothing: the modules were never *collected*, so there was nothing to
prune.

### Fix and evidence

`_driver_line_end` now returns a `(byte_offset, char_offset)` pair and both
callers advance both cursors in lockstep.

| measurement | before | after |
|---|---|---|
| `engine.spl` imports scanned | 1 | **39** |
| ASCII-folded control | 39 | 39 (unchanged) |
| daemon `source_closure` | 96/96 | **230/230** |
| daemon `load_sources` | 111/111 | **313/313** |

Regression spec:
`test/01_unit/compiler/bootstrap/entry_closure_non_ascii_import_scan_spec.spl`
(5 steps, all pass). The pre-existing unicode case in
`entry_closure_physical_source_dedup_spec.spl:166` did **not** catch this — it
places a single `use` immediately after the non-ASCII text, where the small
cursor drift still lands inside the keyword. The defect only shows with several
imports after the multi-byte character.

Scope note: this is not engine2d-specific. Any `.spl` file whose imports follow
a non-ASCII character — an em-dash in a header comment is enough — has been
silently contributing a truncated import list to every `--entry-closure`
native build.

### Still blocked: the x86_64 gate needs a deployed pure-Simple compiler

`check-simpleos-qemu-host-gpu-2d.shs` reports
`simpleos_qemu_host_gpu_2d_reason=pure-simple-compiler-missing`. `find_simple`
admits the Rust seed only through `bootstrap_diagnostic_binary_is_valid`, which
is restricted to `GUEST_ISA_REQUEST=aarch64` and a `build/*diag*` build dir, and
explicitly rejects any binary whose smoke output says `Rust-built` /
`bootstrap seed only`. No `bin/release/x86_64-unknown-linux-gnu/simple` is
deployed here. That admission was NOT weakened. The gate remains blocked on a
bootstrap deploy, independently of the closure fix.

### Dual check and regression baseline (measured, not asserted)

Both runs use the same seed binary; the pre-fix side is an isolated worktree
detached at `36de9a8580c` (the commit before the fix), so neither run disturbs
the other.

| spec | pre-fix (36de9a8580c) | post-fix |
|---|---|---|
| `entry_closure_non_ascii_import_scan_spec.spl` (new) | 1 passed, **4 failed** | **5 passed, 0 failed** |
| `entry_closure_physical_source_dedup_spec.spl` (existing) | 4 passed, 11 failed | 4 passed, 11 failed |

The single pre-fix pass in the new spec is the deliberate pure-ASCII control,
which is exactly the step that must NOT move — so the spec discriminates the
defect rather than the file.

The 11 failures in the existing dedup spec are **pre-existing and unrelated**:
the failing-test name sets are byte-identical on both sides (`diff` reports no
difference), and they are seed-interpreter semantic errors (`variable 'Thing'
not found`, `variable 'run_command' not found`) plus text assertions about
unrelated files (hash-map utilities, expression type inference). This fix
introduces no new failure and repairs none of them.

### The gate is NOT blocked on the compiler — it has a provided-daemon path

Correction to the note above: `check-simpleos-qemu-host-gpu-2d.shs:2861` takes
the `pure-simple-compiler-missing` branch only when `simple_bin` is empty AND
(`SIMPLEOS_GPU_HOST_BIN` is unset OR `SIMPLEOS_HOST_GPU_USE_EXISTING_GUESTS`
is not 1). Line 2878 (`daemon=${SIMPLEOS_GPU_HOST_BIN:-$default_daemon}`) is a
designed knob: supplying a pre-built daemon plus
`SIMPLEOS_HOST_GPU_USE_EXISTING_GUESTS=1` reaches the QEMU/ivshmem/screendump
phase without a deployed pure-Simple compiler and without weakening the
compiler-admission checks, which were left exactly as they are.

## 2026-09-01 — the x86_64 GUEST probe kernel is a second, independent blocker

The provided-daemon path (`SIMPLEOS_GPU_HOST_BIN` +
`SIMPLEOS_HOST_GPU_USE_EXISTING_GUESTS=1`) does not skip the guest: `build_guest`
still requires `kernel_for_isa x86_64` =
**`build/os/simpleos_x86_64_host_gpu_probe.elf`**, or it returns
`guest-artifact-missing`. That is NOT the kernel this lane already has —
`build/os/simpleos_x86_64_desktop_engine2d.elf` is a different artifact and does
not satisfy `kernel_for_isa`.

Building the probe kernel with `build_guest`'s own x86_64 flags surfaced two
**source** defects in
`examples/09_embedded/simple_os/arch/common/host_gpu_ivshmem_probe_entry.spl`
(both now fixed):

- `host_gpu_ivshmem_probe_main_profile` passed `isa` to `_host_gpu_probe_fail`,
  but `isa` is a local of `_host_gpu_probe_main_at` — undefined in that scope.
- `_host_gpu_probe_main_at` used `CudaHostOffloadAdapter` and
  `VulkanHostOffloadAdapter` with no `use` for either. A repo-wide grep finds
  **no other importer of either class**, so this code had never been compiled.

These were reported as `[CODEGEN BODY] ... GlobalLoad: unresolved identifier`,
which reads like a codegen defect but is not: the compiler was right, and it
correctly refused to emit stubs (`SIMPLE_ALLOW_STUB_FALLBACK` was never set).

With those fixed the kernel clears codegen and reaches the **link** stage, where
it stops on deeper, still-open x86_64 bring-up gaps:

1. `examples/09_embedded/simple_os/arch/x86_64/boot/tls13_aes256_gcm_helper.c`
   fails `clang` with 4 errors — calls to undeclared `x86_aes_repack_bytes`,
   `x86_tls13_aes256_gcm_decrypt_tagged` and
   `x86_ssh_aes256_gcm_decrypt_packet_tagged`. Same defect class as the
   `runtime_native.c` incident: C that has never compiled sitting in-tree.
   (clang even suggests `rt_ssh_aes256_gcm_decrypt_packet`, declared right
   above the call.)
2. `ld.lld: undefined symbol: up2_elf64_module_load` (from
   `_boot_multiboot2_elf64_loader.o`) and `rt_byte_array_new` (from several
   `src/lib/common` modules), against
   `Freestanding unresolved symbol check: 41 unexpected symbol(s)`.

So the x86_64 pixel-evidence row is blocked by **two independent chains**: the
host daemon (closure defect, fixed above) and this guest kernel. Only the first
was in the previous diagnosis.

### Status at hand-off (2026-09-01)

The gate that owns `build/simpleos_wm_vulkan/` is
`scripts/check/check-simpleos-x86-64-wm-host-vulkan-pixel-evidence.shs` (not
`check-simpleos-qemu-host-gpu-2d.shs`). It takes a PRE-BUILT daemon at
`build/simpleos_wm_vulkan/simpleos_gpu_host` and uses
`KERNEL_ELF=build/os/simpleos_x86_64_desktop_engine2d.elf`, which exists. Its
`--selftest` is green here: `PASS — 17 selftest fixture(s) checked, classifier
and pixel bar behave (no boot attempted), renderer=n/a`. So the daemon is
genuinely the only missing input, exactly as originally scoped — the guest
probe kernel discussed above belongs to the OTHER gate and is not on this path.

The daemon native-build is running detached with the closure fix in place:
`source_closure 230/230`, `load_sources 313/313`. It is slow precisely because
the closure is now complete — 230 modules instead of the truncated 96 — and
`surface_build` costs 20-60 s for the heavy engine2d modules.

**What is measured vs. what is still pending — do not conflate these.**
Measured: the scanner returns 39 imports for `engine.spl` instead of 1; the
closure is 230/230 instead of 96/96; the new spec is 4/5 RED before the fix and
5/5 green after; the existing dedup spec's 11 failures are identical on both
sides. **Pending: the HIR outcome.** No post-fix run has yet REACHED the HIR
phase — the current build is still in step 1/6 — so a `hir-fatal` count of 0
right now is vacuous, not evidence that the 772 are gone. That the closure fix
removes them is the hypothesis this build is testing, and it is well supported
(every one of the 772 traced to a module the closure had dropped), but it is
not yet a measurement. Also pending: the daemon link, the `nm` census, and the
gate verdict.

A chained runner is armed so the remaining steps complete without supervision:
when the build exits it writes the undefined-`rt_*` census, the WEAK-definition
scan (type column `$(NF-1)`), the gate-required Vulkan provider symbol table,
and then the full gate verdict to
**`build/simpleos_wm_vulkan/post-build-report.txt`**.

Resume by reading that file. Build log:
`build/simpleos_wm_vulkan/daemon-build2.log`. Neither
`SIMPLE_ALLOW_STUB_FALLBACK` nor `SIMPLE_ALLOW_UNRESOLVED_RUNTIME` was ever set,
and the gate's classifier and blank-frame must-FAIL were not touched.

## 2026-09-01 — MEASURED: the closure fix cuts 772 HIR errors to 59, in 4 files

The post-fix build reached HIR and completed the phase (`hir 230/230`). Result:

| | before the closure fix | after |
|---|---|---|
| modules in closure | 96 | **230** |
| sources loaded | 111 | **313** |
| HIR errors | **772** | **59** |
| files carrying them | many (misattributed) | **4** |

`BUILD_RC=1` — the daemon still does not link. But the remaining 59 are a
different, tractable population, and this is the first time they have been
visible: the 772 phantom errors were masking them.

```
 31 unresolved name: draw_ir_rect_bounds      27 src/std/nogc_sync_mut/io/vulkan_sffi.spl
 24 unresolved type: Option                   21 src/std/gc_async_mut/gpu/engine2d/draw_ir_adv.spl
  6 unresolved name: alias                    13 src/std/gc_async_mut/gpu/engine2d/backend_session.spl
  5 unresolved type: Result                    3 src/std/nogc_async_mut/env/platform.spl
  5 unresolved name: draw_ir_no_rect
  4 unresolved name: DRAW_IR_BACKEND_GPU
 3x5 rt_vulkan_{push_constants,dispatch,bind_pipeline,bind_descriptors,bind_buffer}
 2x5 rt_vulkan_{is_available,compile_spirv_array,compile_spirv,begin_compute,alloc_buffer}
  2 rt_env_cwd   2 ComputeError   2 BackendSessionPolicy   2 BackendSessionHandle
  1 IntelBackend  1 DrawIrRect
```

Diagnosis so far, same "never compiled" class as the guest probe entry:

- **`draw_ir_adv.spl`** uses `DRAW_IR_BACKEND_GPU` (line 1334),
  `draw_ir_rect_bounds` (1572) and `draw_ir_no_rect` (2593) but imports none of
  them (its `use std.common.ui.draw_ir.{...}` block, lines 8-27, lists neither).
  `DRAW_IR_BACKEND_GPU` is `pub val` and IS in `draw_ir.spl`'s `export` line
  743, so it only needs importing; `draw_ir_rect_bounds` (161) and
  `draw_ir_no_rect` (164) are plain `fn`, not `pub`, and are NOT exported, so
  they also have to be published before they can be imported.
- **`backend_session.spl`** names `BackendSessionPolicy`,
  `BackendSessionHandle` and `ComputeError`, and **none of the three is defined
  anywhere in `src/lib`**. Line 8 carries them inside a COMMENTED-OUT import,
  and the file itself defines `GcComputeError`, not `ComputeError`. This is
  renamed/dead API, not a missing `use` — it needs a real decision, not an
  import line.
- **`vulkan_sffi.spl`** imports the `rt_vulkan_*` names (line 21) rather than
  declaring them `extern`; the import target does not provide them.
- **`platform.spl`**'s `rt_env_cwd` is the pre-existing
  `[use-warning] 'rt_env_cwd' is named in use std.io_runtime.{...} but module
  .../src/std/io_runtime.spl does not provide it`.

Note the error attribution is again unreliable: all three `draw_ir_adv` names
are reported at `draw_ir_adv.spl:65:29`, which is a `val _E2D_TEXT_PROBE`
declaration, not any of the use sites.

**The rebuild loop is now short.** The build ended with
`[hir-cache] hits=226 misses=4 stores=0` — only the 4 offending modules are
recompiled, so a fix-and-retry no longer costs the ~2 h a cold run does.

Note `src/std` is a **symlink to `lib`** in this worktree, so `src/std/...` and
`src/lib/...` are the same inode; one edit covers both spellings.

### Per-file diagnosis of the remaining 59 (next lane starts here)

**1. `backend_session.spl` (13) — `alias X = Y` is not a real declaration form.**
Lines 200-202 are:
```
alias ComputeError = GcComputeError
alias BackendSessionPolicy = GcBackendSessionPolicy
alias BackendSessionHandle = GcBackendSessionHandle
```
and line 204 exports the alias names. `alias` is a lexer keyword
(`TokenKind::Alias`) but the parser only ever turns it into a keyword-IDENTIFIER
(`parser/src/expressions/primary/identifiers.rs:58`,
`parse_keyword_identifier("alias")`). So these three lines parse as a bare name
`alias` followed by an assignment — which is exactly the reported
`unresolved name: alias` x6, plus `ComputeError` / `BackendSessionPolicy` /
`BackendSessionHandle` x2 each. The supported spelling is `type X = Y`, used in
**48** stdlib files; `^alias ` at top level appears in **exactly this one file**
repo-wide. Fix: `alias` -> `type` on the three lines.
Per the CLAUDE.md grammar rule this is recorded rather than silently
normalised: either `alias` becomes a real type-alias declaration in the parser,
or the keyword should be rejected at top level instead of degrading into an
identifier and failing 200 lines later with an unrelated message.

**2. `draw_ir_adv.spl` (21) — three names used, none imported.** `DRAW_IR_BACKEND_GPU`
is `pub val` and IS exported (`draw_ir.spl:743`), so it only needs adding to the
`use std.common.ui.draw_ir.{...}` block. `draw_ir_rect_bounds` (161) and
`draw_ir_no_rect` (164) are plain `fn`, not `pub`, and not exported — they must
be published first.

**3. `nogc_sync_mut/io/vulkan_sffi.spl` (27) — NOT yet diagnosed.** It imports 37
`rt_vulkan_*` names from `std.gpu.engine2d.sffi_vulkan`; 25 resolve and 12 do
not. Two hypotheses were tested and **both are disproved**: it is not an export
list (`sffi_vulkan.spl` has no `export` line at all, yet 25 names resolve
through it), and it is not a duplicate declaration (each failing name is
declared exactly once tree-wide, in `sffi_vulkan.spl`). Failing and working
declarations are interleaved by line number (44 works, 46 fails; 64 fails, 66
works; 108/116 fail, 136 works) and are identical in form, so it is not a
declaration-shape issue either. This one needs fresh investigation; start with
`SIMPLE_AMBIGDBG=1`, which makes the callable sweep print `sweep-candidate` and
`sweep-verdict` lines per dependency.

**4. `nogc_async_mut/env/platform.spl` (3)** — `rt_env_cwd`, imported via
`std.env.types` from `std.io_runtime`. `io_runtime.spl:70` declares
`extern fn rt_env_cwd() -> text?` while `sffi/env.spl:10` declares
`extern fn rt_env_cwd() -> text` — different return types. This is the
long-standing `[use-warning]` and may share a root cause with (3).

Fix all four in ONE pass before rebuilding: parse is cached (~6 min) but
`surface_build` is not (~90-120 min), so each rebuild costs about two hours
regardless of how few files changed. Expect `hir-cache` misses above 4 next
time — publishing names in `draw_ir.spl` invalidates its dependents.
