# Writing Simple for freestanding/baremetal targets — known codegen landmines and safe patterns

Scope: `native-build --entry-closure --target x86_64-unknown-none` (and other
freestanding/`nogc_async_mut_noalloc` targets) — i.e. SimpleOS kernel and
driver code, not hosted builds. This consolidates a 3-day debugging campaign
(2026-07-16/18) chasing the first rendered desktop frame under QEMU so future
kernel work doesn't re-discover the same landmines. Each pattern below is a
**workaround to apply today**, not a promise the underlying compiler bug is
fixed — check the linked tracking doc for current status before assuming a
mitigation is still necessary.

Primary sources (read these for full disassembly evidence, not duplicated
here):
- `doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md` (C1-C8 catalog)
- `doc/08_tracking/bug/engine2d_cpu_offscreen_render_commands_first_frame_fault_2026-07-17.md`
- `doc/08_tracking/bug/interp_implicit_self_field_assignment_silent_noop_2026-07-17.md`
- `doc/08_tracking/bug/duplicate_type_name_collision_audit_2026-07-17.md`

## 1. `if val x = opt:` on Option-typed globals/fields can return nil on the hit path (C2)

**Failing shape:**
```simple
if val candidate = selected:
    candidate.sha256   # candidate can be nil HERE, on the branch that says it isn't
```

**Observed failure signature:** disassembly of the accessor showed the hit
path compiled to `xor rax,rax; ret` (returns nil) while the miss path
correctly returned the freshly created value. Downstream: nil-receiver
dereference, `cr2=0x0`. Seen on a module-global font mutex and inside
`FontRasterizer.load`.

**Safe pattern:** avoid the binding-if on Option-typed globals/fields under
entry-closure freestanding builds. Prefer an explicit nil-compare followed by
a direct (non-rebound) access:
```simple
if selected.?:
    selected.sha256    # read the original, not a rebound copy
```
or restructure so the value is produced and consumed in the same expression
without an intermediate binding-if. Re-verify with a disassembly spot-check
(`objdump -dr`) before trusting the hit path in a new freestanding call site.

## 2. Import-alias static constructors can bind to the wrong class (C8 original — fixed, but stay defensive)

**Failing shape:**
```simple
use { SharedFat32Driver as Fat32Core }
...
val x = Fat32Core.new(...)   # type annotations honored the alias, but
                              # the static-method CALL resolved to the
                              # real Fat32Core, constructing the WRONG class
```

**Observed failure signature:** the object gets stamped with the wrong
vtable/layout; dispatching it as the aliased type reads unrelated code bytes
as a pointer → wild jump, `cr2` = the wrong method's own prologue bytes.

**Status:** root-caused and fixed in `3f0acf071cf` (`lower_static_method_call`
now goes through `resolve_type_alias`, mirroring the type resolver).
Regression test added. Still worth caution: prefer importing the real name
directly in new freestanding kernel code, and run
`sh scripts/check/check-type-name-collisions.shs` (the DUP001 checker, added
by the same investigation) before adding a new top-level `struct`/`class`
whose name might collide with an existing `enum` — the seed's flat, global
class/enum registries make same-name shadows a *recurring* mechanism behind
multiple production bugs (vtable NAME-keying, `StmtKind.Expr`-vs-struct,
`TestDatabase`/`RunnerTestDb`, `SdnValue`), not a one-off.

## 3. Instance-method receiver binding can drop `self` under `--entry-closure` (94a893e77b9)

**Failing shape:**
```simple
val config = font_render_config_default_for_size(size)
config.identity()     # instance method call on a local value
```

**Observed failure signature:** disassembly showed
`call *rcx` (free function, returns config in RAX — correct) followed by
`movabs $identity_addr,%rdi; call *%rdi` for the method call — **the callee's
own address gets loaded into `self` (rdi); the receiver value in RAX is never
moved into the self register.** `self.family` then reads the method's own
prologue bytes (e.g. `sub rsp,0x3a0` = `48 81 ec a0 03 …`) as a string
pointer → `.trim()` → `decode_string` dereferences a code address → fault.
`cr2` looks like garbage that *changes with code layout* — that's the tell
(compare with pattern 6, same signature family). Confirmed on both
`.identity()`/`.valid()` and both call paths (render + metrics); free
functions with an explicit typed argument were unaffected in every check.

**Safe pattern:** for hot/boot-path config objects under entry-closure
freestanding builds, convert instance methods to typed free functions and
pass the receiver as an explicit argument:
```simple
fn font_render_config_identity(config: FontRenderConfig) -> ...
...
font_render_config_identity(config)   # no receiver dispatch at all
```
This is a workaround, not a fix — the seed's method-call lowering still needs
a real fix for the general case. Applying it to `FontRenderConfig.identity`/
`.valid()` (`src/lib/nogc_sync_mut/text_layout/font_types.spl`) cut a fault
storm from 81 recovered faults to 1 in the same boot.

## 4. Implicit-self field ASSIGNMENT silently no-ops in `me` methods — despite the lint's advice

**Failing shape:**
```simple
class C:
    flag: bool
    me set_it():
        flag = true        # silently no-ops — binds a new local, self.flag stays false
    me set_it_explicit():
        self.flag = true   # works
```

Field **reads** resolve implicitly and correctly; field **assignments**
without `self.` silently create a shadowing local instead of mutating the
field. The compiler's own lint recommends dropping `self.` — following that
advice on an assignment produces silent data loss.

**Safe pattern:** always write `self.field = value` explicitly inside `me`
methods, regardless of what the lint suggests, until this is fixed (tracked
open in `interp_implicit_self_field_assignment_silent_noop_2026-07-17.md`).
This is a general-purpose landmine, not freestanding-specific, but it is
especially dangerous in kernel/boot code where a silently-stale flag (mount
state, lock state, init-done state) fails much later and far from the
assignment site.

## 5. Silent phys=0 DMA acceptance (MOUNT-ERR)

**Failing shape:** requesting a DMA buffer from the raw allocation syscall
and using the returned physical address without checking it against 0.

**Observed failure signature:** under freestanding boot, `SYS_ALLOC_DMA`
could return `phys=0`; the NVMe block adapter accepted it uncritically, every
sector DMA read back zeros, and `Fat32Core.mount()` failed with a generic
`Err` — no fault, no crash, just a wrong/empty filesystem (`mount_failed
reason=no-nvme-or-bad-fs`) that looked like a disk/media problem, not an
allocator problem.

**Safe pattern:** always guard zero addresses from allocation syscalls before
using them for DMA — route through a wrapper that retries/fails closed on
`phys==0` rather than trusting the raw syscall result. Landed fix:
`NvmeDriver.alloc_dma` in `src/os/services/vfs/vfs_block_adapters.spl`
(commit `1e21f3a272b`). Apply the same zero-check discipline to any new
freestanding code that talks to a raw allocation/MMIO syscall — this class of
bug (successful-looking call, garbage data, no signal) is easy to misdiagnose
as something else entirely.

## 6. Fault-handler +2-RIP recovery cascades — how to read a fault storm

The freestanding fault-recovery ISR (`_rich_fault_entry`,
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`) does a
blind "RIP += 2, iretq" on *any* of the 256 IDT vectors, page faults and
`#UD` alike. One bad pointer or one deliberate `ud2` trap can therefore
cascade into 60-80+ "recovered" fault log entries, each one just resuming 2
bytes into whatever garbage follows the real fault site and free-running from
there.

**Rules for reading such a serial log:**
- **Fault COUNT is cascade noise, not a fix signal.** 81 vs 71 vs 66 faults
  across builds does not mean "worse" or "better" — chase the **first**
  fault only; everything after it is derailment.
- **`cr2` incrementing by a small constant (e.g. +2) per fault** is the
  signature of this exact recovery loop, not of a moving target — it's the
  same wild jump landing slightly further each time.
- **A `cr2` value that looks like a valid-ish canonical address but changes
  when you add/remove unrelated code** is very likely *code bytes read as a
  pointer* (a prologue like `push rbp; mov rbp,rsp; sub rsp,0x...` misread as
  a data pointer), not real corruption — cross-check by LE-decoding the low
  bytes of `cr2` against known instruction opcodes (`55 48 89 e5 48 81 ec ...`).
- **`cr2=0x0` (a genuine null)** is a different, simpler bug class (nil-field
  read after an indirect call that returned nil) — don't conflate it with the
  code-bytes-as-pointer signature above; they need different fixes.
- **Check for a `ud2` (opcode bytes `0x0F 0x0B`, i.e. little-endian u16
  `0x0B0F`) at/near the fault RIP before chasing a "corruption" theory.** A
  `ud2` is *intentional* — either the compiler's own duck-dispatch sentinel
  guard (`compile_method_call_virtual`, fires when MIR's `vtable_slot` hits
  `DUCK_DISPATCH_UNSUPPORTED_SLOT = u32::MAX`) or another deliberate trap.
  Before the `C8-CLOSE` fix, the fault-recovery handler treated this exactly
  like a page fault, so the "storm" was really one intentional trap plus 60+
  bytes of RIP+=2 garbage-execution noise; a fatal `spl_x86_on_kernel_ud2_fault`
  check now detects this case and prints `FATAL: kernel #UD (ud2) trap at
  rip=... vector=6 (#UD)` instead of silently recovering. If you see that
  message, the real bug is upstream (why did dispatch pick the sentinel
  slot?), not a memory-corruption chase.
- When grepping raw `.text` for a suspected instruction-prologue byte
  sequence to confirm/deny a hypothesis, use a **raw byte search on the
  extracted section** (`objcopy -O binary --only-section=.text`, then search
  the bytes directly), not a text-grep over `objdump -d`'s rendering —
  `objdump`'s linear decoder desyncs across inlined string-literal writes
  (`movb $imm,(%reg)` sequences for panic messages are common in this
  codebase) and will silently miss real occurrences.

## 7. Probe caveats

- **`unsafe_addr_of()` through an `any`-typed extern parameter lies.**
  Passing a concrete (non-trait) local through `extern fn f(ref: any)` and
  taking its address inside that call gets you the address of an ephemeral
  copy/box made when lowering the `any` argument, not the live object's
  address — confirmed directly: a raw read reported a null vtable pointer on
  an object that, in the same boot, dispatched correctly through a normal
  method call. This is not limited to trait-typed values; it affects any
  value crossing an `any`-typed boundary.
- **Use behavioral probes, not raw-pointer-chase probes.** Prefer
  `serial_println("marker={value.method()}")`-style dispatch-and-print over
  `unsafe_addr_of` + manual `mmio_read64` pointer chasing when isolating a
  freestanding codegen bug — every reliable finding in this campaign came
  from behavioral A/B probes at controlled call sites, not from raw memory
  inspection.
- **`print`, not `eprint`, in bootstrap/native-build worker processes.**
  Worker stderr is not captured by the harness; anything written with
  `eprint` during a native-build trace is silently lost. Use `print` for any
  temporary diagnostic you need to actually see.
- **A rebuild is required for every probe change** — there is no
  hot-instrumentation path for freestanding kernel builds; budget for it
  (isolated `--cache-dir` per lane keeps rebuilds from clobbering a
  concurrent lane's cache, and keeps a from-scratch build honest about what
  it actually compiled).
- **Debug/perf instrumentation is level-gated, not deleted.** General policy
  (see `doc/07_guide/infra/logging/` for the canonical statement): when
  cleaning up instrumentation, debug prints, or perf/timing logs, do not
  delete the insert — convert it to a level-gated log (debug level, or
  another appropriate level; perf/timing instrumentation becomes a
  perf-level log disabled by default) so it stays reusable for the next
  investigation. Deletion is reserved for overly-specific one-off logs with
  no reuse value (e.g. a hardcoded address dump for one dead hypothesis).
  Prefer one shared gate/flag or an existing log facility over ad-hoc
  per-file booleans, so future logs plug into the same mechanism — this
  codebase already has one for baremetal code,
  `src/os/baremetal/profile/log_policy.spl`'s `BaremetalLogPolicy`
  (compile/runtime level pair, `BAREMETAL_LOG_DEBUG`..`BAREMETAL_LOG_OFF`),
  prefer wiring into it over inventing a new mechanism when a target is
  already set up to construct and thread that policy through.
- **Concrete worked example for these `examples/09_embedded/...` entry
  files** (`gui_entry_desktop.spl`, `tls_unit_entry.spl`): they are not yet
  wired to `BaremetalLogPolicy`, and the minimal-footprint fallback used here
  is a per-file `fn _probe_debug() -> bool: false` (flip the literal to
  `true` to re-enable) with an early `if not _probe_debug(): return` guard
  at the top of each probe function, so every call site stays unchanged.
  Use a **function**, not a module-global `val`: module-global initializers
  are unreliable at runtime on this freestanding lane (module-init gap — see
  `taskbar_clock_region_rgb_sha256_pin()` in `gui_entry_desktop.spl` for the
  same workaround applied to a different global), which would make a bool
  `val`'s flip-to-`true` re-enable silently no-op even though it looks
  correct while `false`. Content of the probe must stay intact — gating only
  controls whether it fires. Never gate a probe whose output is asserted on
  by a QEMU evidence/gate script; check the relevant
  `scripts/check/check-simpleos-*-evidence.shs` scripts for the probe's
  marker string before gating it, and leave that probe ungated if a script
  depends on it.

## Other confirmed miscompiles from the same campaign (quick reference)

| ID | Shape | Signature | Mitigation |
|---|---|---|---|
| C1 | top-level `val`/`var X = call()` at module or entry-file scope | global stays nil/empty; all reads see the zero value | Fixed (`4d3f37e3e9e`, entry-file case fixed alongside) — module-global init now runs via `__simple_call_module_inits` before `spl_start` |
| C3 | `if not a and b.call():` short-circuit `and` | LHS test dropped from codegen; RHS call runs unconditionally | Nest the conditions: `if not a: \n  if b.call():` |
| C4 | anonymous tuple return, e.g. `-> (A, i32, i32, text)` | positional members read out of order at the call site (`.1` reads `.2`) | Replace the tuple with a named struct return |
| C5 | `enum_val == EnumType.Variant` | comparison false for a genuinely-matching value while a `match`-based helper in the same frame is correct | Use a `match`-based predicate helper instead of `==` |
| C6 | inlined byte-combine, `b0 \| (b1 << 8)` / `b0 + b1*256` | high byte silently dropped when inlined (heisenbug: adding prints "fixes" it) | Use a single opaque `mmio_read16/32(addr) as u32` load instead of combining separately-read bytes |
| C7 | bare `.to_u32()` on a `u16` via the freestanding alias bridge | dispatches to an unrelated struct's method (e.g. `Color.to_u32`) instead of the scalar conversion | Use `as u32` casts on scalars; avoid bare conversion-method calls in kernel code |

## Verification recipe

**Production kernel build flags** (the canonical recipe used throughout this
campaign, from `scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs`):
```
native-build --backend cranelift --cpu x86-64-v1 --opt-level=aggressive \
  --mode dynload --entry-closure --target x86_64-unknown-none \
  --linker-script examples/09_embedded/simple_os/arch/x86_64/linker.ld \
  --entry examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl
```

**Verification tiering (don't full-rebuild for a one-line lib edit).** See
`.claude/rules/bootstrap.md` § "Verification tiering" for the full T0–T3 policy.
For this kernel specifically:
- **Small pure-Simple lib change** → add `SIMPLE_NATIVE_INCREMENTAL=1` and a
  **stable** `--cache-dir <dir>` (do not wipe it between runs — a fresh dir is a
  cold build). Only the changed module(s) recompile; the build prints
  `[native-incremental] N reused / M rebuilt`. This reuses per-module objects
  only: the **link and entry-closure discovery still run every build**, so it is
  faster than a full rebuild, not instant. Reuse also requires the **same seed
  binary** — rebuilding the seed changes `compiler_fingerprint` and invalidates
  every cached object. The `SIMPLE_NATIVE_INCREMENTAL` key folds in a global
  build fingerprint (opt-level, entry-closure flag, target, linker-script, and
  the closure's cross-module struct/enum/signature layout), so any structural or
  cross-module change auto-falls-back to a full rebuild and prints the reason;
  a leaf edit can never ship a stale wrong kernel. Default OFF.
- **Structural change** (new module, struct/enum/trait layout, entry-closure set,
  linker/flag/target/opt-level) → full rebuild (T1 auto-triggers this too).
- **Compiler change** (`src/compiler_rust` or `src/compiler`) → full bootstrap.

Boot with `qemu-system-x86_64 -machine q35 -cpu max -m 2G` plus an
NVMe-backed FAT32 disk if the VFS/disk path is under test
(`-drive file=...,if=none,id=nvm,format=raw,snapshot=on -device
nvme,serial=deadbeef,drive=nvm` — required to actually reach the NVMe code
path; without it the boot silently short-circuits to
`no-nvme-or-bad-fs`/`mount_failed` and never exercises the driver at all).
Use `gui_entry_desktop.spl`, not `wm_entry.spl` — the latter boots through a
legacy non-pure-Simple FS/NVMe path and cannot reproduce most of these
landmines by construction; confirm with `nm` (look for `NvmeBlockAdapter`/
pure-Simple driver symbols) before trusting a repro against a given entry
file.

**Content-based leak-watch, not line-number-based.** Serial log line counts
and offsets shift between every rebuild (different code layout, different
cache state) — a diff-by-line-number or diff-by-total-line-count between two
boots is not a reliable signal. Instead grep for **stable content markers**:
- `[PANIC] heap exhausted` / `[heap] warn: crossed watermark` — heap-leak
  regression signal, independent of how many lines came before it.
- The **first** `[fault] rip=...` / `[fault] cr2=...` line only — ignore
  fault count (see pattern 6).
- Repeated allocation-size markers (`[heap] alloc sz=0x800020 ...`) — a
  fixed-size allocation repeating N times against expectation is a stronger
  leak signal than heap-offset deltas, since offsets are cache/layout
  dependent but the semantic allocation shape is not.
- A completion marker actually reached (`first-frame-rendered`, `[WM] Glass
  desktop rendered!`) vs. a screendump non-black percentage: treat
  percentage-non-black as unreliable evidence unless the completion marker
  printed — a pre-completion screendump can look "less black" purely because
  more (unfinished, partially-corrupt) compositing happened before the boot
  stalled, not because the frame is more correct.

## 8. Offscreen opacity-consume path & cross-module target-dims misread (2026-07-18)

- **Offscreen opacity-consume path affects COVERAGE, not just heap.** A leaky
  per-window offscreen scratch path (`Engine2D.create_offscreen()` not wiring
  a `software_backend`) doesn't just exhaust the heap — it can also truncate
  the blitted footprint to whatever partial region the leaky scratch buffer
  happened to cover. On the SimpleOS x86_64 glass desktop, wiring
  `software_backend: sw` into `Engine2D.create_offscreen()`'s constructor
  (`engine.spl:348`) activated the `draw_software_offscreen_opacity_consume`
  fast path and fixed BOTH problems in one change: non-black screendump
  coverage went 12.64% -> 99.83%, and the heap panic disappeared. When
  debugging a partial/truncated render, check the offscreen consume wiring
  before assuming the truncation and any co-occurring heap issue are separate
  bugs — they can be the same root cause.
- **Cross-module field-offset misread can hit target dims silently.** The
  gated `[route-dbg]` probe in `draw_ir_adv.spl`
  (`_engine2d_route_dbg`/`ENGINE2D_DRAW_IR_ROUTE_DBG`, around line 38) caught
  `_engine2d_draw_ir_render_batch_embedded`'s `target_width`/`target_height`
  (from `eng.width()`/`eng.height()`, i.e. `Engine2D.w`/`.h`) reading garbage
  cross-module (`tw=158239601 th=3840` instead of `3840`/`2160`) while the
  same batch's embedding dims and opacity read correctly — the same
  receiver-blind ambiguous-field-index class documented in
  `doc/08_tracking/bug/simpleos_native_build_framebufferdriver_crossmodule_field_offset_shift_2026-07-14.md`.
  Currently harmless (`baremetal_direct` routing overrides it for opaque
  full-page batches), but it defeats the `fills_target_exactly` fast path
  silently — see
  `doc/08_tracking/bug/engine2d_draw_ir_target_dims_crossmodule_field_offset_misread_2026-07-18.md`.
  Reuse the same gated route-dbg probe (flip the bool, rebuild, grep serial
  for `[route-dbg]`) as the go-to diagnostic any time a Draw IR routing
  decision looks wrong — comparing the always-correct embedding dims against
  the suspect target dims is what pinned this one.
