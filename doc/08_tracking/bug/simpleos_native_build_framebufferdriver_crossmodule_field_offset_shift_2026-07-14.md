# BUG: freestanding native-build shifts cross-module struct field offsets by one slot for classes with `[u32]` array fields (SimpleOS 4K WM render)

**Status:** source fix and regressions added; executable native/PPM verification pending
**Severity:** high (blocks the SimpleOS x86_64 4K WM desktop from rendering a real PPM; cr2=0x0 null-deref cascade)
**Component:** native-build freestanding codegen (`SIMPLE_BOOTSTRAP=1 native-build`, `--target x86_64-unknown-none --backend cranelift`) — cross-module class field-offset computation
**Family:** same class as [`x64_freestanding_module_level_val_u32_desktop_gui_2026-07-12.md`](x64_freestanding_module_level_val_u32_desktop_gui_2026-07-12.md) (freestanding native-build silently mis-reads a value across a module boundary).
**Found:** 2026-07-14, verifying the SimpleOS WM fullscreen evidence harness after the disk-less spawn fault and the baremetal-mutex halt were fixed.

## Current source resolution (2026-07-16)

The Rust seed now resolves an ambiguous field on an erased `ANY` receiver by
recovering the receiver's declared struct before the receiver-blind global
scan. The implementation is in
`src/compiler_rust/compiler/src/hir/lower/expr/access.rs` via
`try_resolve_receiver_struct_name_from_expr` and
`try_resolve_global_field_index_by_name`. This is the source-level fix for the
full-graph collision pinned below; it does not change the uniform one-word
backend layout.

Two non-duplicated regressions now describe the downstream contract:

- `test/01_unit/compiler/mir/nested_typed_field_index_collision_spec.spl`
  lowers a nested typed receiver through the pure-Simple HIR/MIR pipeline and
  requires `FramebufferDriver.width` to serialize as `GetField` index 2 even
  when a larger decoy declares `width` at index 0.
- `scripts/check/check-native-seed-parity.shs` registers the cross-module
  fixture under `test/fixtures/native_crossmodule_field_index/` once through
  `run_strict_dual_backend_case`, which covers default LLVM and explicit
  Cranelift without target-specific copies.

These additions have not been executed in this edit. The native parity result,
the real SimpleOS PPM result, and the three-stage bootstrap result remain
pending. The separate HEAD-seed NVMe-init regression documented below still
blocks reaching the render/PPM gate; this issue must not be marked verified or
closed until that gate runs on a working Linux native-build host.

## Symptom

When a `class` that has one or more `[u32]` (dynamic array) fields **before** its scalar fields is passed across a module boundary and the receiving module reads a scalar field, the read lands **one slot too early** — it returns the value of the *previous* field (or garbage from before the first read field).

Concretely, `FramebufferDriver` (`src/os/drivers/framebuffer/fb_driver.spl`, `class`, fields in order: `… back_buffer: [u32], host_buffer: [u32], … width: u32, height: u32 …`):

- Created in `gui_entry_desktop.spl` (via `FramebufferDriver.from_scanout_raw`) with `width=3840, height=2160`. The framebuffer's own module confirms this: `[desktop-gui] framebuffer ready width=3840 height=2160`.
- Read cross-module in `src/os/compositor/engine2d_wm_frame_executor.spl` (`framebuffer.width.to_i64()`): returns **34802657** (garbage), while `framebuffer.height.to_i64()` returns **3840** — i.e. `.height` yields the real *width*. Exact one-slot shift.

Serial evidence (before fix):
```
[desktop-gui] framebuffer ready width=3840 height=2160
[wm-frame] host-gpu-fallback reason=unavailable-or-readback-capacity width=34802657 height=3840
```

The garbage width later feeds an out-of-bounds / null framebuffer access in the render/present path → `cr2=0x0` fault. On x86_64 the rich-fault ISR recovers by advancing RIP+2, which turns the single real fault into a garbage cascade (it blunders into `Mutex.lock`/`Mutex.unlock` — "runtime error: field access on nil receiver" — and finally a `rt_file_read_bytes called on baremetal -- halting` TRAP). **These reported fault sites are RIP+2 recovery noise, not the real fault** (confirmed: `grep -rn "\.lock()"` finds zero call sites in any render-linked module, and the composition/present path never legitimately reads a file with 0 windows).

## Reproduction

```bash
scripts/check/check-simpleos-wm-fullscreen-evidence.shs
# serial.log: guest reaches [desktop-gui] degraded-no-disk apps=0, launcher apps=15,
# then host-gpu-fallback with garbage width, then cr2=0x0 fault cascade -> halt.
# status=fail reason=guest-render-fault; no baseline PPM captured.
```

Disassembly of the executor read site (objdump, decoded as x86-64) confirms `framebuffer.width` is loaded from an offset one `[u32]`-field-slot too low. Fault frames all report `cr2=0x0000000000000000`.

## Partial workaround applied (NOT the root fix)

Commit thread trusted scanout scalars into the executor so the shifted field reads are bypassed:

- `src/os/compositor/engine2d_wm_frame_executor.spl`: added `fb_w: i64` / `fb_h: i64` fields and default-`0` params on `create` / `create_host_gpu` / `_create_host_gpu_exact`; every dim read resolves `if fb_w > 0: fb_w else: framebuffer.width…`.
- `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`: pass `screen_width.to_i64(), screen_height.to_i64()` (the trusted scanout dims) into `create_host_gpu`.
- arm64/riscv64 callers pass no dims → default 0 → unchanged field-read fallback.

**Verified effect:** the executor now logs the correct `width=3840 height=2160`. The visible garbage is gone.

## Remaining blocker (same root, different struct)

After the executor dims are fixed, the desktop still faults `cr2=0x0` — bisected via serial markers to **`shared_wm_scene_draw_ir_composition`** (`src/lib/common/ui/window_scene_draw_ir.spl:710`, reached from `Engine2dWmFrameExecutor.render` → composition build). The composition builder reads the `SharedWmScene`/`TaskbarModel` structs cross-module (they are built in the shell/runtime modules). Corroborating evidence of the same shift on `TaskbarModel`: `runtime_taskbar_revision()` returns **514532965** (garbage) while `scene_revision` reads a plausible **17**.

Bisect trail (serial markers, since removed):
```
[DIAG] rbf frames ok rev=17 trev=514532965 cf=0     # taskbar_revision garbage
[DIAG] exr filtered scene.w=3840 scene.h=2160        # scene dims OK here
[DIAG] exr filtered_scene ok
<fault>                                              # inside shared_wm_scene_draw_ir_composition_with_content
```
`content_frames.len()==0`, so the fault is inside the base `shared_wm_scene_draw_ir_composition` (desktop/chrome/taskbar batch builders that read `scene`/`taskbar` fields). `serial_println` is not available in the pure `common/ui` module, so finer bisection needs disassembly of the real (non-recovery) fault rip.

## Root cause (hypothesis)

native-build computes class field offsets **inconsistently across module boundaries** for classes whose layout contains `[u32]` (dynamic array / fat-pointer) fields ahead of scalar fields. The defining module and the reading module disagree on the byte offset of the scalar fields by exactly one array-field slot. This is systemic — it affects at least `FramebufferDriver`, `TaskbarModel`, and likely any WM struct read cross-module in the render path. Per-callsite scalar threading is a workaround, not a fix; the render path reads deep struct graphs and cannot all be scalar-threaded.

## Suggested fix

Fix the native-build (cranelift freestanding) cross-module class field-offset computation so a struct's field layout is identical in every module that references it (single source of truth for `[u32]`/array-field-bearing class layouts). Until then, the SimpleOS 4K WM desktop cannot render a real PPM.

## Scope note

The disk-less spawn/load fault (app_registry `Option<struct>` unwrap + `g_vfs` null-driver via `g_root_fat32` nil-compare) and the baremetal `rt_mutex_*` halt are already fixed on `main`; this field-offset shift is the remaining blocker for the WM paint.

---

## 2026-07-14 — Controlled compiler investigation (Claude Opus 4.8, 1M): "field-layout mis-sizing" mechanism DISPROVEN; trigger is full-graph-scale

A read-only compiler scoping pass plus a controlled disassembly experiment
**disproves** the "Root cause (hypothesis)" above at the isolated level, and
re-points the investigation. **The workaround stays; this only re-scopes the
compiler fix.**

### Backend facts (file:line)

- Native field access is a **uniform 1-word-per-field SLOT model**, not byte
  offsets. `translate_get_field`/`translate_set_field`/`translate_aggregate`
  in `src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl:92,
  :125, :39` (LLVM) and `src/compiler/70.backend/backend/native/isel_x86_64.spl:415-422`
  + `70.backend/codegen.spl:363` (cranelift) all compute address =
  `field_index * 8`. **A `[u32]`/slice field is exactly ONE 8-byte slot on both
  construction and read — there is no fat-pointer (ptr+len) 2-slot expansion
  anywhere in the native backend.** So a field can NOT be "mis-sized" by an
  array field; only the field *index* can differ.
- Field index is resolved in **declaration order** by `resolve_field_index`
  (`src/compiler/50.mir/_MirLowering/function_lowering.spl:582`): `field_map`
  (by global symbol id) → `struct_field_order` (by NAME) →
  `struct_value_syms`/`struct_field_type_name` name-recovery fallbacks. The
  native/bootstrap MIR path has **no expression type inference** (bugs
  #166/#138/#156, `50.mir/mir_lowering_types.spl:25-90`), so cross-module field
  reads lean on these fragile NAME-keyed heuristics.

### Controlled experiment — does NOT reproduce

Built a faithful minimal 2-module reproducer: a `class FbDev` with the EXACT
`FramebufferDriver` field list (`u64, [u32], [u32], u32, u32, u32, u32, bool,
4×u32`) + `static fn make`; a consumer reading it cross-module via both real
patterns — a direct typed param (`fb.width`, mirrors executor line 62) and a
nested `self.fb.width` where `fb` is a class field at index 1 after a class-typed
field (mirrors `self.framebuffer.width`, executor line 104). Compiled with the
CURRENT deployed compiler via `bin/simple compile … --emit=object`, carved the
SMF `.text`, and disassembled the field-read instructions.

**Every read resolves CORRECTLY** — `width`(idx 3)→offset `0x18`, `height`(idx
4)→offset `0x20` — across ALL axes tested:

| variant | width | height | correct? |
|---|---|---|---|
| normal, x86_64-linux | `0x18` | `0x20` | ✓ |
| `SIMPLE_BOOTSTRAP=1`, x86_64-linux | `0x18` | `0x20` | ✓ |
| `SIMPLE_BOOTSTRAP=1`, x86_64-**unknown-simpleos** | `0x18` | `0x20` | ✓ |
| **`SIMPLE_BOOTSTRAP=1`, `--target x86_64-unknown-none --backend cranelift`** (the exact target/backend this bug uses) | `0x18` | `0x20` | ✓ |
| nested `self.fb.width` (consumer field-of-field) | `0x18(%r10)` | `0x20(%r10)` | ✓ |

No shift in any minimal configuration — **including the exact freestanding
`x86_64-unknown-none` cranelift target/mode of the live failure.**

### Conclusion / corrected scope

- The "array fields ahead of scalars mis-size the layout" mechanism is **wrong**
  as stated: array fields are 1 uniform slot and the exact layout + read
  patterns resolve correctly in isolation, even on the freestanding target.
- The shift is **real in the full SimpleOS build** (peer evidence above, and
  `TaskbarModel` too) but **full-graph/scale dependent**. The most likely real
  mechanism is a collision in the NAME-keyed field-resolution heuristics
  (`struct_field_order` / `struct_value_syms` / `struct_field_type_name`, all
  keyed by type NAME) — the documented cross-module same-field-name /
  same-name-subset collision family (cf.
  `interp_cross_module_struct_field_collision_2026-07-04.md`). FramebufferDriver's
  and TaskbarModel's field names (`width`/`height`/`dirty`/`revision`/…) are
  extremely common across the OS graph; at whole-program scale one of these maps
  can recover the WRONG type ordering for the receiver at a read site, dropping
  one leading entry (exactly the -1 signature). This matches the sibling bug
  `x64_freestanding_module_level_val_u32_desktop_gui_2026-07-12.md`.
- **Verdict: a minimal, safely-landable compiler fix is NOT available from this
  pass.** The mechanism is not reproduced in isolation ⇒ the exact miscount site
  cannot be pinned ⇒ no blind change to `resolve_field_index` (the
  bootstrap/native hot path) is justified. The 3-stage-byte-identical-bootstrap
  gate makes a speculative change unacceptable.

### Precise next step to pin it (definitive, bounded)

The real consumer compiles standalone with full closure:
`SIMPLE_BOOTSTRAP=1 bin/simple compile src/os/compositor/engine2d_wm_frame_executor.spl --emit=object --target=x86_64-unknown-none --backend=cranelift -o real.o`
(a ~14 MB SMF; `.text` at the descriptor before the `.text` name string in the
SMF section table). Extract `_Engine2dWmFrameExecutor_dot__render_host_gpu` /
`…_create_host_gpu_exact` from the SMF symbol table (strtab ~`0xd9d9f0`),
disassemble ONLY those, and read the `FramebufferDriver.width` load offset — if
`0x10` (idx 2) instead of `0x18` (idx 3), the shift is confirmed in-build. Then
add a diagnostic to `resolve_field_index` (function_lowering.spl:582) guarded to
`FramebufferDriver`/`TaskbarModel`, rebuild the compiler once, and log which
name-keyed map returns the short/shifted ordering. This needs an SMF-symtab
parser or a compiler-side diagnostic build — a bounded but non-trivial follow-up,
NOT a blind hot-path edit.

### Root-fix direction (unchanged, but now scoped)

Make `resolve_field_index` authoritative via the **symbol-id-keyed `field_map`**
for a typed class receiver (never fall to the NAME-keyed heuristics for an
imported class whose def is in the compilation closure). The broader
"preserve class/struct field types through HIR (stop erasing to `Infer`)" rework
is the durable fix but is out of bounds for a minimal pass.

---

## 2026-07-14 (later) — instrument→pin→fix loop ATTEMPTED; blocked by local environment. Ready diagnostic handed off.

Followed the decisive instrument→pin→fix plan. Two independent pinning methods
were attempted; both are blocked ON THIS MAC (aarch64-apple-darwin), not by the
compiler logic.

### Extended disproof (added the exact live target/backend)

Re-ran the controlled disassembly repro on **`--target x86_64-unknown-none
--backend cranelift`** (the EXACT freestanding target+backend the live SimpleOS
build uses) under `SIMPLE_BOOTSTRAP=1`, with `framebuffer` as a class field at
index 1 (after a class-typed field, mirroring the real executor). Result:
`width`→`movl 0x18` (idx 3), `height`→`movl 0x20` (idx 4), nested and direct,
all correct. So the resolution is correct in isolation even on the precise
live target. The shift is confirmed **full-graph-scale only**.

### Pinning method 1 (instrument + rebuild): BLOCKED — bootstrap native-build is pre-existing-broken on this Mac

A behavior-preserving `[FIDX]` diagnostic was added to `resolve_field_index`
(logs which name-keyed table resolves the index, the recovered receiver type,
and the index — see patch below). To make it take effect the compiler must be
rebuilt. `bin/simple build bootstrap` **fails at Stage 1** with
`error: native-build failed without diagnostics` / `native-build worker exited
with code 1`. Re-ran on a CLEAN tree (diagnostic reverted): **identical Stage 1
failure**. So the bootstrap native-build is broken in THIS environment
independent of any edit (same root as the host `--native` link failures:
`ld.lld: error: unable to find library -lSystem`, `_main_shim.o: unknown file
type`). The compiler cannot be rebuilt here, so the diagnostic cannot be
captured on the real build here.

### Pinning method 2 (disassemble the real object): BLOCKED — SMF symtab not hand-parseable

The real consumer compiles standalone with full closure
(`bin/simple compile src/os/compositor/engine2d_wm_frame_executor.spl
--emit=object --target=x86_64-unknown-none` → ~14 MB SMF). But `--emit=object`
wraps output in Simple's **SMF** format (not ELF), the symbol-table record
format is defined in a runtime extern (`rt_smf_write`, not readable Simple
source), and the `.text` is ~12 MB — so the specific `_Engine2dWmFrameExecutor_*`
function cannot be reliably located/attributed by hand to read its
`FramebufferDriver.width` load offset. (`objdump`/`llvm-objdump` on this Mac
cannot read SMF and lack `-b binary`; no `objcopy`/`gobjdump`/radare available.)

### Consequence

Both the "pin the collision" step AND the PPM verification gate
(`check-simpleos-wm-fullscreen-evidence.shs`, which needs a working native-build
+ QEMU) require an environment where SimpleOS native-build actually links. **This
Mac is not that environment.** The next pass must run on a Linux/working-
native-build host (the same host the peer used to observe the live fault).

### READY-TO-USE diagnostic (drop-in, pins it in ONE executor compile on a working host)

Insert into `src/compiler/50.mir/_MirLowering/function_lowering.spl` inside
`resolve_field_index` (right after the docstring, before `val type_sym =
self.expr_type_symbol(base)`), add the `fidx_watch` guard, and add the four
`print "[FIDX] …"` lines at each `return`/default branch:

```
val fidx_watch = field_name == "width" or field_name == "height" or field_name == "revision" or field_name == "pinned" or field_name == "running" or field_name == "tray" or field_name == "scene_revision" or field_name == "front_addr" or field_name == "back_buffer" or field_name == "host_buffer" or field_name == "windows" or field_name == "background"
# ... at the field_map hit:
if fidx_watch: print "[FIDX] field={field_name} via=field_map sym={sym_id} idx={idx} list={fields.join(\",\")}"
# ... at the struct_field_order-by-name hit:
if fidx_watch: print "[FIDX] field={field_name} via=struct_field_order.byname recv={type_symbol.name} idx={named_idx} list={named_fields.join(\",\")}"
# ... at the struct_value_syms hit:
if fidx_watch: print "[FIDX] field={field_name} via=struct_value_syms recv={nm} idx={vidx} list={vfields.join(\",\")}"
# ... at the default:
if fidx_watch: print "[FIDX] field={field_name} via=DEFAULT idx=0 (receiver type unrecovered)"
```

Then on a working-native-build host: rebuild the compiler once, and
`bin/simple compile src/os/compositor/engine2d_wm_frame_executor.spl --emit=object
--target=x86_64-unknown-none 2>&1 | grep '\[FIDX\] field=width'`. The line tells
you, in one shot: the resolved `idx` (0x18/idx3 = correct, anything less =
shifted), which name-keyed table produced it (`via=`), and the recovered
receiver class (`recv=`) + the field `list=`. If `recv=` is NOT
`FramebufferDriver`, it is a wrong-receiver-recovery (then the low-risk fix is to
make `resolve_field_index` reach `field_map[sym_id]` for the typed receiver, or
rename the confused field); if `recv=FramebufferDriver` but the `list=` is short
by one, the field-list registration dropped an entry (investigate
`struct_field_order`/`field_map` population for that class in the full closure).
Repeat the grep for `field=revision`/`field=pinned` (TaskbarModel path).

### Verdict

- **Layout-arithmetic / fat-pointer hypothesis: DISPROVEN** (uniform 1-slot
  backend; correct in isolation on the exact live target).
- **Exact collision: NOT yet pinned** — both pinning methods are blocked by the
  local Mac's broken native-build, not by lack of a plan. The drop-in diagnostic
  above turns pinning into a single compile on a Linux host.
- **No compiler change is landable from this environment** (cannot satisfy the
  byte-identical-bootstrap gate or the PPM gate here). Handing off to a
  working-native-build host with the diagnostic + procedure above.

---

## 2026-07-14 — Linux-host team follow-up (handoff accepted; ROOT PINNED, patch ready, but 2 MORE blockers found downstream)

On a Linux host with a working native build (recipe: session scratchpad
`screendump_repro.md` — build the kernel with the NATIVE x86 rust seed
`bin/release/x86_64-unknown-linux-gnu/simple`, NOT the emulated aarch64 self-hosted
binary the gates pick; ~87 s vs never), a team pinned the root and tested fixes.

**ROOT PINNED (rust seed, not `.spl`).** The `.spl` `resolve_field_index` NEVER runs
in this path — MIR consumes a pre-resolved HIR `field_index` (`hir/lower/expr/…
lowering_expr.rs:216`). The misresolution is in the RUST seed's HIR lowering:
`src/compiler_rust/compiler/src/hir/lower/type_resolver.rs:155` registers imported
struct fields as `TypeId::ANY`; for an ANY receiver the field INDEX is resolved by a
receiver-BLIND "struct with the MOST fields declaring this name wins" scan
(`type_resolver.rs:548-564`/`:599-625`; `expr/access.rs:337-346` keeps the wrong
index, only degrading the TYPE to ANY). 57 structs declare `background`, 801 `width`
at differing indices → wrong struct → one-slot shift. Isolated repro = ~1 struct/name
⇒ correct; full desktop closure ⇒ wrong. Fully explains "full-graph-only". The
`is_ambiguous_global_field` guard is defeated (computed only over `imports.struct_defs`,
and it sits AFTER the scan).

**PATCH READY (uncommitted; captured at `scratchpad/screendump_handoff/compiler_field_fix.patch`).**
In `access.rs` before `get_field_info`: when the receiver erased to ANY AND the field is
globally ambiguous, recover the receiver's real struct
(`try_resolve_receiver_struct_name_from_expr` → `try_resolve_global_field_index_by_name`)
and use THAT index. Bootstrap-SAFE: seed rebuild 3m29s, `widget_text_edit_spec` 7/7,
no regression (the ambiguous-set is empty outside `--entry-closure`).

**BUT the patch is UNVERIFIED for the PPM, because 2 more downstream blockers surfaced:**
1. **HEAD rust-seed NVMe-init regression (separate, newer).** A seed built from CURRENT
   `src/compiler_rust` HEAD produces a SMALLER kernel (652 units / 17 MB vs the deployed
   Jul-11 seed's 670 units / 41 MB) that dies in `NvmeDriver.init_from_grant` BEFORE the
   render stage — a *pristine* HEAD seed faults identically, so it is pre-existing, not the
   field patch. Coincides with the Jul-13 `fix(native-build):` closure-discovery churn
   (nested-import following / bare-export / production-check imports) that shrank the kernel.
   This blocks verifying ANY render fix with a HEAD seed. (The field patch also does not
   fire on the HEAD seed — `_wm_draw_ir_desktop_batch` disassembles byte-identically to
   pristine — so HEAD already resolves that call differently.)
2. **Baremetal Engine2D executor renders 0 commands.** Using the deployed Jul-11 seed (which
   DOES boot to the render stage) plus a source-level nil-guard workaround for the field
   shift (`scratchpad/screendump_handoff/render_nilguard.patch`), the desktop gets PAST the
   nil-receiver panic and reaches `first-frame-rendered` — but the frame is still black:
   `[wm-frame] engine2d-draw-ir-rejected … rendered=0 skipped=5 … unsupported Draw IR
   commands skipped: 3`. The baremetal preflight (`draw_ir_adv.spl:385-398`) supports only
   `RECT`/`TEXT`/`IMAGE`; the composition also emits `GROUP`/`EDGE`/`PATH`, and even the
   supported background `RECT` renders 0. Plus a scanout mismatch (QMP captures 3840×768 vs
   the desktop's detected 3840×2160).

**Correction (render-lane bisect, same day): the "rendered=0" IS the same field-shift, not a
separate render bug.** After guarding all 5 `scene.background` derefs + bypassing the internally-
faulting `resolve_font_metrics_with_language`, the composition BUILDS FULLY
(`desktop-ok → taskbar-ok → composition-built`) and reaches `first-frame-rendered`. The paint
step then returns `rendered=0` because the Engine2D CPU rasterizer reads
`FramebufferDriver.width()/height()` cross-module at creation (`src/lib/gc_async_mut/gpu/
engine2d/backend_baremetal.spl:59-60`) and gets the SAME one-slot-shifted garbage dims; the
present-time target-fill/geometry checks (`draw_ir_adv.spl:329,574` via `eng.width()/height()`)
then reject every command. `DrawIrCommand` geometry is pre-array and reads fine — GROUP/EDGE/PATH
being "unsupported" is a red herring; the real cause is the garbage framebuffer dims. So the whole
render chain reduces to ONE root cause — the cross-module field-index shift — which the ready
`compiler_field_fix.patch` fixes wholesale (the executor's existing `fb_w/fb_h` trusted-dims
workaround covered only host-gpu present dims, not Engine2D creation / CPU framebuffer addressing).
Full render-lane bisect notes: `scratchpad/render_findings.md`.

**Net (revised).** Real non-black desktop PPM is gated on essentially TWO things: **(1) the
field-index fix** [patch ready, bootstrap-safe — fixes composition AND Engine2D-creation dims in
one shot], and **(2) the separate HEAD-seed NVMe-init regression** that must be resolved to even
build a HEAD-seed kernel that boots to the render stage and thereby verify (1). Scanout-resolution
match is likely downstream of (1). Both worked source patches (compiler fix + render nil-guards)
are captured under `scratchpad/screendump_handoff/`.
