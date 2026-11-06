# Simple XRay — compiler structural change design

**Date:** 2026-11-06
**Status:** OWNER-APPROVED design (decisions recorded in § G). Nothing here is implemented or qualified yet.
**Base:** `origin/release/1.0.0` @ `671d5545201`
**Parent plan:** `doc/03_plan/compiler/aspect_dynload/simple_xray_staged_implementation_plan_2026-11-03.md` (cited as "plan §N")
**Status doc:** `doc/03_plan/compiler/aspect_dynload/xray_v1_integration_status_2026-11-03.md`
**Draft reviewed:** `origin/work/xray-v1-interface-20261103` (tip `7919ed563e0`, merge-base `46bc084a37f`, 1992 commits behind release)

Owner direction (2026-11-06): (1) land compiler-affecting structure first, details after;
(2) share arch first; (3) OFF both statically (no sleds/code/metadata/runtime) and
dynamically (sleds present, disabled = NOP-class path, toggle without restart);
(4) stage order: Linux LLVM-XRay adapter → Linux pure-Simple (AArch64 first, then
x86-64) → Windows pure-Simple (x64, ARM64).

> Order note: plan §2/§7 lists Linux x86-64 first. Owner direction puts **AArch64
> first in stage 2**. This document follows the owner; stage 1 (LLVM) admits both
> Linux triples already accepted by the draft's `trace_build_route_v1`.

---

## A. Compiler structural changes

### A.1 Ownership split (unchanged from plan / skill)

| Concern | Owner layer | Decides |
|---|---|---|
| Whether sleds exist (static switch) | `00.common` `CompileOptions.xray` + `80.driver` resolution | `--xray` on/off, never-list |
| Semantic intent per function | `50.mir` (`MirFunction` flag) | entry/exit/tail-exit wanted |
| Physical sled positions + bytes + map | `70.backend` (per backend, post-regalloc) | where the sleds really are |
| Which sleds fire (dynamic switch) | runtime (`src/lib/common/trace`, `src/lib/nogc_sync_mut/trace`) + SOSIX leaves, driven by aspect params | when sleds are on |

MIR `Ret` terminators are **intent, not sites**: the pure-Simple backends synthesize
the real epilogue/return late (`70.backend/backend/native/isel_x86_64.spl:279`
dedicated return block, `isel_aarch64.spl:969`), and `native/regalloc.spl:418`
rebuilds the prologue block after allocation. The draft's
`mir_observer_site_intent_v1.spl` header already concedes this ("the late emitter
must bind each surviving physical copy"). Therefore:

**Decision A1: no new `MirInstKind` for sleds. Use a function-level flag.**
A MIR instruction would have to survive `60.mir_opt`, inlining, block merging and
be re-derived anyway after regalloc; the existing coverage probes
(`50.mir/mir_instruction_kinds.spl:109`, "backends must reject these variants")
show the cost of an instruction every backend must learn. A flag is ignored by
default by every backend that does not read it.

### A.2 No new source syntax

There is **no `@xray` attribute** and no `decl_attrs.spl` change. Function
selection is expressed only through aspect params (`AspectParamsV1.ext`,
`simple.trace/observer-v1` pointcuts), which act at runtime (A.4).

### A.3 MIR representation (`50.mir/mir_instruction_graph.spl:236` `MirFunction`)

Add one defaulted field next to `is_naked`/`is_inline` (`:290-296`):

```
xray_mode: i64 = 0   # 0 = no sleds (default; static off), 1 = entry+exit sleds, 2 = +tail-exit
```

- Default `0` keeps every existing `MirFunction(...)` constructor valid.
- **Trap:** `MirFunction.with_blocks` (`:310`, comment "update field list when
  MirFunction gains fields — spread operator fails cross-module") must copy the
  field, else every MIR rewrite silently drops it. PR1 test asserts survival
  through `with_blocks` and through each `60.mir_opt` pass that rebuilds functions.
- MIR serialization does not carry function attributes today, so off-path MIR
  dumps are unchanged by construction; the native capsule function identity
  appends `|xray=N` only when non-zero.

### A.4 Instrumentation policy (who decides)

Two switches, never conflated:

- **Static switch — `--xray` compile option (+ SDN key).** Off by default ⇒ zero
  sleds, byte-identical output (B guard). On ⇒ sleds are emitted.
- **Dynamic switch — aspect params.** At runtime, `simple.trace/observer-v1`
  pointcuts in `AspectParamsV1` select which existing sleds are patched on/off.
  Aspect params never decide whether sleds exist.

New file `src/compiler/80.driver/driver_xray_policy.spl` (one resolution point),
run once per compile **after** `60.mir_opt`, at the instrumentation stage
(`apply_debug_trace` in `driver_pipeline_aop.spl`, reached by every pipeline):

```
struct XrayBuildPolicy:        # resolved value, in 80.driver/driver_xray_policy.spl
    enabled: bool = false      # static switch; false = no sleds anywhere
    include_tail_exit: bool = true
fn xray_policy_apply(module: MirModule, policy: XrayBuildPolicy) -> MirModule
```

Per function, first match wins:
1. `policy.enabled == false` → return module **untouched** (no traversal, no allocation).
2. Never-list (compiler-owned, not user-overridable): `is_naked`, `is_kernel`,
   `is_generic_template`, interrupt handlers (`70.backend/interrupt.spl`),
   functions in `src/lib/common/trace/**`, `src/lib/nogc_sync_mut/trace/**`
   (the xray handler itself), and the allocator/runtime-hook set → `xray_mode = 0`.
   Interrupt handlers are caught only when `@naked` or placed in a custom
   section: a non-naked `@interrupt` fn carries no MIR flag yet. Bare-metal and
   SimpleOS targets are rejected by `compile --xray` until that flag exists.
3. `is_inline`/`alwaysinline` → no sleds (physical-function rule, plan §5.4).
4. Every other function → sleds (`xray_mode = 1`, or `2` with tail-exit).

There is **no instruction threshold** (no field, no `--xray-threshold`). A
threshold can be re-added later only if measured code-size overhead requires it
(# ponytail: ceiling/upgrade path).

Nothing is resolved per function entry (plan §14): runtime `prepare(config,
selection)` turns the aspect-param selection into the enabled sled subset.

### A.5 Backend emission

**LLVM (stage 1)** — `70.backend/backend/_MirToLlvm/core_codegen.spl:1029-1060`
(the `attrs` string where `alwaysinline`/`naked noinline` are appended):
append `"function-instrument"="xray-always"` when `xray_mode≥1`, plus
`"xray-skip-exit"`/no tail flags per policy; `"function-instrument"="xray-never"`
for never-list members **only when `--xray` is on**. LLVM emits its own `xray_instr_map` / `xray_fn_idx` sections. Link:
add `libclang_rt.xray-<arch>.a` (+ `-lpthread -ldl -lrt`) in
`llvm_native_link_hosted_support.spl` / `llvm_native_link_orchestrator.spl`, Linux
triples only, only when `--xray` is on with the LLVM backend. SimpleOS `src/os/port/llvm/compiler_rt_cmake.cmake`
stays XRay-OFF (plan §4).

**Pure-Simple native (stage 2)** — `70.backend/backend/native/`:
- New `native/xray_sled_emit.spl`: runs **after** `regalloc.spl` and before
  `layout_solver.spl`/`elf_writer.spl`; inserts the entry sled as the first bytes
  of the function (before the prologue patched at `regalloc.spl:418`) and an exit
  sled before every `RET` produced at `isel_x86_64.spl:279`/`:1389`,
  `isel_aarch64.spl:969`; tail-exit sled before a tail `B`/`JMP`.
- AArch64 (first): plan §10.3 32-byte sled; off word `B #+32`, on word `NOP`;
  ID materialized via `MOVZ/MOVK w0`; x16/x17/x0/x30 preserved; never x18.
- x86-64: plan §10.2 13-byte sled (`EB 0B` ↔ `66 90`, `CALL rel32`, `EB 04`, imm32 ID);
  SysV profile is separate from the Windows one (plan §10.4).
- Map: new section `.simple_xray_map` (read-only, `SHF_ALLOC`, `SHF_LINK_ORDER`
  to `.text` for GC) added beside `.text/.data/.rodata/.bss` in
  `native/elf_writer.spl:372-409`. Each module also gets one hidden
  `__simple_xray_map_v1_<buildid>` root symbol and an init-array entry that calls
  `simple_xray_register_module(&map)` — emitted **only when `--xray` is on with the native backend**.
- Map format v1 (little-endian, fixed-width; plan §11): header {magic `SXRM`,
  u16 format=1, u16 isa, u16 abi_profile, u16 sled_abi_version, u32 fn_count,
  u32 site_count, u8[16] build_id (XXH3-128 of object), u64 text_base_reloc};
  function rows {u32 local_fn_id, u32 first_site, u32 site_count, u32 name_off};
  site rows {u64 addr_reloc, u32 local_fn_id, u8 kind (entry/exit/tail), u8 len,
  u8 align, u8 reserved, u32 off_word, u32 on_word}; then a string table of
  canonical semantic identities. Module instance identity is assigned at
  registration (plan §5.4), never the path.

**Cranelift** — `cranelift_codegen_adapter.spl` lowers through seed-owned
`rt_cranelift_*` externs (`src/compiler_rust/compiler/src/native_build_sffi.rs`).
It cannot emit sleds without Rust seed changes. Decided: `--xray` with
`backend=cranelift` → clear `UnsupportedTarget` error at policy resolution, in
all stages. No Rust seed changes.

**Interpreter / JIT / VHDL / GPU** — `--xray` rejected (`UnsupportedTarget`); off
untouched.

### A.6 Driver and config plumbing

- `00.common/driver_compile_options.spl` (next to `coverage_enabled`, `:52` region):
  scalar `xray_enabled: bool = false` (scalar like `mcdc_mode_text`: by-value
  aggregate copies of `CompileOptions` have corrupted nested fields before).
- CLI: `--xray` (boolean). The sled flavour (LLVM XRay vs Simple native) follows
  the selected backend; there is no separate backend knob.
- SDN: `trace.instrumentation: off|dynamic` (plan §5.3), mapped in
  `80.driver/driver_types.spl` next to the `coverage` mapping. `off` (default) ⇒
  `enabled=false`.
- Single gate: `xray_policy_resolve(enabled, compile_mode, backend, release) -> Result<XrayBuildPolicy, text>`
  called **once** in `CompileContext.create`; an `Err` (`XRAY-E-UNSUPPORTED-TARGET`)
  fails the compile before any pipeline runs, like the MC/DC config error.
  Emitters read only `MirFunction.xray_mode`. The SDN key lands with PR3.

---

## B. Static OFF (compile-time, zero cost)

**Gate point:** `XrayBuildPolicy.enabled == false` (the default). Every emitter checks
`MirFunction.xray_mode` and nothing else:

| Artifact | Off behaviour |
|---|---|
| `xray_policy_apply` | returns the input module object unchanged |
| `MirFunction.xray_mode` | stays `0`; not serialized |
| LLVM IR | no `function-instrument`/`xray-*` attrs, including no `xray-never` |
| Native objects | no sleds, no `.simple_xray_map`, no root symbol, no init-array entry |
| Link | no `clang_rt.xray`, no `-lrt/-ldl` additions, no `simple_xray_*` runtime |
| Cache keys | unchanged (below) |
| Windows | route resolves `Off` before any trace import (draft `observer_build_route_v1`) |

**Cache-key rule:** `80.driver/driver_native_prelower_cache.spl:131`
`option_identity` must append `|xray=on` **only when `--xray` is on**. Appending a token
for `off` would invalidate every existing prelower/object cache entry — a
measurable perf regression on every build. Same rule for `object_cache_key`
and `native_build_cache_scope_key`.
PR1 applies it to the prelower option identity, native no-op admission and
capsule function identity. `compile_options_hash_compute` is formally bound
(`src/verification/cache_protocol/source_bindings.txt`); its xray component
lands in PR3 together with the LiveKey model field and re-pin review (today
only SMF/spec callers reach it, and `--xray` rejects SMF output).

**Guard test (PR1, kept forever): `scripts/check/check-xray-static-off-identity.shs`**
1. Build fixtures (`hello`, multi-return, tail call, recursion) with the **same**
   compiler binary twice (default options), plus a baseline compiler built from
   the pre-PR base.
2. Compare: (a) MIR dump bytes, (b) emitted `.ll` text, (c) object
   `.text/.data/.rodata` section bytes and section/symbol lists
   (`llvm-readelf -S -s`), (d) final link command line and `DT_NEEDED`.
3. Assert absence: no section matching `xray|simple_xray`, no symbol `__xray_*`
   or `simple_xray_*`.
4. Whole-file `cmp` is attempted first; if the toolchain embeds non-deterministic
   bytes, fall back to the normalized comparison (plan §15 last paragraph).
   **Run-to-run determinism of today's objects was NOT measured for this proposal**;
   PR1 measures it and records which comparison mode the guard uses.
5. Verdict convention: `PASS — <n> artifacts compared` / `FAIL` / `ERROR — nothing was checked`;
   `--selftest` with a deliberately injected attr must FAIL.

---

## C. Dynamic OFF/ON (sleds present, runtime switch)

Stage 1 delegates dynamic ON/OFF to compiler-rt (`__xray_patch` /
`__xray_unpatch` / `__xray_patch_function`) behind the private LLVM adapter;
C.2 below is the Simple-owned stage-2/3 protocol. The facade calls are identical.

### C.1 Disabled cost

- AArch64: one taken `B #+32` per entry/exit (predicted, no memory access).
- x86-64: one `JMP rel8 +11` per entry/exit.
- Plus code-size/I-cache cost (32 B / 13 B per site). This is "low-overhead
  disabled", **not zero** (plan §14); PERF-01 measures before any default-on.

### C.2 Patch / unpatch protocol (plan §12.2, quiescent mode first)

1. Control plane: one serialized owner per module (`Busy` on conflict); hooks never lock.
2. Validate manifest (plan §11 steps 1-7), build immutable plan.
3. Prepare generation, rings, dispatcher *before* any site can reach them.
4. Establish patch mode: `quiescent` (default; startup or SOSIX-established
   quiescence) or `live` only where qualified per target.
5. W^X: record page protections; `RX → RW` (or `RWX` only if live-mode qualified
   forbids removing X from executing pages), write **only** the aligned
   activation word (u32 on AArch64, u16 on x86-64) with an atomic store, restore
   `RX` on every exit path.
6. I-cache sync: AArch64 `DC CVAU`/`DSB ISH`/`IC IVAU`/`DSB ISH`/`ISB` via
   `__builtin___clear_cache`; x86-64: cross-modifying-code rules (the existing
   no-op in `src/runtime/runtime_legacy_core.c:96-98` is **not** a CMC proof, plan §6).
7. Publish transition marker after sync completes.

**Leaves (Linux):** `rt_mprotect` (`runtime_legacy_core.c:115`, declared in
`src/os/hosted/dedicated_host_posix.spl:29`) and `rt_legacy_sync_instruction_cache`
(`runtime_legacy_core.c:96`, fails closed on unknown arch — keep that). The
loader's `native_make_rw/native_make_executable/native_flush_icache`
(`99.loader/loader/smf_mmap_native.spl`) are whole-symbol granularity and remain
the loader's; XRay gets a narrow page-range leaf:
`src/os/sosix/host/code_patch_adapter.spl` exposing
`code_patch_begin(range) / code_patch_store_u16|u32(addr,val) / code_patch_end(range)`
validated against registered manifest bounds only — never an arbitrary-address API.
**Windows (stage 3):** same adapter over `VirtualProtect` + `FlushInstructionCache`
(result checked), behind the stage-3 target feature.

### C.3 Thread safety — lockless by default

- Hot path (trampoline → collector): no locks, no allocation, no syscalls;
  packed atomic state word {closed, generation, reservations} with CAS admission
  (plan §12.4); per-thread fixed rings; overflow ⇒ loss counter.
- Control path: serialized; may block; never callable from a hook (`Busy`).
- Code/maps/dispatcher/generations are resident until process exit (no unload).

### C.4 Runtime API (V1 facade, plan §5.1; draft `observer_contract_v1`)

`capabilities / prepare / start / request_stop / drain / poll / flush / stats / release`
plus per-site selection inside `prepare(config, selection)`
(`TraceSelectionV1` = function-ID set). Enable/disable = `start`/`request_stop` on
a selection; per-function toggle = a new prepared selection (new generation).

### C.5 Fail-closed

- No manifest / sled ABI mismatch / build-id mismatch ⇒ `InstrumentationAbsent`/`InvalidMap`; nothing patched.
- Partial patch failure ⇒ close admission, keep all resident, record exact per-site
  state, controlled rollback via the same protocol; if rollback or I-cache sync
  fails ⇒ session `Faulted`, never "off".
- Unsupported profile/consistency ⇒ reject; never silently degrade to raw or off (plan §17).


### C.6 Stage-2 resident runtime and registration (PR5b, AArch64)

- **Trampoline** `__simple_xray_trampoline_v1` (asm in
  `src/runtime/xray/xray_native_runtime_aarch64.c`, Simple twin
  `std.common.trace.xray_native_trampoline_aarch64_v1`, compared word for word
  by `check-xray-native-inprocess-e2e.shs`). Entry: `w0` = site id, `x30` =
  sled + 24, sled already pushed x16/x17 and x0/x30. Saves x1-x15, x18,
  x29/x30, NZCV, FPCR, FPSR, q0-q31; passes (site id, sled return) to an
  allocation-free handler that finds the registered module by return address,
  checks the map row names that sled, and calls the one C channel producer
  (`xray_channel_producer_v1.h`, shared with PR4; twin
  `trace_native_channel_record_words_v1`).
- **Map base relocation:** the map header `text_base` field carries an
  `R_AARCH64_PREL64` against the object's `.text`; runtime text base = field
  address + signed(field). No dynamic relocation, valid in PIE and shared objects.
- **Registration (deliberate deviation from A.5's init-array):** the Simple
  control plane locates `.simple_xray_map` of a mapped module (`/proc/self/maps`
  bias + ELF section table, `xray_native_module_v1.spl`), admits it through
  `trace_native_map_validate_v1`, then registers it with the module's resident
  runtime (`simple_xray_native_register_module_v1`, which re-checks every row).
  `--xray` objects therefore carry no constructor or root symbol. Implemented
  and tested for dlopen'd modules (`XrayNativeDlModuleV1`). Locating works by
  path for any mapped image, but registering the MAIN EXECUTABLE needs a
  binding without dlopen (the runtime ABI has no `dlopen(NULL)`): it belongs to
  the in-binary control plane, which waits on a deployed pure-Simple compiler.
  One map per module: a link of several `--xray` objects concatenates their
  maps and is rejected (InvalidMap) until multi-map walking lands. Each `--xray` module
  links its own runtime with PROTECTED visibility (direct BL, no PLT veneer).
- **Channel publication:** `XrayNativeBoundLeafV1.install` publishes the arena
  through `XrayNativeDispatchPortV1` before any sled is patched (C.2 step 3).
- **Sled-kind agreement:** `XrayLlvmLeafV1.sled_kind()`; `prepare` refuses a
  leaf whose sled kind is not the adapter backend.
- **Quiescent only:** `begin` drops execute permission for the whole page, so no
  thread may execute code on that page during a switch; `Live` is refused.
- **Selection:** aspect extension `simple.trace/observer-v1.pointcuts` names
  canonical functions; each expands to all of its sleds (`xray_native_selection_v1`).

### C.7 Stage-2 x86-64 SysV leaves (PR6)

- Sled: the V1 `X64Rel32` template, 13 bytes, 2-aligned (the encoder pads an
  odd position with one `90`): `EB 0B` | `66 90`, `E8 rel32` (R_X86_64_PLT32 at
  +3, addend -4) to `__simple_xray_trampoline_v1`, `EB 04`, imm32 site id. Map
  rows: isa 1, abi profile 2 (`simple-x86_64-sysv-sled-v1`), len 13, align 2,
  off 0x0BEB, on 0x9066; text_base relocated by `R_X86_64_PC64`.
- Patch: one aligned u16 store of the activation word (`store_u16` on the
  `XrayCodePatchPortV1`, `rt_ptr_write_i16`). **Quiescent only** (Q6): no
  cross-modifying-code qualification for live patching.
- Runtime: `src/runtime/xray/xray_native_runtime_x86_64.c` owns the asm
  trampoline (bounded remedy, SysV variant of the merged Windows experiment:
  RFLAGS first, rax rcx rdx rsi rdi r8-r11, explicit 16-byte realignment,
  xmm0-15 via `movdqu`, MXCSR, DF cleared for the handler; upper ymm/zmm,
  opmask, x87/MMX, AMX/APX are NOT preserved, the handler is
  `-mgeneral-regs-only`) and the registration sled leaf (`E8` target, `EB 04`,
  id). Handler, registry and installer are shared with AArch64 through
  `xray_native_registry_v1.h` (static inline bodies; each ISA TU defines the
  two exported entry points). Simple twin:
  `std.common.trace.xray_native_trampoline_x86_64_v1`.
- Evidence lane on a non-x86 host: `check-xray-native-x86-64-objects.shs`
  (cross-emitted objects, relocations, sled disassembly, OFF object clean,
  twin vs assembled trampoline, patcher ops). Executing the patched code needs
  an x86-64 Linux host and is not part of that check.
---

## D. Backend-neutral V1 contract placement and the draft branch

### D.1 Placement

```
src/lib/common/trace/            observer_contract_v1 (port/trait), config, codec,
                                 session, collector, native_map, native_abi  — no OS imports
src/lib/nogc_sync_mut/trace/     observer_native_channel_v1 (rings), native patch manager
src/lib/nogc_sync_mut/trace/backend/llvm_linux/   stage 1 adapter (private)
src/lib/nogc_sync_mut/trace/backend/simple_native/  stage 2/3 core (private)
src/os/sosix/host/code_patch_adapter.spl           POSIX leaf (stage 2), Win32 leaf (stage 3)
```

Applications import only `std.common.trace.observer_contract_v1`. Backend
selection happens at build time from `XrayBuildPolicy.mode` + target; only the
selected adapter enters the import graph (plan §5.3). Stage 1→2→3 swaps the
adapter and sled ABI; the facade, statuses, events and map *model* are unchanged.
Objects must be rebuilt across sled ABIs; `sled_abi_version` + build-id reject
mismatches (plan §5.2).

Windows in stages 1-2: `trace_build_route_v1` rejects non-Linux triples before any
backend import; the Windows lane resolves `Off`; WIN-OFF-01 diff (plan §15) runs
on every PR in F.

### D.2 Draft branch `work/xray-v1-interface-20261103` — reuse vs revise

| Part | Verdict |
|---|---|
| `src/lib/common/trace/observer_contract_v1.spl`, `_config_v1`, `_event_codec_v1`, `_session_v1`, `_collector_v1`, `_native_map_v1`, `_native_abi_v1`, `_build_route_v1`, `_aspect_config_v1` | **Reuse** as the W0 port; map format reconciled with A.5 |
| `src/lib/nogc_sync_mut/trace/observer_native_channel_v1.spl` | Reuse (stage-2 transport) |
| `aspect_params.spl` (+1 const) | Reuse; fields/ordinals unchanged |
| `driver_observer_compile_gate_v1` called at **5** entry points (`aot_compile`, `stage_emit_object`, orchestration, `compile_vhdl_only`, pipeline execution) + AOP weave | **Revise:** collapse into the single `xray_policy_resolve` (A.6) |
| `if self.ctx.has_errors(): return CodegenError` added after `weave_aop()` in `driver_aot_pipeline.spl` and `driver_pipeline_execution.spl` | **Split out:** changes behaviour of every compile, unrelated to trace; own PR + review |
| `50.mir/mir_observer_site_intent_v1.spl` (name-based selection, rejects `is_inline`) | **Superseded** by `MirFunction.xray_mode` + policy (A.3/A.4); name-based selection moves to runtime aspect params; keep only its musttail/`Ret` rules as backend tests |
| `70.backend/backend/observer_llvm_host_shim_v1.spl` | Revise after PR3 decides attr emission site |
| Specs (18 files) | Status doc says UNRUN; must run green on admitted tooling |

**Safe to land as-is after the structural change? No.** Base is 1992 commits
behind (re-root as one commit on current release, own files only), the
`has_errors` change and the five-way gate must be split/collapsed first. After
those, it is safe: `driver_observer_request_v1` rejects every non-`Off` route, so
it is pure static-off scaffolding and passes the B guard by construction.

---

## E. Bootstrap impact

| Stage | Must understand new attrs/flag? | Why |
|---|---|---|
| Rust seed | **No** | It compiles Simple compiler *source*; it never consumes Simple MIR (`grep MirInstKind src/compiler_rust` → none). A defaulted struct field is ordinary source. Only Cranelift sled emission (A.5) would need seed work — deferred/rejected. |
| Stage 2 (seed-built Simple compiler) | Carries the code; builds itself with `--xray` off | Its own *output* for off must be byte-identical (B guard) |
| Stage 3 | Same | Stage 2 vs Stage 3 equivalence unaffected because off emits nothing |
| Stage 4 / full CLI | Unaffected unless built with `--xray` | Tools are never instrumented by default |

The compiler **binary** changes (new code); its **off-path output** must not. Land
the structure with no emitter active (PR1), so the bootstrap only has to compile
new defaulted fields. Bootstrap CI exercises both LLVM and Cranelift
(`.claude/rules/bootstrap.md:208`); the Cranelift `UnsupportedTarget` rule keeps
that lane untouched. Never build the compiler itself with `--xray` in a
sanctioned bootstrap.

---

## F. Landing sequence (structural first)

Every PR: B identity guard green (baseline = its own base), WIN-OFF-01 command /
dependency diff, Linux-only paths, TDD (failing spec first).

| # | PR | Content | Acceptance |
|---|---|---|---|
| 1 | `xray-structure` | `XrayBuildPolicy` option + `--xray` CLI flag, `MirFunction.xray_mode` (+`with_blocks`), `driver_xray_policy.spl` resolve+apply (never-list), cache-key token only when on, Cranelift rejection, `check-xray-static-off-identity.shs` | Field survives `with_blocks`/mir_opt; never-list spec; Cranelift + `--xray` rejected; off guard PASS; no emitter yet |
| 2 | `xray-v1-contract` | Re-rooted draft `src/lib/common/trace/**` + channel; no driver gate duplication | Draft specs run green; contract golden bytes; no OS import in common (import-graph check) |
| 3 | `xray-llvm-attrs` | A.5 LLVM attrs; Linux triples only | `.ll` contains attrs only when on; `llvm-readelf` shows `xray_instr_map` only when on; off guard PASS |
| 4 | `xray-llvm-adapter` | Private LLVM adapter + state-preserving handler shim + link of `clang_rt.xray` | Real Simple binary traced through facade on x86-64 + AArch64 Linux; ABI-01/02 (plan §16.2) |
| 5 | `xray-native-aarch64` | `xray_sled_emit` AArch64, `.simple_xray_map`, `code_patch_adapter` POSIX, quiescent patch | Object inspection; MAP-01; PATCH-02 fault injection; differential vs PR4 |
| 5b | `xray-aarch64-runtime` | Resident trampoline + handler, PREL64 map base, module registration, `--xray` link wiring, in-process quiescent patching, sled-kind agreement (C.6) | In-process e2e on a real `--xray` module; off identity |
| 6 | `xray-native-x86_64` | 13-byte sled, SysV profile, u16 quiescent patch, resident SysV trampoline + shared registry, `--xray` link wiring (C.7) | Object inspection, twin vs assembled trampoline, off identity; execution on an x86-64 host |
| 7 | `xray-native-live` | Qualified live patch per target | PATCH-01 stress |
| 8+ | `xray-windows-*` | COFF map, Win32 leaf, x64 then ARM64 profiles | Native runners, MIT-01, plan §9 gates |

Split out separately (own PR + review, any time): the `weave_aop` `has_errors` early-return change.

### Risks

- `with_blocks`-style manual copy constructors elsewhere drop the field silently (PR1 test).
- Sled before the regalloc-rebuilt prologue: `regalloc.spl:418` reorders block 0; sled insertion must run after it.
- Map `SHF_LINK_ORDER` + `--gc-sections` support in the in-house ELF writer is new work.
- x86 CMC: a u16 store over `EB 0B` is only safe under the qualified protocol; quiescent until then.
- Name/ID collisions across generic instantiations (plan §5.4) — canonical identity check.
- Draft staleness (1992 commits) may hide API drift in `AspectParamsV1`.

---

## G. Owner decisions (final, 2026-11-06)

| # | Question | Decision |
|---|---|---|
| Q1 | Attr spelling | **No `@xray` attribute.** Selection only via aspect params (A.2). |
| Q2 | Cranelift | **Unsupported in all stages:** `--xray` + Cranelift ⇒ `UnsupportedTarget`; no Rust seed changes. |
| Q3 | Static vs dynamic switch | **Both:** `--xray` (+ SDN key) is static, off by default; aspect params are dynamic (A.4). |
| Q4 | Cache key | Decided: default (owner may revisit) — append `xray` token only when on. |
| Q5 | Threshold | **Dropped.** All functions except the never-list get sleds when on. |
| Q6 | Stage 2 patch mode | Decided: default (owner may revisit) — quiescent-only on x86-64 until CMC is qualified. |
| Q7 | `knowledge_selection.sdn` | Decided: default (owner may revisit) — driver policy over MIR (A.4), not a host capability. |
| Q8 | Stage order | Decided: default (owner may revisit) — AArch64 first, then x86-64, for pure-Simple stages. |
| Q9 | Draft `has_errors` early-return | Decided: default (owner may revisit) — split out to its own PR + review, not part of XRay. |

---

## H. Data observations (cross-link)

Typed data observations — field read/write, collection operations and node
lifecycle — are **work package W5** of
[`doc/03_plan/compiler/data/data_attributes_layout_containers_xray_2026-11-06.md`](../../../03_plan/compiler/data/data_attributes_layout_containers_xray_2026-11-06.md)
(§10 shared XRay profiling architecture, §15.1 XR-01..12). They extend the V1
trace contract in `src/lib/common/trace` through a versioned record extension
and the existing facade/channel; they add no `@xray` attribute, keep the
`--xray` static-off identity guard authoritative, and select data sites only
through aspect params (section G, Q1/Q3).
