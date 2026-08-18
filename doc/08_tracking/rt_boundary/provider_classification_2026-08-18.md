# rt_* provider classification — top non-allowlisted offenders (2026-08-18)

Owner: lane-rt-bitstream (ormastes@gmail.com). Authority:
`doc/01_research/infra/sspec_binary/binary_sspec_rt_hardening_frozen_design_2026-08-18.md`
section 12 "When an alias is permitted".

## Honesty statement

**Allowlisting HIDES a count; it does not reduce it.** Every entry below leaves
the same number of direct `rt_*` call sites in the tree — it only moves them from
the `forbidden_product` bucket to `allowed_provider`. Only migration to a pure
Simple API (design section 12, Phase B/C) actually reduces the number. Entries
here are justified as genuine ABI boundaries, not as a way to make the gate green.

## Measurement (grep only — `check-no-direct-rt.shs` deliberately NOT run)

Regex `^[^#]*\brt_[a-z0-9_]*\(` over `src/**/*.spl`, excluding `**/vendor/**`.
Note this regex also counts `extern fn rt_foo(...)` DECLARATION lines, so a pure
binding header inflates the count; that is a measurement artifact of the gate,
recorded here rather than papered over.

| | sites |
|---|---|
| direct total (all src/**.spl, non-vendor) | 21191 |
| forbidden before this change | 18788 |
| newly allowlisted (2 files) | 222 |
| **forbidden after this change** | **18566** |

(The gate script's own baseline reads 12948; it scopes/normalises differently.
The 18788 -> 18566 delta is the number measured by the regex above and is the
only figure this record claims.)

Stale intel: the task brief listed `src/os/kernel/arch/riscv32/boot.spl` (~156),
`src/lib/common/wine_process_session.spl` (~139) and
`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` (~139). Measured
today they are **13, 0 and 3** sites respectively. They are not offenders.

## Classification of the real top offenders

### ALLOWLISTED — genuine boundary (2 files)

**`src/lib/nogc_sync_mut/io/vulkan_sffi.spl`** (111 sites, 74 of them `extern fn`
declarations)
- Family: `rt_vulkan_*` (create/destroy/bind/device/copy/compile/submit/get).
- Boundary: the Vulkan loader/ICD C ABI. These are handle-passing thunks into
  the installed GPU driver. Pure Simple cannot replace a vendor driver; there is
  no representation conversion, the file is the tier-1 binding layer.
- To retire it: a pure-Simple Vulkan loader plus in-Simple SPIR-V submission —
  i.e. reimplementing a vendor driver interface. Not plausible; the realistic
  end-state is that this file stays the single sanctioned provider and all
  callers go through the tier-2 wrappers it exports.

**`src/lib/nogc_sync_mut/io/metal_sffi.spl`** (111 sites, 43 `extern fn`)
- Family: `rt_metal_*` (init/create/destroy/device/buffer/load/wait/set).
- Boundary: Apple Metal, an Objective-C framework reachable only through the C
  shim in the runtime. Same argument as Vulkan, and additionally platform-gated
  (macOS/iOS hardware).
- To retire it: a pure-Simple Objective-C message-send ABI plus Metal object
  model. Same conclusion as above.

Both are tier-1 extern blocks with tier-2 pass-through wrappers; the branching
present (32 / 20 `if`/`for` lines) is availability and null-handle checking, not
business logic.

### REFUSED — product code that must migrate

- `src/lib/nogc_async_mut/linalg/backend_ops.spl` (177) and
  `src/lib/nogc_sync_mut/linalg/blas_openblas.spl` (103): dominated by
  `rt_alloc`/`rt_free`/`rt_ptr_write`/`rt_ptr_read` (170 and 99 of the sites).
  Raw allocation and pointer stores are exactly what a pure-Simple buffer type
  is for. Only the handful of `rt_scilib_openblas_*` calls are a real boundary,
  and they do not license the file.
- `src/os/apps/sshd/ssh_session_kex.spl` (137): **114 are `rt_push_byte`** — byte
  buffer building, pure product logic. The genuine crypto primitives
  (`rt_tls13_*`, `rt_ssh_curve25519_*`) are ~20 sites and belong behind a
  provider module, not this one.
- `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` (106): 93
  `rt_enum_discriminant` + `rt_tuple_get` — compiler lowering reaching into
  runtime value representation. Product code; belongs behind a value-accessor API.
- `src/lib/common/torch/dyn_sffi_ops.spl` (189): its own header says it is the
  *dynamic dispatch* layer built on top of the static externs in
  `std.torch.sffi`, with graceful-degradation branching (`rt_torch_available()`
  guards, 71 sites). That is policy logic, not a boundary. It should call the
  provider, not the runtime.
- `src/app/io/window_ffi.spl` (124), `src/app/io/window_sffi.spl` (124),
  `src/app/io/graphics2d_*.spl`, `src/app/io/rapier2d_*.spl`: byte-level
  duplicates of the `src/lib/nogc_sync_mut/io/` bindings. Duplication is not a
  boundary — the fix is deletion in favour of the lib module. Allowlisting these
  would sanctify a copy-paste fork.

### NEEDS OWNER DECISION (not allowlisted today)

- `src/lib/nogc_sync_mut/io/window_sffi.spl` (157, `rt_sdl2_*`/`rt_winit_*`) and
  `src/lib/nogc_sync_mut/io/graphics2d_sffi.spl` / `rapier2d_sffi.spl`: the
  `rt_sdl2_*` family is a genuine external-library ABI, but these files also
  carry event decoding and pixel-format packing (documented in their headers) —
  real logic mixed into the binding tier. Needs an owner to split binding from
  logic before a provider claim is honest.
- `src/lib/nogc_sync_mut/torch/sffi.spl` (137) and
  `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl` (144): plausibly the same
  case as the two allowlisted files, but `engine2d` names an engine, and libtorch
  availability is optional-at-runtime; both need an owner to confirm they are
  binding-only before being sanctioned.

---

## Round 2 (2026-08-18) — the three "needs owner decision" files, decided

Owner decision taken by lane-rt-bitstream. **Verdict: all three REFUSED. No
allowlist line added. Measured forbidden-count delta = 0.**

Path correction: the brief's `src/lib/common/torch/sffi.spl` does not exist; the
file is `src/lib/nogc_sync_mut/torch/sffi.spl` (as round 1 recorded).

### Measured (grep only; `check-no-direct-rt.shs` deliberately NOT run)

`total` = `^[^#]*\brt_[a-z0-9_]*\(`; `extern` = `^\s*(pub )?extern fn rt_`;
`shimdefs` = `^\s*(pub )?fn rt_[a-z0-9_]*\(` (Simple functions *named* `rt_*` —
these are definitions, not calls, and are themselves a boundary violation: a
public symbol must not carry an `rt_` name, design section 12).

| file | total | extern | shimdefs | genuine calls |
|---|---|---|---|---|
| `src/lib/nogc_sync_mut/io/window_sffi.spl` | 157 | 66 | 12 | **79** |
| `src/lib/nogc_sync_mut/torch/sffi.spl` | 137 | 133 | 2 | **2** |
| `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl` | 144 | 56 | 0 | **88** |

Confirms the filed measurement defect: torch/sffi.spl's headline 137 is 97%
declarations and it is in truth a 2-call-site file. It is one of the smallest
offenders in the tree, not one of the largest.

### `window_sffi.spl` — MUST MIGRATE (or split)

`rt_sdl2_*` is a genuine external-library ABI, but only ~45 of the 79 calls are
thin handle thunks. The rest is logic:
- **Event decoding**, a hand-written SDL event-code state machine:
  `window_sffi.spl:460-470` (`if window_event == 4: EventType.WindowMoved / == 5
  or == 6: WindowResized / == 10: CursorEntered ...`) and `:520-526`
  (`val vkey = parse_virtual_key(keysym)`, `val state = if event.handle == 2:
  KeyState.Pressed else: KeyState.Released`, `sdl2_normalize_modifiers(...)`).
  Mapping integer codes to Simple enums is pure Simple work.
- **Pixel packing** — header `:7` "each i64 is packed as R*16777216 + G*65536 +
  B*256 + A".
- **A whole winit compatibility shim**, `:718-800`, twelve `fn rt_winit_*`
  definitions that re-express SDL events as the retired winit API
  (`fn rt_winit_event_keyboard_input(...)` at `:742`). That is a translation
  layer wearing an `rt_` name — the exact anti-pattern section 12 forbids.
Correct fix: split the ~66 `extern fn rt_sdl2_*` declarations plus their thin
thunks into a provider module, and move decoding/packing/the winit shim into
ordinary product code. Allowlisting the current file would sanction 34+ logic
call sites.

### `torch/sffi.spl` — MUST MIGRATE (deletion, not allowlist)

Its own header, `:1-3`: *"torch SFFI Bindings (NoGC — Duplicated) / Duplicated
from gc_async_mut/torch/ffi.spl to avoid cross-mode import warnings."* This is a
copy-paste fork, the same disqualification round 1 applied to
`src/app/io/window_*.spl`. Duplication is not a boundary. Its 2 real calls
(`:57`, `:60`) are pass-throughs to `rt_ps_torch_*`. Allowlisting would sanctify
the fork and hide a 2-site file; the real defect is the duplication and the
cross-mode-import limitation that forced it.

### `gpu/engine2d/sffi_vulkan.spl` — MUST MIGRATE (not a second Vulkan provider)

Not a binding layer. Header `:1`: *"Vulkan SFFI Dispatch — Static/Dynamic
Dual-Path ... supports both static (extern fn) and dynamic (DynLib) dispatch"* —
i.e. the same dispatch-policy shape as `torch/dyn_sffi_ops.spl`, refused in
round 1. The `case Static: rt_vulkan_*` arms (`:270-412`) are thin, but the file
also carries:
- **ABI-mode policy branching**: `if gpu_sffi_uses_interpreter_array_abi():`
  at `:99`, `:117`, `:128` selecting between two call shapes.
- **Buffer building / byte packing**: `_vulkan_read_buffer_strided_bytes_abi`
  `:106-135` — bounds policy (`if row_count > 16384 or src_stride < row_bytes`),
  an 8K-surface size cap, and a manual row-by-row `packed.push(bytes[i])` loop.
- **Device-selection policy**: `vulkan_sffi_find_headless_device` `:790-800`
  scanning devices for `dt == "cpu" or dt == "CpuOnly"` (lavapipe heuristic).
It also re-declares `rt_vulkan_*` externs already owned by the allowlisted
`src/lib/nogc_sync_mut/io/vulkan_sffi.spl`. There must be exactly one sanctioned
provider per `rt_` family; a second one is a fork, not a boundary. This file
should call that provider.

### Net effect

allowlist unchanged (still 2 files / 222 sites from round 1); forbidden count
unchanged at the round-1 figure of **18566** by the regex above. 10 candidates
examined across two rounds, 2 allowlisted, 8 refused.
