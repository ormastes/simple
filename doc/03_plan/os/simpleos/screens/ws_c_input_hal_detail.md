# Workstream C — Input drivers + HAL: detail implementation plan

Parent plan: `doc/03_plan/os/simpleos/screens_showcase_2d_opt_plan.md` (§ Workstream C, C1–C5).
Design: `doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md` §2.2, §2.4.
Lane state: `.spipe/simpleos-screens-render-lane/state.md` AC-5 (click/drag/keytype from the real
host/driver boundary reach the widget layer), AC-6 (keyboard+mouse reach simple-2d through **one**
event type and **one** queue).

Scope: everything from the device (PS/2 ports, virtio-input, USB HID, host winit/SDL2) up to the
point where a `HostInputEvent` is handed to the widget/WM layer.

---

## 0. Ground truth (verified in tree, 2026-08-06)

| Fact | Location |
|---|---|
| `enum Key` (~78 variants), `enum KeyEvent: Press(key)/Release(key)` | `src/os/drivers/input/ps2_keyboard.spl:25`, `:37` |
| Set-1 decode `scancode_to_key(code: u8) -> Key` | `ps2_keyboard.spl:41` |
| `class Ps2Keyboard{shift_held,ctrl_held,alt_held,caps_lock}`, `init()` at `:115`, `poll() -> KeyEvent?` at `:130`, `key_to_char(key) -> text?` at `:170` | `ps2_keyboard.spl:95`–`:243` |
| Keyboard is **polled only** — `poll()` reads `port_inb(0x64)` status at `:132` then `port_inb(0x60)` at `:136`. No IRQ1 handler exists anywhere in the tree. | — |
| `struct MouseState` (`x,y,left/right/middle_button,dx,dy,screen_width,screen_height`) | `src/os/drivers/input/ps2_mouse.spl:40` |
| `struct MouseEvent` (`x,y,dx,dy,left_pressed,right_pressed,middle_pressed,left_just_pressed,right_just_pressed,left_just_released`) — **no wheel/z field** | `ps2_mouse.spl:52` |
| 3-byte packet parse (`packet_byte0/1/2`, overflow bits `0x40/0x80`, sign bits `0x10/0x20`), absolute position + clamping, edge-triggered buttons | `ps2_mouse.spl:158`–`:305` |
| Controller cmds already defined: `CMD_WRITE_AUX=0xD4`, `MOUSE_CMD_SET_SAMPLE_RATE=0xF3`, `MOUSE_CMD_ENABLE_REPORTING=0xF4`, `MOUSE_CMD_RESET=0xFF` | `ps2_mouse.spl:25`–`:34` |
| No IRQ12 handler; config byte write at `:127-128` sets bit 1 / clears bit 5 but nothing registers a vector | — |
| **Dead parallel type system**: `class KeyEvent`(`scan_code,key_code,is_pressed,is_repeat,modifiers,timestamp_us`), `class MouseEvent`(`delta_x`,…), `TouchEvent`, `GamepadEvent`, `class InputEventQueue` (counters only — `record_key/record_mouse/record_touch/record_gamepad/total/stats`, **not a queue**, stores no events) | `src/os/drivers/input/input_event.spl:12,77,141,174,226` |
| **Zero consumers repo-wide** for `os.drivers.input.input_event` — a grep for the module path returns only unrelated `input_event_*` field names in `src/app/ui.browser/backend.spl:261-270`. | verified |
| De-facto abstraction: `trait InputBackend { me poll_key()->KeyEvent?; me poll_mouse()->MouseEvent?; fn alt_held/shift_held/ctrl_held()->bool; fn key_to_char(key: Key)->text? }` | `src/os/compositor/input_backend.spl:5` |
| 5 impls: `Ps2InputBackend` (`input_backend.spl:20`), `UartInputBackend` (`uart_input_backend.spl:43`, PL011, keyboard-only), `Arm64VirtioInputBackend` (`arm64_virtio_input_backend.spl:301`, `create()` sets `_available=false` — externs have no native/interpreter definition), `HostedInputBackend` (`hosted_input_backend.spl:193`, **winit-only**), `UsbHidInputBackend` (`usb/usb_hid_input_backend.spl:364`) | — |
| Compositor warns in a header comment that two incompatible `MouseEvent` types exist and that same-named types collapse in the global registry (first registration wins) → HIR error `struct 'ANY' field 'left_just_pressed'`; it works around this with an explicit `use os.drivers.input.ps2_mouse.{MouseEvent}` | `src/os/compositor/compositor.spl:6-13` |
| `handle_input()` / `_handle_input_backend()` / `_handle_input_ps2()`, incl. the "bind through a typed local so the optional carries a concrete MouseEvent type into lowering" workaround | `compositor.spl:~962`, `:~971`, `:~1010` (block at 942–1060) |
| HAL traits: HalConsole/HalBoot/HalCpu/HalPower/HalPaging/HalInterrupt/HalTimer/HalContext/HalEntropy/HalCstart/HalSyscall/HalCanary/HalBarrier/HalCache/HalSmp/HalPerCpu — **no `HalInput`** | `src/os/kernel/arch/hal.spl:86`–`:219` |
| `HalInterrupt.interrupt_set_handler(irq: u32, handler: u64)` declared at `hal.spl:128`; free fn `hal_interrupt_set_handler` at `hal.spl:386` → `hal_current.spl:159` → `arch_adapt/x86_64/interrupt.spl:27 interrupt_set_handler(vector, handler_addr)`. **Unused by input.** `hal_current.spl` is hard-wired to `arch_adapt/x86_64/*`. | — |
| Third independent input model: `InputSnapshot` + `set_current/current/key_down/key_pressed_this_frame/mouse_pos/mouse_down` | `src/lib/nogc_sync_mut/game2d/input/{api,snapshot,keys}.spl:22-42` |
| Widget consumers: `widget_dispatch_hover:79`, `widget_dispatch_click:93`, `widget_dispatch_scroll(root,w,h,px,py,dy):120`, `widget_dispatch_key(focused_id, key):311` | `src/lib/common/ui/widget_hit.spl` |
| WM app-process event contract `WmFsAppEvent` | `src/lib/common/ui/wm_app_process_contract.spl` |

Bugs this workstream closes:
- `doc/08_tracking/bug/wm_mouse_wheel_events_dropped_2026-07-05.md` — **Open, High**. Runtime emits
  `EVENT_MOUSE_WHEEL=22` but `src/os/hosted/hosted_entry.spl:108-151` and
  `src/app/ui.browser/app.spl:65-68,225-267` both drop it; right/middle buttons also discarded in
  `hosted_entry.spl:125-131`. → C3.
- `doc/08_tracking/bug/simpleos_arm64_qmp_input_transport_missing_2026-07-24.md` → C2/C6.
- `doc/08_tracking/bug/simpleos_wm_host_qmp_mouse_input_no_framebuffer_delta_2026-06-11.md` → C7.

---

## 1. Boundary with Workstream B (do not violate)

- **B1 owns the type.** `HostInputEvent` is *defined once* in `src/lib/common/ui/host_input_event.spl`
  (pure, `common` tier) by B1, together with `ScreenHost.poll_input() -> HostInputEvent?`.
- **Workstream C owns the producers**: PS/2 / virtio / USB-HID / UART / host-toolkit adapters, the
  IRQ path, the single queue, and the compositor consumption sites.
- C **must not** declare its own copy of `HostInputEvent`, nor a shadow `Pointer`/`Key` payload type
  in `src/os/**`. If B1 has not landed when C1 starts, C1 **blocks** — it does not stub the type.
  (Rationale: a second same-named declaration is exactly the failure documented at
  `compositor.spl:6-13`; the global registry collapses same-named types first-wins.)
- Shape C1 consumes (from B1, quoted here for reference only, authoritative copy is B1's file):

```
enum HostInputEvent:
    Pointer(x: i32, y: i32, dx: i32, dy: i32, button: i32, pressed: bool, wheel: i32)
    Key(code: i32, ch: text, down: bool, mods: i32)
    Resize(w: i32, h: i32)
```

`mods` bitfield: bit0 shift, bit1 ctrl, bit2 alt, bit3 meta, bit4 capslock (matches the existing
`KeyEvent.has_shift/has_ctrl` encoding at `input_event.spl:56-60`, which is the only prior art).
`button`: 0 none, 1 left, 2 right, 3 middle. `wheel`: signed detents, +1 = scroll up.

**Decision on `game2d` `InputSnapshot`: OUT OF SCOPE for this workstream.** It is a per-frame
polled *state snapshot*, not an event stream, it lives in the `nogc_sync_mut` tier, and it has its
own `KeyCode`/`MouseButtonId` vocabulary with live game consumers. Converging it would triple C1's
blast radius for no AC. What C *does* do (C8, optional) is add a one-way adapter
`input_snapshot_from_events([HostInputEvent], prev: InputSnapshot) -> InputSnapshot` so games can be
driven by the same queue without the queue knowing about games. Recorded here so the divergence is a
decision, not an oversight.

---

## 2. Architecture decision — `HalInput` trait: **NO. Keep `InputBackend`.**

**Recommendation: do not add a `HalInput` trait to `src/os/kernel/arch/hal.spl`.** Instead keep
`trait InputBackend` (moved/renamed as described in C1) as the single abstraction, and add exactly
one *narrow* HAL surface for the part that genuinely is arch-specific: IRQ registration, which
already exists as `HalInterrupt.interrupt_set_handler` (`hal.spl:128`).

Reasoning:

1. **`hal_current.spl` is hard-wired to `arch_adapt/x86_64/*`** (its import block, `:36`). A
   `HalInput` trait routed through `hal_current` would make PS/2 the *only* reachable input on every
   build, and would make the arm64/riscv64 virtio-input backends and the host winit/SDL2 backends
   unreachable — the exact opposite of the goal. `InputBackend` is already runtime-selected
   (`Compositor.input` is an optional trait object; `handle_input()` at `compositor.spl:~962`
   branches on `self.input != nil`), which is what a *device* abstraction needs and what a
   *link-time arch* abstraction cannot give.
2. **HAL traits in `hal.spl` are CPU/platform facilities** (paging, timer, context, barrier, canary).
   Input is a device tree concern, and SimpleOS already has a device-driver layer for it.
3. **Cost of the alternative is real**: 16 traits × per-arch adapters; adding a 17th forces an
   `arch_adapt/{arm64,riscv64}` input implementation to exist even where the answer is "no input
   device", and `Arm64VirtioInputBackend.create()` already returns `_available=false`
   (`arm64_virtio_input_backend.spl:301`) — availability is a *runtime* property here, not a
   compile-time one.
4. The only arch-specific bit — "attach ISR to vector N" — is already HAL'd. C2 uses it and adds
   nothing new to `hal.spl`.

Consequence: `InputBackend` moves up one level conceptually to "input HAL", gains a
`me poll_event() -> HostInputEvent?` method, and gets a queue in front of it. Registration of an IRQ
source is a separate, optional capability trait (`IrqInputSource`, C2) that only PS/2 implements
today.

---

## 3. Tasks

Dependency graph: `B1 → C1 → (C2, C3, C4 parallel) → C5 → (C6, C7)`. C8 optional, after C5.

### C1 — Unify the event type and the queue  *(model: **opus**)*

**Objective.** One event type (`HostInputEvent`, from B1), one queue, zero duplicate `MouseEvent`.
The tree must compile **after every numbered step below** — this is the riskiest task in the
workstream and is sequenced additively (add → migrate → delete), never delete-first.

**Files.**
- `src/os/drivers/input/input_event.spl` — **rewrite in place** (do not delete the file; delete its
  types). Verdict on the "delete vs rewrite" question: **rewrite**, because the *path* is the natural
  home for the queue and the file's four dead classes are exactly the duplicates being collapsed. New
  content: only `InputEventQueue` over `HostInputEvent`. `KeyEvent`/`MouseEvent`/`TouchEvent`/
  `GamepadEvent` classes are **deleted outright** (zero consumers — verified; they are not
  "unused code to keep", they are the second half of the dual-type bug).
  Touch/gamepad are not lost: they are re-expressed as future `HostInputEvent` variants owned by B1;
  until a driver produces them, no type exists for them (per "NEVER add unused code").
- `src/os/compositor/input_backend.spl` — trait gains `poll_event`.
- `src/os/compositor/compositor.spl:6-13` (header warning comment), `:942-1060`
  (`handle_input`/`_handle_input_backend`/`_handle_input_ps2`).
- All 5 `impl InputBackend for …` sites (listed in §0).
- `src/os/drivers/input/ps2_mouse.spl:52` — `struct MouseEvent` **deleted** at the end of C1.

**New `input_event.spl` (whole file, ~90 lines):**

```
use common.ui.host_input_event.{HostInputEvent}

val INPUT_QUEUE_CAP: i64 = 256

class InputEventQueue:
    """Single bounded FIFO of HostInputEvent. Producers: ISR (C2) or poll drain.
    Consumer: compositor / screen app. Fixed-capacity ring — no allocation on the
    ISR path."""
    buf: [HostInputEvent]      # preallocated to INPUT_QUEUE_CAP
    head: i64                  # next read index
    tail: i64                  # next write index
    count: i64                 # NEVER derived from a Dict/len() — maintained counter
    dropped: i64               # overflow counter, surfaced in stats()

impl InputEventQueue:
    static fn create() -> InputEventQueue
    me push(ev: HostInputEvent) -> bool      # false = dropped (full); O(1), no alloc
    me pop() -> HostInputEvent?              # nil when empty
    me len() -> i64                          # returns self.count
    me is_empty() -> bool
    me drain_into(sink: [HostInputEvent]) -> [HostInputEvent]
    me stats() -> text                       # "input queue: n=.. dropped=.. cap=.."
```

Notes: ring buffer, not a growing list — `push` must be ISR-safe (C2) and allocation-free.
`count` is an explicit field, never `Dict.len()`/`.length()` (see Traps).

**Trait change (`input_backend.spl:5`):**

> **SUPERSEDED — what actually landed (2026-08-06). Read this before following
> the steps below.**
>
> `poll_event` is **NOT a trait method**. It landed as a **free function**
> `input_backend_poll_event(backend)` in `input_backend.spl`, and the trait was
> left alone.
>
> Why: the zero-churn variant of this step — putting a **default body** on the
> trait so no impl needs editing — **SIGSEGVs (exit 139)** through a trait object
> when the default body calls the trait's own `fn`-declared methods. Byte-identical
> logic as a free function works. See
> `doc/08_tracking/bug/trait_default_body_segfaults_via_trait_object_2026-08-06.md`.
> The free function carries a comment forbidding a tidy-up back into a default
> body, because the refactor looks obviously correct and will be attempted again.
>
> (The prose below is accurate that the declaration must be **default-free** —
> that part was never the problem. The problem is only the tempting shortcut.)
>
> **Step 6 is DONE**: `poll_key`/`poll_mouse` are gone from the trait and all
> seven implementors plus their spec stubs are migrated. Verified at origin: zero
> `fn poll_key`/`fn poll_mouse` declarations remain on `trait InputBackend`.

```
trait InputBackend:
    # poll_event is NOT here — see the superseded note above.
    me poll_key() -> KeyEvent?              # REMOVED in step 6 (done)
    me poll_mouse() -> MouseEvent?          # REMOVED in step 6 (done)
    fn alt_held() -> bool
    fn shift_held() -> bool
    fn ctrl_held() -> bool
    fn key_to_char(key: Key) -> text?
```

**Ordered steps (each ends with a green build):**

1. Land `poll_event()` on the trait with a default-free declaration and implement it in all 5 impls
   **as a shim over the existing `poll_key`/`poll_mouse`**. For `Ps2InputBackend`:
   ```
   me poll_event() -> HostInputEvent?:
       if val k = self.poll_key():
           return host_key_event_from_ps2(k, self.shift_held(), self.ctrl_held(), self.alt_held())
       if val m = self.poll_mouse():
           return host_pointer_event_from_ps2(m)
       nil
   ```
   New pure translation helpers live in a new file
   `src/os/drivers/input/host_input_adapt.spl`:
   ```
   fn host_key_event_from_ps2(ev: KeyEvent, shift: bool, ctrl: bool, alt: bool) -> HostInputEvent
   fn host_pointer_event_from_ps2(ev: MouseEvent) -> HostInputEvent   # ps2_mouse.MouseEvent
   fn ps2_key_code(k: Key) -> i32                                     # stable numeric code
   fn mods_pack(shift: bool, ctrl: bool, alt: bool, meta: bool, caps: bool) -> i32
   ```
   `left_just_pressed`/`left_just_released` collapse into `Pointer{button:1, pressed:true|false}`;
   pure motion emits `Pointer{button:0, pressed:false}`. This is where the two `MouseEvent` field
   sets are reconciled — one place, testable in isolation (C1 spec).
   *Build must be green here.* Nothing consumes `poll_event` yet.
2. Rewrite `input_event.spl` to the ring queue above. Still no consumers → green.
3. Add `Compositor.input_queue: InputEventQueue` and a private
   `me _drain_input_source()` that calls `self.input.poll_event()` in a bounded loop
   (`while i < 64`) and pushes into the queue. Not yet called → green.
4. Rewrite `_handle_input_backend()` to: `self._drain_input_source()` then
   `while val ev = self.input_queue.pop(): self._apply_host_event(ev)`.
   `_apply_host_event(ev: HostInputEvent)` contains the logic currently at `compositor.spl:962-1060`
   re-expressed against the single type: `Key{down:true}` → `dispatch_gui_key_event` +
   `dispatch_gui_text_event` (preserving the existing ctrl/alt shortcut and
   `pending_meta_key`/`pending_shortcut` behaviour verbatim); `Pointer` → cursor clamp to
   `screen_width/height` + button dispatch; `wheel != 0` → scroll dispatch (wired in C3).
   `_handle_input_ps2()` is rewritten to build a `Ps2InputBackend` on the fly and go through the same
   drain, so **both** paths share one code path.
5. Delete the explicit `use os.drivers.input.ps2_mouse.{MouseEvent}` at `compositor.spl:13` and the
   6-line warning comment at `:6-13`, and the "bind through a typed local" workaround comment at
   `:~1005`. These exist solely because of the duplicate type.
6. Remove `poll_key`/`poll_mouse` from `trait InputBackend` and from all 5 impls (the drivers keep
   their own concrete `Ps2Keyboard.poll()`/`Ps2Mouse.poll()` — those are driver API, not the
   abstraction). Delete `struct MouseEvent` from `ps2_mouse.spl:52`; `Ps2Mouse.poll()` returns
   `HostInputEvent?` directly via `host_pointer_event_from_ps2` inlined. `ps2_keyboard.spl`'s
   `enum KeyEvent`/`enum Key` **stay** — they are the scancode-decode vocabulary and are covered by
   an existing spec; only their escape into the compositor is removed.

**Acceptance.**
```
bin/simple lint src/os/drivers/input/input_event.spl src/os/drivers/input/host_input_adapt.spl \
                src/os/compositor/input_backend.spl src/os/compositor/compositor.spl
bin/simple test test/01_unit/os/drivers/input/          # existing 2 specs still pass
grep -rn "struct MouseEvent\|class MouseEvent" src/os --include=*.spl   # expect: no matches
grep -rn "poll_mouse\|poll_key" src --include=*.spl                    # expect: no matches
```
Expected: lint clean; both existing specs (`ps2_keyboard_spec.spl`, `ps2_mouse_spec.spl`) pass with a
non-zero example count printed; both greps empty.
New spec `test/01_unit/os/drivers/input/host_input_adapt_spec.spl` (C1): asserts that a
`MouseEvent{left_just_pressed:true}` maps to `Pointer{button:1, pressed:true}`, a
`left_just_released` to `pressed:false`, motion-only to `button:0`, and that
`mods_pack` round-trips through `has_shift/has_ctrl` bit positions.
New spec `test/01_unit/os/drivers/input/input_event_queue_spec.spl`: FIFO order, `len()` after
N pushes/M pops, wrap-around across `INPUT_QUEUE_CAP`, overflow increments `dropped` and does not
corrupt `head`.

**Depends on:** B1 (`host_input_event.spl` landed).

---

### C2 — IRQ1 / IRQ12 path, with polling retained behind the same queue  *(model: **opus**)*

**Objective.** PS/2 keyboard and mouse deliver through interrupts; polling remains a fully supported
fallback selected at runtime, and **both** feed the same `InputEventQueue` so no consumer changes.

**Files.** `src/os/kernel/interrupts/` (new `ps2_irq.spl`), `src/os/drivers/input/ps2_keyboard.spl`,
`src/os/drivers/input/ps2_mouse.spl`, `src/os/compositor/input_backend.spl`, `src/os/kernel/arch/hal.spl`
(**read-only — no new trait**, per §2).

**Design.**

Split each driver into *ingest* (byte-level, ISR-safe) and *decode* (may allocate):

```
# ps2_keyboard.spl — added
impl Ps2Keyboard:
    me isr_ingest() -> bool          # ISR-side: read 0x60 ONCE, push raw u8 into
                                     # self.raw_ring, EOI. No decode, no alloc, no text.
    me decode_pending(q: InputEventQueue) -> i64   # task-side: drain raw_ring ->
                                     # scancode_to_key -> modifier update -> q.push(HostInputEvent)
```
```
# ps2_mouse.spl — added
impl Ps2Mouse:
    me isr_ingest() -> bool          # read 0x60 once, append to raw_ring
    me decode_pending(q: InputEventQueue) -> i64   # reassemble 3/4-byte packets, clamp, push
```

**What runs in the ISR (hard limit):** read the status port, read **one** data byte, store it in a
fixed-size `raw_ring: [u8]` (capacity 64, counter field, overflow drops + increments `raw_dropped`),
send EOI. Nothing else. No `text`, no allocation, no `HostInputEvent` construction, no trait dispatch
(trait-object dispatch from an ISR is not proven safe here). Packet reassembly, scancode→`Key`
mapping, modifier-state update, and `HostInputEvent` construction all happen in `decode_pending`,
called from the compositor's normal drain (`_drain_input_source`, C1 step 3).

**Registration** (new `src/os/kernel/interrupts/ps2_irq.spl`):

```
use os.kernel.arch.hal.{hal_interrupt_set_handler}     # hal.spl:386

val IRQ_KEYBOARD: u32 = 1
val IRQ_MOUSE: u32 = 12

fn ps2_irq_keyboard_handler():        # @interrupt-safe entry; address taken as u64
    ps2_keyboard_global().isr_ingest()

fn ps2_irq_mouse_handler():
    ps2_mouse_global().isr_ingest()

fn ps2_irq_install() -> bool:
    """Register IRQ1/IRQ12. Returns false if the platform has no PIC/APIC route,
    in which case the caller stays on polling."""
    hal_interrupt_set_handler(IRQ_KEYBOARD, fn_addr_of_ps2_irq_keyboard_handler())
    hal_interrupt_set_handler(IRQ_MOUSE, fn_addr_of_ps2_irq_mouse_handler())
    # unmask PIC lines: master bit 1, slave bit 4 (cascade bit 2 on master)
    pic_unmask(IRQ_KEYBOARD)
    pic_unmask(IRQ_MOUSE)
    true
```
Route via `hal.spl:386 hal_interrupt_set_handler` → `hal_current.spl:159` →
`arch_adapt/x86_64/interrupt.spl:27`. Do **not** call `interrupt_set_handler` from x86_64 directly —
that would re-hardwire what the HAL already abstracts.

Also enable IRQ generation in the controller config byte: `ps2_mouse.spl:127-128` currently computes
`(config | 0x02) & 0xDF`. Bit0 (`0x01`, port-1/keyboard interrupt) must additionally be set when
`ps2_irq_install()` succeeded — make the mask a parameter of the init:
`me init(enable_irq: bool)`, config = `enable_irq ? (config | 0x03) & 0xDF : (config | 0x02) & 0xDF`.
When IRQ install fails, leave the current polled config untouched — **byte-for-byte no regression**.

**Mode selection.** `Ps2InputBackend` gains a field `irq_mode: bool` set by
`Ps2InputBackend.create_auto()`, which attempts `ps2_irq_install()` and falls back:
```
static fn create_auto(kbd: Ps2Keyboard, mouse: Ps2Mouse) -> Ps2InputBackend
    # irq_mode = ps2_irq_install(); if false, polled
me poll_event() -> HostInputEvent?:
    if not self.irq_mode:
        self.keyboard.isr_ingest()      # same ingest fn, called from the poll loop
        self.mouse.isr_ingest()
    self.keyboard.decode_pending(self.queue)
    self.mouse.decode_pending(self.queue)
    self.queue.pop()
```
So polling and IRQ differ in **exactly one line** — who calls `isr_ingest`. Everything downstream is
identical, which is what "polling retained behind the same queue API" must mean to be safe.
An rc.conf/env override `SIMPLE_PS2_IRQ=off` forces polling for bisecting.

**Acceptance.**
```
bin/simple lint src/os/kernel/interrupts/ps2_irq.spl src/os/drivers/input/ps2_*.spl
bin/simple test test/01_unit/os/drivers/input/
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs     # boot must still reach the WM
```
Expected: lint clean; specs pass; QEMU wrapper reaches its existing PASS verdict line (a hung ISR
shows up as a boot hang, so a green boot is the primary regression gate).
Plus a new probe assertion: with `SIMPLE_PS2_IRQ=off` and with it on, the C7 QMP keystroke evidence
must produce the **same** transcript — proving the fallback is not a second code path with different
behaviour. Capture both transcripts to `doc/09_report/`.

**Depends on:** C1.

---

### C3 — Mouse wheel end-to-end  *(model: sonnet)*

**Objective.** Close `doc/08_tracking/bug/wm_mouse_wheel_events_dropped_2026-07-05.md` (Open, High):
wheel detents from PS/2 **and** from the host toolkits reach `widget_dispatch_scroll`.

**Files.** `src/os/drivers/input/ps2_mouse.spl`, `src/os/drivers/input/host_input_adapt.spl`,
`src/os/compositor/compositor.spl` (`_apply_host_event`), `src/os/hosted/hosted_entry.spl:108-151`,
`src/app/ui.browser/app.spl:65-68,225-267`, `src/lib/common/ui/widget_hit.spl` (consumer, unchanged).

**1. Enable IntelliMouse 4-byte mode (`Ps2Mouse.init`).** After reset/defaults and **before**
`MOUSE_CMD_ENABLE_REPORTING (0xF4)`, send the magic sample-rate knock, each byte prefixed by
`CMD_WRITE_AUX (0xD4)` on port 0x64 and ack-waited:
```
set_sample_rate(200); set_sample_rate(100); set_sample_rate(80)
send_aux(0xF2)                      # Get Device ID
val id = read_data()                # 0x03 => wheel present; 0x00 => plain 3-byte
self.has_wheel = (id == 0x03)
set_sample_rate(100)                # restore a sane rate
send_aux(MOUSE_CMD_ENABLE_REPORTING)
```
`set_sample_rate(r)` = `send_aux(0xF3); wait_ack(); send_aux(r); wait_ack()` using the existing
`MOUSE_CMD_SET_SAMPLE_RATE=0xF3` at `ps2_mouse.spl:33` and the existing ack-wait loops at `:229`/`:238`.
Optionally follow with the 200/200/80 knock for ID 0x04 (5-button); if it reports 0x04, bytes 4's
low nibble is the signed Z and bits 4/5 are buttons 4/5 — decode Z the same way and ignore 4/5 for now.

**2. Packet length becomes dynamic.** `packet_index` wraps at `self.has_wheel ? 4 : 3`. Byte 3 is the
Z byte: 4-bit signed two's complement in `z & 0x0F` for ID 0x04, full signed i8 for ID 0x03. Decode:
```
fn decode_wheel_z(byte3: i64, dev_id: i64) -> i32:
    if dev_id == 4:
        val n = byte3 & 0x0F
        return if n > 7: (n - 16) as i32 else: n as i32
    return if byte3 > 127: (byte3 - 256) as i32 else: byte3 as i32
```
Sign convention: PS/2 reports **positive Z = wheel down**; `HostInputEvent.wheel` is +1 = up, so
negate at the adapter boundary — in `host_pointer_event_from_ps2` only, once.

**3. Compositor dispatch.** In `_apply_host_event`, for `Pointer` with `wheel != 0`, call the
window-manager scroll route that ends in
`widget_dispatch_scroll(root, w, h, px, py, dy)` (`widget_hit.spl:120`) with
`dy = wheel * SCROLL_LINES_PER_DETENT` (3), coordinates already in surface-local space after the
existing hit-test translation used for clicks.

**4. Close the bug's other two halves** (the bug report names them explicitly, so the fix is not
complete without them):
- `hosted_entry.spl:108-151` — add a `kind == 22` (`EVENT_MOUSE_WHEEL`) branch producing
  `Pointer{wheel}`; and extend the button branch at `:125-131` beyond `button==0` to forward
  buttons 1 and 2 (the report's "Related Issue (M8)").
- `ui.browser/app.spl:65-68,225-267` — add the wheel case; the protocol layer already has
  `ScrollEvent` at `ui.ipc/protocol.spl:181-191,230-239`, so this is a translate, not a new protocol.

**5. Update the bug file** to Status: Fixed with the commit sha, the QEMU/host transcript path, and
the spec names. Do not close without captured evidence.

**Acceptance.**
```
bin/simple test test/01_unit/os/drivers/input/ps2_mouse_spec.spl
grep -rn "EVENT_MOUSE_WHEEL\|kind == 22" src/os/hosted/hosted_entry.spl src/app/ui.browser/app.spl
```
New spec cases in `ps2_mouse_spec.spl`: 4-byte packet with `byte3=0xFF` → `wheel:+1` (after
negation), `byte3=0x01` → `wheel:-1`, `dev_id==4` nibble form `0x0F` → `-1`, and a 3-byte packet on a
non-wheel mouse still yields `wheel:0` and correct dx/dy (no regression on the existing cases).
Host-side: `sh scripts/check/check-hosted-wm-capture-evidence.shs` plus a wheel injection in the C7
harness showing the probe pane's scroll offset changing.

**Depends on:** C1.

---

### C4 — SDL2 host `InputBackend`  *(model: sonnet)*

**Objective.** Fill the winit-only gap: `src/os/compositor/hosted_input_backend.spl:193` is winit;
`src/os/compositor/hosted_backend_sdl2.spl` (display) references an input peer that does not exist.

**Files.** New `src/os/compositor/hosted_input_sdl2.spl`; touch `hosted_backend_sdl2.spl` to
construct it; check `src/app/hosted_apps/compositor/hosted_input_backend.spl` for a second call site.

**Shape.**
```
class Sdl2InputBackend:
    _available: bool
    mods: i32
    last_x: i32
    last_y: i32
    static fn create() -> Sdl2InputBackend    # probes the SDL2 externs; _available=false if absent

impl InputBackend for Sdl2InputBackend:
    me poll_event() -> HostInputEvent?:
        if not self._available: return nil
        val kind = sdl2_poll_event()        # 0 = none
        ... translate SDL_KEYDOWN/KEYUP/MOUSEMOTION/MOUSEBUTTONDOWN/UP/MOUSEWHEEL/WINDOWEVENT_RESIZED
```
Externs required (declare in the SDL2 SFFI module the display backend already uses, **not** as bare
`@extern fn` in this file — see Traps): `sdl2_poll_event`, `sdl2_event_kind`, `sdl2_event_key_code`,
`sdl2_event_key_mods`, `sdl2_event_text`, `sdl2_event_mouse_x/_y`, `sdl2_event_mouse_button`,
`sdl2_event_wheel_y`, `sdl2_event_resize_w/_h`. If any is unregistered, `create()` **must** return
`_available=false` rather than silently polling nil forever (the `Arm64VirtioInputBackend` precedent
at `arm64_virtio_input_backend.spl:301` is the pattern; make the unavailability *logged*, not silent).

**Acceptance.**
```
bin/simple lint src/os/compositor/hosted_input_sdl2.spl
bin/simple test test/01_unit/os/compositor/hosted_input_sdl2_spec.spl
mcp play_sdl2_connect / play_sdl2_click / play_sdl2_screenshot   # live proof via the SDL2 MCP tools
```
Expected: a click injected via `play_sdl2_click` produces a screenshot delta in the target window.
Capture the before/after screenshots into `doc/09_report/`.

**Depends on:** C1.

---

### C5 — Input → simple-2d screen app  *(model: sonnet)*

**Objective.** The `2d` screen app produced by Workstream A's `backend_factory.spl` consumes the one
queue and routes into the widget layer. This is where AC-6 is actually satisfied end to end.

**Files.** A2's screen app shell (`src/os/compositor/screen_app_2d.spl` per WS-A), plus
`src/os/compositor/backend_factory.spl` (A1) for wiring; `src/lib/common/ui/widget_hit.spl` consumed
unchanged; `src/lib/common/ui/wm_app_process_contract.spl` (`WmFsAppEvent`) for the `wm` screen type.

**Frame loop:**
```
me tick():
    var n = 0
    while n < 64:
        val ev = self.host.poll_input()     # ScreenHost.poll_input (B1) -> HostInputEvent?
        if ev == nil: break
        self.queue.push(ev)
        n = n + 1
    while val ev = self.queue.pop():
        self._route(ev)
    if self.dirty: self.host.present_scene(self.build_scene())

me _route(ev: HostInputEvent):
    # Pointer, pressed, button==1        -> widget_dispatch_click(root,w,h,x,y,layout)
    # Pointer, button==0                 -> widget_dispatch_hover(root,w,h,x,y)
    # Pointer, wheel != 0                -> widget_dispatch_scroll(root,w,h,x,y,wheel*3)
    # Key,     down                      -> widget_dispatch_key(self.focused_id, ch_or_name)
    # Resize                             -> self.resize(w,h); self.dirty = true
```
Drag = `Pointer{pressed:true}` followed by `Pointer{button:1, pressed:true}` motion events; the app
holds `drag_active` + `drag_origin` and forwards a synthesized drag to the widget layer's existing
hover/click routes (no new widget API).
`ScreenHost` impls for `wm` translate `WmFsAppEvent` into `HostInputEvent` — the WM file/env bridge
becomes just another adapter, not a parallel event model.

**Acceptance.**
```
bin/simple test test/01_unit/os/compositor/screen_app_2d_input_spec.spl
```
Spec feeds a scripted `[HostInputEvent]` through `_route` against a fixture widget tree and asserts
the returned dispatch ids from `widget_dispatch_click/scroll/key` (they return `text`), including a
3-event drag sequence and one wheel event.

**Depends on:** C1, C3 (wheel), A2 (screen app shell).

---

### C6 — arm64/riscv64 virtio-input producer  *(model: sonnet)*

**Objective.** Make `Arm64VirtioInputBackend` real, or record the block explicitly. Closes/updates
`doc/08_tracking/bug/simpleos_arm64_qmp_input_transport_missing_2026-07-24.md`.

**Files.** `src/os/compositor/arm64_virtio_input_backend.spl:301`,
`src/os/kernel/arch/{arm64,riscv64}/virtio_input.spl`,
`src/os/drivers/virtio/virtio_input_{mmio,ops,wire}.spl`.

**Work.** `create()` hard-codes `_available=false` because the virtio-input externs have no native or
interpreter definition. Two outcomes are acceptable, in this order of preference:
1. Provide the definitions and implement `poll_event()` translating Linux evdev codes
   (`EV_KEY`/`EV_REL`/`EV_ABS`, `REL_WHEEL`) into `HostInputEvent`; then
   `sh scripts/check/check-arm64-virtio-input-preflight.shs` and
   `sh scripts/check/check-simpleos-arm64-qmp-input-evidence.shs` must both reach PASS.
2. If (1) is out of budget, leave `_available=false` **and** update the bug file with the precise
   missing extern list and the file:line where each is declared. Do not leave it implicit.
Per `.claude/rules/board-runnable.md`, state explicitly that virtio-input is a QEMU transport and
name the physical-board input path (USB HID via `usb_hid_input_backend.spl:364`) rather than
implying board coverage.

**Depends on:** C1.

---

### C7 — Tests + QEMU evidence (AC-5)  *(model: sonnet)*

**Objective.** Captured, reproducible proof that a **typed character** and a **pointer drag**
originating at the real driver/host boundary reach the widget layer. Assertions in a spec are not
sufficient for AC-5 — the evidence must be a transcript or framebuffer delta produced by a wrapper.

**Unit specs (all new/extended, run under `bin/simple test`):**

| Spec | Covers |
|---|---|
| `test/01_unit/os/drivers/input/ps2_keyboard_spec.spl` (extend) | set-1 scancode → `Key` for a letter, a modifier, and a break code (`\|0x80`); `key_to_char` shift/caps matrix |
| `test/01_unit/os/drivers/input/ps2_mouse_spec.spl` (extend) | 3-byte and 4-byte packets; sign/overflow bits; clamping; wheel decode (C3) |
| `test/01_unit/os/drivers/input/host_input_adapt_spec.spl` (new) | the dual-`MouseEvent` collapse (C1) |
| `test/01_unit/os/drivers/input/input_event_queue_spec.spl` (new) | FIFO, wrap, overflow (C1) |
| `test/01_unit/os/compositor/screen_app_2d_input_spec.spl` (new) | routing to `widget_dispatch_*` (C5) |
| `test/01_unit/os/compositor/hosted_input_sdl2_spec.spl` (new) | SDL2 translation table (C4) |

**QEMU evidence wrapper.** New `scripts/check/check-simpleos-2d-input-evidence.shs`, modelled on the
existing `scripts/check/check-simpleos-arm64-qmp-input-evidence.shs` (QMP `sendkey` / mouse
injection) and `scripts/check/check-qemu-capture-fake-qmp-evidence.shs` (screendump capture +
delta). Real-firmware boot only (OVMF pflash) per `.claude/rules/board-runnable.md` — never
`-kernel`, never `isa-debug-exit`. Steps:
1. Boot the 2d screen type (`SIMPLE_SCREEN_TYPE=2d`) to the showcase with a **probe pane** that
   renders the last N `HostInputEvent`s as text.
2. `screendump` → `before.ppm`.
3. QMP `{"execute":"sendkey","arguments":{"keys":[{"type":"qcode","data":"a"}]}}`.
4. QMP mouse: `input-send-event` `rel`/`btn` sequence for press → move ×N → release (the drag).
5. QMP `input-send-event` `wheel-up` for the C3 proof.
6. `screendump` → `after.ppm`; assert byte-delta non-zero **and** grep the serial log for the probe
   pane's structured line, e.g. `INPUT: Key ch=a down=1 -> widget=<id>` and
   `INPUT: Pointer drag (x0,y0)->(x1,y1) -> widget=<id>` and `INPUT: Pointer wheel=+1 -> widget=<id>`.
7. Print one verdict line, last line of stdout: `PASS — 3 injected events observed at widget layer`
   or `FAIL — …`. A run that injects 0 events must print `ERROR — nothing was checked` and exit 2
   (match the pre-push guard convention in `.claude/rules/vcs.md`).
Artifacts (`before.ppm`, `after.ppm`, serial log) land in `doc/09_report/` and are referenced from
the bug files being closed. Also re-run `sh scripts/check/check-simpleos-wm-host-seam-evidence.shs`
and `check-hosted-wm-capture-evidence.shs` for the host lanes, which closes
`simpleos_wm_host_qmp_mouse_input_no_framebuffer_delta_2026-06-11.md` if the delta is now non-zero
(if it is still zero, update that bug with the new evidence — do not silently leave it).

**Depends on:** C2, C3, C5.

---

### C8 — (optional) game2d bridge  *(model: sonnet)*

One-way adapter `input_snapshot_from_events(evs: [HostInputEvent], prev: InputSnapshot) -> InputSnapshot`
in a new `src/lib/nogc_sync_mut/game2d/input/from_host_events.spl`, so `game2d`
(`api.spl:22-42`) can be driven by the unified queue without `common` depending on `game2d`.
No change to `InputSnapshot`, `KeyCode`, or `MouseButtonId`. Skip if C1–C7 consume the budget; the
divergence is a recorded decision (§1), not debt to be hidden.

---

## 4. Traps (repo hazards that have burned this area before)

1. **Same-named types collapse first-wins in the global registry.** This is the root cause of the
   compositor's warning at `compositor.spl:6-13` and of the `struct 'ANY' field 'left_just_pressed'`
   HIR error. During C1 there must never be two live `MouseEvent` declarations *and* two live
   `KeyEvent` declarations in the reachable graph — that is why step 2 rewrites `input_event.spl`'s
   classes away in the *same* step that introduces the queue, and why `HostInputEvent` is declared
   only by B1.
2. **Unregistered `@extern fn` returns nil silently under JIT.** It is not a link error. C4's SDL2
   externs and C6's virtio externs must be probed at `create()` and reported as
   `_available=false` with a log line — never assumed working because "it compiled and ran".
3. **Dict native pitfalls.** Under native codegen `Dict.len()` returns `-1` and `.get()` on a
   struct/class/enum value type is corrupt or segfaults
   (`doc/07_guide/language/dict_native_pitfalls.md`). The event queue therefore uses a **fixed array
   ring + explicit `count` field**, never a Dict, and never `.len()`/`.length()` on a Dict. If any
   keycode lookup table is needed, use `contains_key(k)` + index read `d[k]`, or a match.
4. **Evidence must be captured, not asserted.** A passing spec does not satisfy AC-5. The QEMU
   wrapper must emit artifacts and a verdict line; a wrapper that checks nothing must exit 2, not 0
   (the fail-open pattern documented in `.claude/rules/vcs.md`).
5. **Never skip a failing test without approval.** If a wheel or IRQ spec fails, fix it or file a
   bug — do not mark it pending. Do not convert TODO to NOTE.
6. **Default tooling is the self-hosted binary,** not the Rust seed. Verify `readlink -f bin/simple`
   points at `bin/release/<triple>/simple` before trusting a green run; a green run from a stale
   scratch build proves nothing.
7. **ISR discipline.** Anything allocating, taking a lock, doing trait dispatch, or building `text`
   inside `isr_ingest` risks a boot hang that presents as "QEMU shows a black screen". Keep the ISR
   to: status read, one data-port read, ring store, EOI.
8. **Don't regress polling.** The polled path is what works today on every target. C2 must keep the
   controller config byte identical when IRQ install fails, and the `SIMPLE_PS2_IRQ=off` transcript
   must match the IRQ-on transcript (C2 acceptance).
9. **Never delete a live consumer while "deduplicating".** Deleting a reimplementation reroutes
   callers, it does not remove work — C1's grep-based acceptance checks exist to prove the reroute
   actually happened rather than leaving an orphan.
10. **Bug files close only with evidence.** `wm_mouse_wheel_events_dropped_2026-07-05.md` names three
    distinct call sites; fixing one and closing the bug leaves siblings live.
