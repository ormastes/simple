<!-- codex-design -->
# WM Full-Stack Demo Detail Design

## Frozen Names

- Native record: `WindowEventRecord`
- Status values: `WindowStatus`
- Canonical facade: `SimpleWindow`
- GLFW facade: `SimpleGlfw`
- Content discriminator: `WmContentKind`
- Child widget: `RenderSurface`
- Scenario setup: `setup_wm_full_stack_demo`
- Event injection: `inject_window_event`
- State checker: `check_wm_full_stack_demo_state`
- Evidence capture: `capture_wm_full_stack_demo_evidence`

## Window/Event Data

`WindowEventRecord` contains event/window generation handles, sequence,
timestamp, kind, key/scancode/action/modifiers, text handle/length,
pointer/wheel milli-units, and width/height. The queue is bounded and FIFO.

Headless and GLFW use identical enqueue/dequeue code. GLFW callbacks only
translate native values and enqueue. Key and committed-text events are
independent. Text arena entries are released after consumption.

## Content Data

`WmContentKind` values are EMPTY, GUI_SESSION, WEB_DOCUMENT, and PIXEL_SURFACE.
The owning window retains kind, generation handle, and revision. Registries
reject stale generations and expose live counts for cleanup evidence.

GUI production:

1. Resolve `UISession`.
2. Compute layout and widget Draw IR.
3. Execute through the existing Engine2D/pixel executor.
4. Build `wm_gui_content_frame_from_pixels`.

Web production keeps the existing canonical renderer. Pixel surfaces provide
dimensions, format, revision, dirty rectangle, and pixel handle and become a
frame directly. Freestanding storage is a generation handle over a bounded raw
registry; scalar reads drive the SimpleOS backend. High-level host/evidence
code may materialize a local pixel array when building `WmContentFrame`.

`RenderSurface` carries child content kind/handle, fit mode, clipping, focus
proxy, pointer translation/capture, and child revision. It emits a nested
`WmContentFrame`; it does not own another compositor.

## Event Routing

1. System shortcuts.
2. WM shortcuts.
3. Chrome hit test/capture.
4. Client-local hit test.
5. Focused widget keybindings.
6. Text editing command.
7. Separate committed text.

Titlebar, scrollbar thumb, and 2D panel drags use one pointer-capture record.
Release ends capture outside bounds. Minimize/close cancels it.

SimpleOS stores tree and focused-widget state behind each GUI generation
handle, then reconstructs a local `UISession` only while dispatching or
rendering. This keeps freestanding authority scalar/flat instead of embedding
large session aggregates in the compositor. Desktop coordinates are translated
from the selected or captured window into its client rectangle before
`UIEvent.MouseEvent` dispatch. Tree replacement clears retained focus.
Focused GUI dispatch handles physical shortcuts before a separate
`CompositionCommit`; the SimpleOS desktop clipboard is retained as scalar text
so reconstructed sessions preserve Ctrl+C/X/V without retaining a session
aggregate.

`WindowEventLoop` stores fixed records as sixteen packed scalar words. The
status-returning scalar poll is the SimpleOS boundary; aggregate `poll()` is a
host compatibility wrapper. Pixel content similarly uses packed words plus
parallel handle/offset/size metadata, and closing its owning window compacts
and releases that storage.

The QEMU PS/2 compatibility path retains Shift/Ctrl/Alt as compositor scalars
and decodes only the MVP Set-1 printable/special-key subset. It routes physical
keys before committed text, handles Alt+Tab/F4 and Ctrl+M/Ctrl+Shift+M at the
WM layer, and has no `char_from_code` runtime dependency.

Hosted callbacks and deterministic injection enqueue the same 16-word scalar
event records directly. Aggregate `WindowEventRecord` construction is retained
only as a compatibility facade above that queue.

SimpleOS taskbar pin state is an ordered set of parallel stable `app_id`,
display-name, and icon arrays owned by `DesktopShell`. Pinning is idempotent,
unpinning does not remove running windows, and launcher activation resolves the
display name from the stable ID. The shell loads and saves the bounded,
versioned `/SYS/TASKBAR.PIN` wire format through the shared VFS. Invalid or
duplicate records leave the built-in defaults intact and increment the
diagnostic error count.

## Lifecycle and Taskbar

Open creates content ownership, adds a running item, and focuses. Minimize
hides client content but retains the running entry and pre-minimize state.
The scalar transition owner is `common.ui.wm_window_state`; the compositor
stores both current state and `state_before_minimize`. Maximize stores
`normal_rect`; restoring from Minimized first recovers Normal or Maximized,
while restoring from Maximized copies `normal_rect` exactly. Close moves
through Closing, cancels capture, releases content/event/pixel handles, then
Closed.

Pin/unpin mutates an ordered stable-`app_id` list and immediately requests a
VFS save. A pinned-but-not-running item launches; a running item
restores/focuses its most recent window.

## Audio

The button click allocates deterministic 48-kHz stereo PCM behind a scalar
address, records a bit-level checksum, and submits it through the raw miniaudio
entry when a host device started. The device copies samples before the caller
releases the raw buffer. No Simple PCM array crosses this boundary.

The x86 SimpleOS boot entry now starts the scalar-owned HDA service. It
normalizes BAR0, enables memory/bus mastering, prepares four 4096-byte IOC BDL
periods, selects the first output stream from GCAP, programs 48-kHz stereo
16-bit format, routes PCI INTx through the Q35 I/O APIC, installs the IRQ
handler, then starts RUN. Codec probing consumes the hardware-reported RIRB
response slot rather than assuming slot zero. Live QEMU acceptance requires
initialization plus at least four completed-period IRQs.

## Live Evidence

The GLFW check launches under a real display, injects through the normalized
platform boundary, retains at least one native-input receipt, captures the
staging framebuffer/window, and records semantic state. Stable regions and
content diversity are checked instead of one full-screen hash.

## Deliberate Deferrals

- No SDL or board audio adapter. HDA source wiring exists, but no live-device
  completion claim until the canonical QEMU scenario passes.
- No QEMU/board completion claim.
- No macOS visual parity, animation, blur, accessibility tree, GPU browser,
  multi-monitor, or advanced audio.
- The QRB2210 port is a separate prerequisite feature.
- The fail-closed UNO Q checker targets `qrb2210-uno-q` only; the STM32U585
  board ID is explicitly rejected as a desktop target.
