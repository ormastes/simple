# Optional macOS HTML GUI event lifecycle

Status: draft; stacked on #1417. This is separate from the compositor Cocoa
provider in #1402. No production WebKit provider is currently supplied by #1417.

## Problem and selected scope

Both `app/editor/gui_shell.spl` and `gui_shell_render.spl` return an empty event
unconditionally. Installing the HTML presentation dylib therefore cannot make
the editor receive input or leave its run loop. Neither HTML run loop tears
down the provider's window.

The requested smallest change extends the existing lazy HTML provider with a
separately versioned event/session capability, a canonical Simple SFFI owner,
and both caller paths. No AppKit/WebKit symbols enter the core executable.
The compositor provider's image/pixel/event-type ABI remains independent.

## Requirements

- REQ-001: Headless execution performs no GUI library loading; session open
  resolves the configured absolute HTML provider path once per process.
- REQ-002: Before presenting an editor frame, require the complete event ABI.
  A presentation-only library fails explicitly rather than creating an
  unusable editor window.
- REQ-003: Poll returns one complete copied `kind\npayload` UTF-8 packet, or
  empty text for an idle timeout. Event kind is 1–31 lowercase ASCII/hyphen
  bytes; total packet size is at most 4096 bytes. Payload can contain newlines.
- REQ-004: A close event stops the existing editor loop and calls provider
  shutdown exactly once. A session can subsequently reopen.
- REQ-005: Session open/present/poll/shutdown run on macOS's main thread.
  Nested sessions, callback reentry, out-of-session calls, malformed packets,
  and provider failures fail closed with the existing GUI exit status 70.

## ABI and ownership

Keep HTML ABI v1 unchanged. The same dylib additionally exports
`simple_gui_event_provider_abi_v1() -> i64` (must return 1),
`simple_gui_poll_event_v1(bytes, capacity, wait_ms) -> i64`, and
`simple_gui_shutdown_v1() -> i64` (1 = success).

Poll receives a caller-owned 4096-byte stack buffer valid only during the call;
it must not retain that pointer. Return 0 for idle, -1 for failure, or the exact
positive packet byte count. No NUL terminator is required. Invalid lengths,
embedded NUL, invalid UTF-8, and malformed kinds are rejected before Simple
receives the packet. The runtime copies accepted bytes into registered Simple
text; no foreign allocation or Objective-C pointer crosses the boundary.

One main-thread session owns provider UI state. An atomic admission gate counts
in-flight standalone HTML calls or reserves one exclusive session. Overlap in
either direction fails before provider work; the gate stays reserved through
shutdown. Standalone HTML v1 calls may remain concurrent with each other.
Provider callbacks must not reenter
runtime GUI entrypoints. Shutdown removes observers/callbacks, closes owned
windows, and releases their state before success. The dylib remains loaded for
process lifetime, avoiding unload races with AppKit/WebKit deferred work.

## Bounds and performance

Symbol resolution occurs only on first GUI/session use; negative admission
terminates rather than rescanning or sleeping/retrying. Warm polling has no
filesystem access, process spawn, symbol lookup, or library load. One packet
is copied per poll; idle uses a cached empty string. Providers receive a 16 ms
wait budget and must wait for input or its expiry when idle, while pumping the
main run loop. They must bound queued events and must not drop a close request
under pressure. These provider bounds require live-provider verification;
an in-process ABI cannot preempt a misbehaving provider callback.
The existing caller renders before every poll, including idle polls; this
change does not claim redraw-on-change or measured low idle CPU.

## Focused evidence plan

Use a tiny dlopen fixture, not a full bootstrap. Verify lazy resolution counts,
text with embedded newline, key/focus/pointer/resize/close delivery, idle,
reopen, exactly-once shutdown, missing symbols, wrong event version, invalid
length/framing/UTF-8, rejection, reentry, and worker-thread refusal. Retain a
baseline missing-symbol/link failure proving the session boundary is absent.
Simple specs exercise packet splitting independently of platform loading.

No live editor, WebKit rendering, IME, accessibility, or shutdown claim follows
from a fixture. Those require the eventual production provider and a coherent
source-matched Simple CLI. Full bootstrap and broad compiler checks are outside
this draft lane; parent owns those gates.

## Coordination and review

Merge owner: this isolated event lane. Dependency: #1417 HTML ABI. #1402 remains
the separate hosted compositor provider. Lower-model sidecars: N/A. Required
final reviewer: Astra source/design review before accepting the implementation.
