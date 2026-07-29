# SimpleOS remote windows dropped committed text

- **Status:** fixed in protocol and PS/2 routing; live QEMU evidence pending
- **Affected path:** compositor input → desktop shell → WM service → WindowClient

## Root cause

The compositor consumed PS/2 characters directly into local GUI sessions.
Only pointer events crossed the shell-owned WM IPC path, so remote application
windows could not receive text.

## Fix

`WmEventType.Text` is appended without renumbering existing event kinds.
`WmInputEvent` carries committed text separately from physical keys. The IPC
record preserves its existing scalar prefix and appends
`text_len(u32) | UTF-8 bytes`, bounded to 4096 bytes. The client rejects
truncated, oversized, or non-round-tripping UTF-8.

The freestanding compositor stores only window ID, scancode, and modifier
scalars; the shell reconstructs and sends the physical key before committed
text. PS/2 polling returns after one routable key, leaving the rest in the
hardware FIFO so the scalar pending slot cannot overwrite a burst. This avoids
aggregate-return and text-in-aggregate boundaries known to fail in current
Phase 3. Backspace, Tab, Enter, and Escape use their conventional scalar key
codes so their identity survives the IPC record even though committed text
remains separate.

## Evidence

The pure-Simple Stage-2 compiler built the focused native probe with three
source objects and no failures; the binary exited `0`. A first modifier helper
returned an aggregate and crashed with a nil receiver, so the final wire path
uses scalar inline bit packing instead.

Live QEMU event injection and application receipt remain required runtime
evidence.
