# SOSIX Hosted Input Producer Adapter

The hosted event owner pushes already-normalized `HostInputEvent` callbacks
into the canonical bounded SOSIX input stream. The adapter does not poll or
read clocks: its caller supplies the event timestamp.

## Normalized callbacks remain ordered

Given a valid stream, pointer motion, pointer button, wheel, canonical key,
text carried by the key event, and resize callbacks are assigned consecutive
SOSIX sequence numbers and retain the timestamps supplied by the event owner.
The complete typed `HostInputEvent` is retained, including coordinates,
buttons, direction, wheel delta, key text/modifiers, and resize dimensions.

## Stream policy remains canonical

The adapter delegates timestamp validation, bounded admission, and adjacent
pointer-motion coalescing to `input_stream_state`. A rejected or unsupported
callback does not consume a sequence number.

## Payload contract

- Pointer move: `data0=x`, `data1=y`.
- Pointer button: `data0=canonical button`, `data1=1` for down or `0` for up.
- Key: `data0=canonical key code`, `data1=mods * 2 + down`.

These fields are compatibility metadata only. Consumers needing the complete
event use the retained typed `host_event`; no parallel input encoding exists.
