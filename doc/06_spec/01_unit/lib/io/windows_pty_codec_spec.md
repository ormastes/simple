# Windows ConPTY wire values

Source: `test/01_unit/lib/io/windows_pty_codec_spec.spl`.
This is an authored manual, not generated execution evidence. Status: pending.

| Scenario | Asserted observation |
|---|---|
| COORD packing | 24 rows by 80 columns equals 1572944 |
| Geometry bounds | Zero, negative, SHORT overflow and excessive area are rejected |
| ASCII/control bytes | Embedded NUL, ESC, CR and LF survive unchanged |
| Split three-byte scalar | Lead octet retained, then decoded to 한 |
| Split four-byte scalar | Three reads produce 😀B with no trailing bytes |
| Empty poll | An incomplete scalar remains buffered |
| EOF | A truncated scalar becomes replacement text and clears tail |
| Invalid UTF8 | Overlong and surrogate encodings never become malformed text |

These pure value checks do not prove Win64 ABI correctness, pipe ownership,
child execution, resize notification, or cancellation. Those require the real
native `windows_pty_owner` fixture and product SSpecs on the current Windows host.
