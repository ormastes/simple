# HTTP/2 codec loses every octet >= 0x80: frames of 128+ octets and the default window decode as 0 (2026-11-14)

Status: OPEN. Severity: high for the HTTP/2 client (`browser_engine/net/h2_*`).

## Defect

`net/h2_frame.spl` carries wire octets in `text`. `_byte_to_char` (line 398)
maps 0..127 exactly, has literals for 128/252/254/255 and returns U+FFFD for
the rest; `decode_byte` (line 309) reads one unit with
`data.substring(pos, pos + 1)`, a byte offset, so a two-byte character is cut
in half and `_char_to_byte` answers 0. No octet 128..255 round-trips.

## Repro (seed built 2026-11-14, interpreter; run from a `test/` path)

```
val wire = encode_frame(H2Frame.create(H2FrameType.Data, 0, 1, <200 x "x">))
decode_byte(wire, 2)                                      # length low octet
decode_frame(wire).unwrap().length
decode_uint32(encode_settings(default_settings()), 20)    # SETTINGS_INITIAL_WINDOW_SIZE
decode_uint32(encode_window_update(1000), 0)
```

| expression | expected | actual |
|---|---:|---:|
| octets 0..255 through `encode_byte` / `decode_byte`, count wrong | 0 | 128 |
| length octet of a 200-octet DATA frame | 200 | 0 |
| decoded frame length / payload | 200 / 200 x "x" | 0 / "" |
| default initial window in the SETTINGS payload | 65535 | 0 |
| WINDOW_UPDATE increment 1000 | 1000 | 768 |
| `apply_remote_settings(.., INITIAL_WINDOW_SIZE = 40000)` | 40000 | 0 |

So a response DATA frame whose length has a high octet (e.g. 128..255, or any
length with 0x80..0xFF in one of its three octets) is read as shorter or empty,
and the client advertises a zero flow-control window.

## Why it is not fixed here

Switching `_byte_to_char` to `char_from_code` for 128..255 (what
`net/ws_utils.spl` does) is not enough: `decode_byte`, `decode_frame` and
`h2_hpack.decode_header_block` slice by byte offset while lengths are counted
in characters. The carrier has to become a byte array (or every index has to
move to character units, as `ws_utils.ws_substring` does) across
`h2_frame`, `h2_settings`, `h2_hpack`, `h2_stream` and `h2_client` together.
Tried and reverted in this branch: the one-line encode change leaves all six
rows above unchanged.

## Evidence

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/h2_settings_and_header_block_spec.spl`
and `h2_frame_codec_spec.spl` cover the codec for octets below 0x80 only.
