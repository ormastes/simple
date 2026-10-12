# Authored prevention inputs

All inputs UNEXECUTED. Preserve source length and exact bytes; source-only proposal, not platform qualification.

## empty

```simple
@unsafe(reason: "observe counted native literal bytes through the actual runtime owner", capabilities: [ffi])
extern fn rt_text_to_bytes(value: text) -> [u8]

fn main() -> i64:
    val bytes = unsafe(capabilities: [ffi]):
        rt_text_to_bytes("")
    if bytes.len() != 0: return 1
    0
```

## unicode_nul

```simple
@unsafe(reason: "observe counted native literal bytes through the actual runtime owner", capabilities: [ffi])
extern fn rt_text_to_bytes(value: text) -> [u8]

fn main() -> i64:
    val bytes = unsafe(capabilities: [ffi]):
        rt_text_to_bytes("é\0Z")
    if bytes.len() != 4: return 1
    if bytes[0] != 195: return 2
    if bytes[1] != 169: return 3
    if bytes[2] != 0: return 4
    if bytes[3] != 90: return 5
    0
```

## nul_edges

```simple
@unsafe(reason: "observe counted native literal bytes through the actual runtime owner", capabilities: [ffi])
extern fn rt_text_to_bytes(value: text) -> [u8]

fn main() -> i64:
    val bytes = unsafe(capabilities: [ffi]):
        rt_text_to_bytes("\0A\0")
    if bytes.len() != 3: return 1
    if bytes[0] != 0: return 2
    if bytes[1] != 65: return 3
    if bytes[2] != 0: return 4
    0
```
