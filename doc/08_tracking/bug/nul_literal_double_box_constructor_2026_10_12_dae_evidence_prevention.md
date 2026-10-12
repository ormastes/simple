# Native prevention evidence and remaining authored input

Four actual first-run source inputs below passed 21 checks under facet9fd/C47/935. Their receipt/source hashes are in the evidence JSON. The separate empty input remains UNEXECUTED; the original seven-check fixture covers empty text. These results do not qualify core/backend specs or full Redis.

## unicode_nul — native PASS, 5 checks

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

## nul_edges — native PASS, 4 checks

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

## nul_only — native PASS, 2 checks

```simple
@unsafe(reason: "observe exact literal bytes through the actual counted runtime owner", capabilities: [ffi])
extern fn rt_text_to_bytes(value: text) -> [u8]

fn main() -> i64:
    val bytes = unsafe(capabilities: [ffi]):
        rt_text_to_bytes("\0")
    if bytes.len() != 1: return 1
    if bytes[0] != 0: return 2
    0
```

## plain_utf8 — native PASS, 10 checks

```simple
@unsafe(reason: "observe exact literal bytes through the actual counted runtime owner", capabilities: [ffi])
extern fn rt_text_to_bytes(value: text) -> [u8]

fn main() -> i64:
    val bytes = unsafe(capabilities: [ffi]):
        rt_text_to_bytes("é雪🙂")
    if bytes.len() != 9: return 1
    if bytes[0] != 195: return 2
    if bytes[1] != 169: return 3
    if bytes[2] != 233: return 4
    if bytes[3] != 155: return 5
    if bytes[4] != 170: return 6
    if bytes[5] != 240: return 7
    if bytes[6] != 159: return 8
    if bytes[7] != 153: return 9
    if bytes[8] != 130: return 10
    0
```

## Standalone empty — UNEXECUTED

```simple
@unsafe(reason: "observe counted native literal bytes through the actual runtime owner", capabilities: [ffi])
extern fn rt_text_to_bytes(value: text) -> [u8]

fn main() -> i64:
    val bytes = unsafe(capabilities: [ffi]):
        rt_text_to_bytes("")
    if bytes.len() != 0: return 1
    0
```
