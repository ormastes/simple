# Baremetal enum RecordResult destructuring corrupts fields

Date: 2026-05-30
Status: Open
Severity: High

## Symptom

In the x86_64 freestanding TLS unit image, `RecordResult.Ok(content_type: i64, data: [u8])`
from `record13_decrypt(...)` matches the `Ok` variant but destructured fields
are corrupted. During the TLS live repair, D4 observed `content_type == 0` and
a garbage `data.len()` even though the same record decrypted successfully via
`rt_tls13_record_decrypt_compact(...)`.

## Evidence

- A clean QEMU run of `examples/simple_os/arch/x86_64/tls_unit_entry.spl`
  showed pure record encryption and compact decrypt succeeding for D3, D4, D9,
  and D10.
- The failure only appeared when destructuring
  `if val RecordResult.Ok(ct, data) = record13_decrypt(...)`.

## Expected

Enum variant destructuring in freestanding native code must preserve all fields
with their declared types and values, including mixed scalar plus heap-reference
payloads.

## Next Probe

Add a minimal freestanding/native regression with an enum shaped like:

```simple
enum E:
    Ok(code: i64, data: [u8])
    Err(msg: text)
```

Construct `E.Ok(0x16, [0x48u8])`, destructure it, and assert `code == 0x16`
and `data.len() == 1`.
