# Bug — `STUN_ATTR_SOFTWARE` constant uses wrong type code (0x802b vs RFC 0x8022)

**Filed:** 2026-05-03 (W29-L STUN KAT spec, RFC 5769 §2 vector work)
**Severity:** Medium — SOFTWARE attributes in RFC 5769 §2.1/§2.2/§2.3 vectors parse as
`Unknown(type_code: 0x8022, value: ...)` instead of `Software(value: ...)`. Emit also
writes 0x802b on the wire instead of 0x8022, breaking interoperability.

## Symptom

```spl
# In src/os/proxy/stun.spl line 52:
val STUN_ATTR_SOFTWARE: i64 = 0x802b   # BUG — RFC 5389 §18.2 assigns 0x8022
```

RFC 5769 §2.1 Sample Request wire bytes show SOFTWARE header as `80 22 00 10`.
RFC 5769 §2.2 and §2.3 Sample Responses show `80 22 00 0b`.
All three vectors produce `Unknown(0x8022, ...)` from `stun_parse`, not `Software(...)`.

## Root Cause

`STUN_ATTR_SOFTWARE` is initialised to `0x802b` in `src/os/proxy/stun.spl`.
IANA STUN attribute registry and RFC 5389 §18.2 assign **0x8022** to SOFTWARE.
0x802b has no assigned meaning in the standard.

## Impact

- `stun_parse` on any real STUN packet (e.g., from Google TURN servers, Coturn)
  returns `StunAttr.Unknown(0x8022, ...)` instead of `StunAttr.Software(...)`.
- `stun_build` with a `Software(value)` attr writes type code 0x802b on the wire,
  which peers will ignore or treat as unknown.
- RFC 5769 §2.1/§2.2/§2.3 KAT round-trips cannot assert `Software(...)` equality.

## Fix

```spl
# src/os/proxy/stun.spl line 52 — change:
val STUN_ATTR_SOFTWARE: i64 = 0x802b
# to:
val STUN_ATTR_SOFTWARE: i64 = 0x8022
```

Single-line fix; no logic changes needed. After fix, re-run RFC 5769 §2 KAT spec.

## References

- RFC 5389 §18.2 STUN Attributes table — SOFTWARE = 0x8022
- IANA STUN Attributes registry: https://www.iana.org/assignments/stun-parameters/
- RFC 5769 §2.1 wire bytes: `80 22 00 10 53 54 55 4e 20 74 65 73 74 20 63 6c 69 65 6e 74`
