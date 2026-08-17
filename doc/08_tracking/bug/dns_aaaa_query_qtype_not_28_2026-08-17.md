# DNS AAAA query does not carry QTYPE=28

- Status: OPEN
- Found: 2026-08-17, `test/01_unit/lib/` sweep
- Severity: MEDIUM — AAAA (IPv6) lookups are affected

## Symptom

```
✗ AAAA query has QTYPE=28
  expected subject to be truthy, got 0
```
`test/01_unit/lib/nogc_sync_mut/dns/dns_spec.spl`
→ `Results: 35 total, 34 passed, 1 failed` (rc=1)

## Why it is only visible now

This failure was **masked**. Before `3d56c94653e`, `dns_spec.spl` reported
`(30 passed, 5 failed)`, where 3 of the failures were
`semantic: function char_from_code not found` coming from a phantom
`use string.{char_from_code}` import in `src/lib/nogc_sync_mut/dns/wire.spl`.
Fixing that import took the spec to 34 passed / 1 failed and left this one
genuine, pre-existing defect exposed.

It is NOT a regression from that change: the fix only repointed a name-resolution
import to `char_from_codepoint`, and it touched the label/TXT rdata *decode*
path, whereas this failure is in AAAA *query* construction (QTYPE encoding).

## Next step

Check that the AAAA query builder writes `DNS_TYPE_AAAA` (28) into the QTYPE
field. `DNS_TYPE_AAAA` is already declared in
`src/lib/nogc_sync_mut/dns/types.spl` and imported by `wire.spl`; the assertion
reading `0` suggests the field is left unset or the accessor returns the wrong
offset.

Spec left RED deliberately per `.claude/rules/testing.md` — do not skip it.
