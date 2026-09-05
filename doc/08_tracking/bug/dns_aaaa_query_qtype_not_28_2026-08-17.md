# DNS AAAA query does not carry QTYPE=28

- Status: OPEN
- Status: CLOSED (2026-08-17)
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

## Resolution (2026-08-17) — CLOSED, the spec was wrong, not the encoder

Root cause: **an off-by-two field read in the spec.** RFC 1035 §4.1.2 orders a
question `QNAME, QTYPE, QCLASS`, so the last two bytes of a query are the
QCLASS, not the QTYPE. The example read `q[last]` / `q[last-1]` and asserted
`28` against the QCLASS **low byte**, which is always `1` (IN). It read back
`1`, and `to_equal` rendered that mismatch as
`expected subject to be truthy, got 0`.

`dns_wire_encode_query` was RFC-correct the whole time, and this file's own
header vector already said so:
`Question: 07 65 78 61 6d 70 6c 65 03 63 6f 6d 00 00 01 00 01` — QTYPE `00 01`
then QCLASS `00 01`, 29 bytes total. The sibling example
`"QCLASS=IN (1) at offset 27–28"` passed throughout and pins the same layout.

Why only AAAA surfaced it: for record type **A**, `DNS_TYPE_A == 1` and
`DNS_CLASS_IN == 1` are the same byte, so an off-by-two read is invisible. It
can only show up for a type whose value differs from 1.

Fix: corrected the assertion to read the QTYPE from `q[last-3]`/`q[last-2]` and
the QCLASS from `q[last-1]`/`q[last]`. No library change.

Reproducing spec (the corrected example, run before and after):
`test/01_unit/lib/nogc_sync_mut/dns/dns_spec.spl`

```
before: Results: 35 total, 34 passed, 1 failed
        ✗ AAAA query has QTYPE=28
after:  Results: 35 total, 35 passed, 0 failed
```

Similar-problem detection spec, generalising to the whole record-type class
rather than AAAA alone — pins the QTYPE offset **and** the IANA value for
A=1, NS=2, CNAME=5, MX=15, TXT=16, AAAA=28, SRV=33, and uses the trailing
QCLASS bytes as an absolute oracle so a reader slid two bytes right cannot
pass:
`test/01_unit/lib/nogc_sync_mut/dns/dns_qtype_encoding_spec.spl`

```
after:  Results: 3 total, 3 passed, 0 failed
```

Commit: `7b85841e0e7`.
