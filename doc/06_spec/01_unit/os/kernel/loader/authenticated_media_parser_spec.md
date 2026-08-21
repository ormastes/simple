# Authenticated Media Parser Architecture Parity

Source: `test/01_unit/os/kernel/loader/authenticated_media_parser_spec.spl`

Evidence class: `host-fixture`.

## Scenarios

- Decode the same unsigned admission fields identically for RV64 and x86_64
  records.
- Reject absent, duplicate, empty, malformed, and invalidly named fields, plus
  negative unsigned integers.
- Decode canonical lowercase signature hex and reject odd-length, uppercase,
  and non-hex input.

The fixture exercises the shared production parser. It does not verify a
signature, authenticate media, or boot either architecture.

