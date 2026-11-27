# Literal byte queues and explicit paste

REQ-CMUX-003/008; NFR-CMUX-005/007. **AUTHORED / NOT_RUN: twelve cases, zero executed.** Manual mirror from source; canonical docgen and maintenance scan are pending.

Source: `test/01_unit/os/apps/smux/literal_input_spec.spl`.

| Scenario | Real production oracle |
| --- | --- |
| Arbitrary octets | NUL, 0x80, 0xff and malformed UTF8 remain exact array elements. |
| Mixed stream | Unicode text, literal bytes and a terminal query reply retain byte order; the queue cannot return to a text-pipe carrier. |
| Short progress | Accepted byte prefixes advance without scalar decoding; zero progress preserves offset and complete drain resets the transport marker. |
| Flush bound | Only 4096 bytes are exposed; a greater advance refuses. |
| Retained capacity | Consumed prefix still counts toward 65536 retained bytes until complete drain. |
| Errors | Sticky failure retains bytes/transport marker; invalid offset and negative progress refuse. |
| Empty enqueue | No transport switch, byte loss or fabricated progress. |
| Paste flags | All four bracketed/append-enter combinations have explicit expected byte arrays, including raw NUL/0x80/0xff. |
| Paste overhead | Complete marker/body/CR fits exactly or refuses before queue mutation. |
| Budget bounds | Negative, too-small and over-service budgets refuse without truncation. |
| Ownership | Production pure admission validates ancestry, closing state and explicit installed mechanism support. |
| No fallback | Piped, missing and deferred-close children refuse the literal path. |

`literal_input_setup` creates synthetic records only for the pure admission function. No synthetic PID/fd reaches any native effect. Queue equality proves queue semantics, not actual WriteFile bytes or child input effects. The generic Sys negative implementation and Windows provider require their own admitted execution profiles; the boolean admission case is not mocked native qualification. No placeholders or skip-as-pass branches are authored.
