# C36 SDN parser payload ownership candidate

Bug: `native_sdn_empty_payload_owner_2026_10_11`, GitHub #2982 (OPEN).
Base source: `f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c`.
Failing producer SHA-256: `5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235`.

The actual `src/app/io/env_access_host.spl` consumer still reports two
`lib.common.sdn.value.SdnValue.Array` and two `SdnValue.Dict` MIR payload
type mismatches after the narrow empty-container workaround in `7324234`.
The previous fixture passing does not establish consumer success.

Retained evidence directory:
`/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-consumer-fixes/consumer-env-access-host`.
Its parser HIR is `ac46daca39e954f89233cef3fc1e200d0be8d8773f7202f60bee64ba942c0a87.hir`.
The HIR preserves parser enum construction spans at original lines 189, 256,
291 and 513, and resolves the owner to `lib.common.sdn.value.SdnValue`.
The MIR errors omit source spans; assigning each error to these sites is a
source-based hypothesis until the affected consumer compiles.

Two parser array constructors pass `sq.0` from
`Result<([SdnValue], i64), text>` directly. Two dictionary constructors consume
locals initialized by unannotated `{}`. The workaround retains the array
element owner in typed aliases and declares both dictionaries as
`Dict<text, SdnValue>`. It preserves the exact values, writes, ordering, offsets,
and parse branches; it adds no synthetic element, cast or fabricated container.
Each affected block carries the canonical workaround marker.

`test/fixtures/compiler/sdn_parser_payload_workaround/main.spl` exercises the
real parser: empty/nonempty inline dictionary, block dictionary, top-level
sequence, and nested sequence. Checks inspect enum tags, sizes, keys and integer
payloads. Compile-only success must be reported separately from running these
checks.

Independent landing review: source-only PASS, no introduced P0/P1 findings;
the four source sites remain unproven as individual failing sites. No native
build or execution ran in this lane because the manual build owner imposed a
disk-floor hold. Queue the real `env_access_host.spl` affected-source object
with the same C36 producer, `SIMPLE_NO_STUB_FALLBACK=1`, and monitor-only RSS
collection after integrating this source candidate and the separate callback
fix. Require the SDN errors to disappear; keep #2982 OPEN regardless of the
local workaround result until the compiler ownership defect is fixed.
