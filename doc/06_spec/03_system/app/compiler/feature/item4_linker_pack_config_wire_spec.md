# Linker native configuration wire V2

Authored companion to `item4_linker_pack_config_wire_spec.spl`; ITEM4-REQ-010.
**UNRUN**, not generated runner evidence. No observed RED/GREEN or successful
native provider execution is claimed.

| Scenario | Observable contract |
|---|---|
| Fifteen-field preservation | Nondefault scalar/boolean/array expectations separately cover every NativeLinkConfig field, literal whitespace/newline/Unicode, empty array elements, inputs and selected request/policy fields |
| Malformed/truncated envelope | Every boolean slot rejects noncanonical values; every count slot rejects signed/leading-zero/overflow values; every strict prefix and trailing argument rejects |
| Version/NUL/oversize | Outer and nested unknown protocols, every config string category containing NUL, too many arguments and excessive byte arena reject; encoder rejects NUL too |
| V1 compatibility | Original V1 round trip remains valid; version decoders reject mismatched envelopes |
| Exact limits | 4096 arguments and a complete 1 MiB arena admit; one additional argument or byte rejects |
| Provider dispatch | Real command/adapter returns InputError for mismatching explicit config; correcting config identity reaches UnsupportedBudget, proving the V2 handler did not discard it |

The last scenario requires an uncontested target environment and uses the native
host target. It does not read fake fixture files or claim successful image output.
Positive actual-link lifecycle/CLI scenarios remain specified separately in
`linker_provider_positive_acceptance_2026-10-04.md` and are not replaced here.
