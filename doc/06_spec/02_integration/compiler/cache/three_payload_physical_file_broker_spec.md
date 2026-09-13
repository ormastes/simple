# Three-payload physical-file broker — incomplete draft

- Executable: `test/02_integration/compiler/cache/three_payload_physical_file_broker_spec.spl`
- Requirements: `REQ-CSM-006`, `REQ-CSM-017`, `REQ-CSM-027`, `NFR-CSM-010`
- Evidence class: executable SSpec definition; no execution receipt is embedded.

The inactive broker reads exactly `module.spl` and effective `__init__.tld` for
a cold candidate payload, adding only the matching prior `module.tld` for warm input.
RR and external input requests are refused. Catalog and generation-pin counts
are represented only by a separate untrusted diagnostic observation and never
added to the semantic payload count. They cannot authorize eligibility.

## Scenario inventory

- cold-two and warm-three bounded facade reads;
- diagnostic separation of payload and control counts;
- embedded macro and symbolic trait/aspect reference accounting; and
- RR, external, role-confused, and over-budget refusal.

Frozen visible flow: pin one coherent generation; apply one scoped semantic
mutation; recompute the authenticated affected closure; publish or refuse one
coherent generation; verify exact reuse and confined consumer IO. This draft
covers only diagnostic physical payload confinement.

The control observation is shape-checked, not minted, by this module. Ordinary compiler
activation remains false until the live catalog/pin source owner, identity/alias
proof, and admitted self-hosted execution are available.

This is an incomplete hand-authored draft, not generated-manual qualification.
