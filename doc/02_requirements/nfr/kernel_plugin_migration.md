<!-- codex-research -->
# Kernel/Plugin Migration NFRs

Status: FINAL. Qualification uses the selected policy in
`doc/04_architecture/compiler/plugin_arch/kernel_closure.sdn`.

- **KPM-NFR-001 — Startup.** Plugin metadata and negotiation shall add less than
  2 ms to the current measured CLI startup baseline; resident facet lookup shall
  add no I/O, hashing, or subprocess work.
- **KPM-NFR-002 — Hot path.** Registration/negotiation occurs at startup, load,
  or once per compile, never once per AST/HIR/MIR node.
- **KPM-NFR-003 — Compatibility.** Major/digest/schema mismatch fails closed;
  an explicitly accepted older minor remains loadable and unknown extensions
  are skipped only where the contract permits it.
- **KPM-NFR-004 — Bootstrap continuity.** Every phase shall keep the selected K1
  bootstrap backend set self-hosting and shall not substitute the Rust seed for
  native qualification.
- **KPM-NFR-005 — Observability.** Receipts expose stable result/reason codes,
  negotiated identities, provider digest, link mode, timing, and cache impact.
- **KPM-NFR-006 — Test integrity.** Planned SPipe checks use real assertions,
  mutation-red fixtures, canonical matchers, and explicit fail-fast placeholders
  until helpers are implemented.
