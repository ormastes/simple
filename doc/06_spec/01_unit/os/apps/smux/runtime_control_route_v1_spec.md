# Runtime control route prevention

AUTHORED_UNRUN. This manual corresponds to
`test/01_unit/os/apps/smux/runtime_control_route_v1_spec.spl`; it records no
compiled, native or runtime acceptance result.

- **Reject caller supplied principal roots argv and lease metadata.** Canonical
  requests round trip; extra authority fields and noncanonical base64 are denied.
- **Reject cross-kind payloads overflow revisions and unsupported geometry.**
  Input and Geometry have distinct bounded envelopes and revision limits.
- **Refuse forged authentication before any control request parsing.** The real
  server dispatcher denies the wrong service token first; an unconfigured server
  cannot issue runtime controls even with its legacy token.
- **Correlate refusal replies without promoting metadata to an effect.** The
  actual hosted CLI rejects provider-unavailable effects and altered readiness.
- **Keep bound terminal input and resize guards before native effects.** An
  intentionally invalid process reference tests early refusal only. It is never
  adopted or used as native ownership evidence. Attachment metadata without the
  actual matching admitted attachment also fails snapshot lookup. The actual
  client-size transform changes only attachment dimensions; pane geometry stays
  unchanged and the runtime resize capability guard still refuses effects.

The adjacent owner spec covers pure lease-state semantics. The socket system
spec separately requires real enrollment, native adoption and workload output.
