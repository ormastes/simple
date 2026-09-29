# Native SVIM Toolingd Cutover

The native editor keeps buffer text and edit history as its sole editing authority while the shared toolingd/KPF session owns versioned analysis requests.

Acceptance evidence:

- diagnostics and code actions derive from one normalized analysis publication;
- publishing diagnostics never mutates buffer text;
- a newer snapshot cancels the superseded analysis ticket;
- stale publications are rejected;
- exact test operations reuse the shared analysis ticket;
- syntax-only fallback is explicitly labeled degraded and never claims semantic authority.
- native publications expose the same `kpf-result-v1` canonical result identity carried by the VS Code projection;
- closing one document cancels and removes its edge-owned ticket;
- disconnecting cancels and removes all remaining edge-owned tickets and leaves SVIM explicitly unavailable.

Mutation sensitivity is explicit: the native test asserts the complete canonical
identity and embedded LSP field, while the VS Code host test rejects a batch
whose identity prefix is mutated away from `kpf-result-v1`.
