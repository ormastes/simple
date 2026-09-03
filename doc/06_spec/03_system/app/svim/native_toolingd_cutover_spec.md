# Native SVIM Toolingd Cutover

The native editor keeps buffer text and edit history as its sole editing authority while the shared toolingd/KPF session owns versioned analysis requests.

Acceptance evidence:

- diagnostics and code actions derive from one normalized analysis publication;
- publishing diagnostics never mutates buffer text;
- a newer snapshot cancels the superseded analysis ticket;
- stale publications are rejected;
- exact test operations reuse the shared analysis ticket;
- syntax-only fallback is explicitly labeled degraded and never claims semantic authority.
