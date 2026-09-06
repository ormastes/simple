# Caret external receipt semantic authenticity gap

Status: open. The five external Caret must-check rows remain `TODO` and generic
signed receipts are deliberately rejected until lane-specific validators land.

`check-external-must-check-receipt.shs` previously accepted a trusted signature
over four generic blobs and exact `acceptance.*=PASS` labels for local Slang,
installed providers, runtime primitives, production multi-manager, and smux.
That proves reviewer identity and blob integrity, not provider generation,
process reaping, concurrent supervision, or real PTY ownership. Provisioning a
trusted key would therefore have enabled semantic fabrication. The importer now
fails these gates closed after signature authentication and before generic
attachments can promote a row.

## Required versioned validators

All new contracts must retain clean-HEAD producer/checker snapshots, exact
source fingerprint, target/toolchain identity, monotonic events, and an unsigned
reviewer-ready manifest. Authenticate the signature before loading or executing
evidence attachments.

- Installed providers: executable path/hash/version, provider-distinct argv,
  nonce prompt/parsed response, deadline, PID-start identity, waited exit,
  process-group/descendant census, and redacted leak scan. Echo fixtures prove
  wrapper structure only.
- Runtime primitives: distinct cancel and stop plus
  launch→running→cancel/stop→waited-exit, PID anti-reuse, escalation,
  PGID ownership, descendants before/after, and zero survivors.
- Multi-manager: all provider children concurrently live across timestamped
  polls under one parent, followed by waited/reaped children and descendants.
- smux: one real session/pane/PTY per Caret child, nonce capture, observed
  resize, cancel/stop/wait/close, and zero PID/fd survivors. Display-only
  `AgentTmuxEmbed` and in-memory `smux/api.spl` rows are not PTY evidence.
- Local Slang: first implement a production generation endpoint and Caret
  provider. Loader/readiness and `local_torch` cannot substitute. Then retain
  artifact/provider identity, readiness, nonce generation, timeout, waited
  stop, descendants, and leak-free cleanup.

The automated wrapper, messaging, and batch-adapter rows remain separate
bootstrap checks and must never promote these production rows.

