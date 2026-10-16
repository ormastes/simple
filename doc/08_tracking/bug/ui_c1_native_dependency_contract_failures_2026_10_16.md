# UI C1 native dependency contract failures

Status: isolated source repair in progress; no native PASS or deployment.
Authoritative bug database reconciliation is pending a qualified full CLI.

The UI build from frozen C1 with producer SHA256
`0cd6d7c598f20af768774d68bc434f6a0b6660f6194a2e34e7eff48946e1aa9b`
failed HIR. The second diagnostic retained 133 capped per-source diagnostics
covering all 33 failed source paths. The compiler reported 262 errors; not all
messages were emitted. Actual reuse was 973 frontend hits and 940 HIR hits.

Confirmed repairs prepared in this isolated branch:

- Recover the three login-grant/security-header functions deleted by
  `88aac2ffe286e111f929a72f5532b9d74ed0b9a1`, retaining their exact parent
  bodies and the genuine constant-time comparison owner. A small shared leaf
  supplies the original auth and HTML public surfaces.
- Extract existing CLI observer entry implementations into `ui.cli/entry.spl`.
  Both directory and slash facades import this unambiguous leaf. Preserve the
  original `CLIObserver` declaration and existing caller-facing run functions.
- Restore missing imports from existing exported HTTP-core, crypto-byte,
  theme, Skia-color, string, and JS-runtime owners. No visibility changes or
  substitute implementations are used for these imports.
- Track the narrow Unit/Nil annotation compatibility repair in
  `ui_c1_unit_nil_type_aliases_native_2026_10_16.md`.

Source repairs for all 33 diagnostic-source groups are complete and reviewed. Mutable NVMe/VFS state remains with its actual owners; no copied mutable global or broad private export was introduced. Native verification remains UNRUN. The capped preview retained 133 messages from 262 underlying errors, so source readiness does not prove every hidden diagnostic resolved.

Runtime and SDK materialization match frozen C1. The original C1 checkout and
both UI diagnostic caches remain untouched by source edits. Final cycle 3 is
held until the complete repair diff and evidence plan receive root review.
