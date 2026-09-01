<!-- codex-design -->

# Lazy system path variable test plan

- REQ-LSPV-001/005: known tokens, escaped braces, malformed/unknown tokens, Windows drive and UNC normalization.
- REQ-LSPV-002/NFR-LSPV-001: construct without invoking the injected resolver; resolve exactly once on first access.
- REQ-LSPV-003/004: application, Simple-wide, OS-standard and fallback precedence matrices.
- REQ-LSPV-006: mutate injected inputs after first resolution and retain the memoized result.
- REQ-LSPV-007: raw constructor preserves template tokens; ordinary raw string semantics remain unchanged.
- REQ-LSPV-008/009: RED compiler parity cases for `_path`, contextual `Path`, interpreter and native lowering until Phase B/C land.
- REQ-LSPV-010: Windows file/process boundary conversion covers `C:/`, `/c/`,
  and `c/`; Linux/macOS/BSD preserve `/`.
