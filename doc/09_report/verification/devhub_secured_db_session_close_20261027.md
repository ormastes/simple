# Secured Messenger DB: unresolved handoff

The user requested stopping implementation, recording the bug and TODO, landing eligible work, and closing the session. No second fresh acceptance attempt was started.

## Actual acceptance

- Existing pinned phase-2 producer SHA256: `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`. The compiler was not rebuilt.
- Source: commit `42824ac1ec5` plus the frozen cleanup diff whose hashes are recorded in `build/devhub-completion/fresh-secured-ledger1.sdn`.
- Fresh native build exited 0. Artifact SHA256: `35cfd55ba5ba2735fe98386f001d6ebc881e8b27e37df7b41d95ac2ccc2eea7e`.
- Independent in-memory SQLite/AES/KDF/HMAC fixture oracle passed. The encrypted fixture contained nine pages and overflow data.
- Native acceptance exited 1. Byte-provider and geometry checks passed; direct key-session opening returned `Err` before page decryption. Registered storage and Messenger calls were not reached. This run did not reproduce RTS01; it does not prove that older panic fixed.
- Source bytes and metadata remained unchanged. No plaintext, journal, or secret file was created.

The safe typed error code and precise failing sub-boundary remain unknown. Next investigate SecretRef parsing, environment-provider resolution, KDF setup, and checked key cleanup without printing secret values or weakening cleanup checks. Preserve the existing six-cycle limit of the older diagnostic lane; fresh acceptance attempt 1 is complete and has no retry.

## Remaining work

Production secured-DB reading is not verified. The snapshot candidate is unreferenced and native-unverified. Consistent snapshot acquisition, supported journal/WAL behavior, key/schema session reuse, bounded authenticated paging and streaming row traversal require integration and actual acceptance. Full security completion, formal SSpec execution and efficient-query claims remain open.

## Landing limit

Independent DevHub PR #5085 was rejected by automatic self-review admission: `immutable semantic restriction matched current content: credential_secret`. No bypass or repeated admission is authorized. Its other CI failures and producer-provisioning limitations are recorded separately. Commits and branches preserve the handoff; a pushed branch is not a landed fix.

## Resumed goal, 2026-10-30

The user resumed DevHub fixes, real build/test and actual launch with Astra and Luna. The historical stop instruction above describes the October 27 handoff; it does not close the resumed goal. The outstanding key-session failure remains open pending fresh typed diagnostic evidence and production-path acceptance.

GitHub was rechecked on October 30: PR #5085 is MERGED into `release/1.0.0`, merged at `2026-10-28T00:36:53Z`, merge commit `6011ef9fee09b3ab3fc8d9b069442ed948caaba1`. The historical admission rejection is not its current landing state. This merge does not prove the separate secured-database work complete.

The pinned compiler exists and its SHA-256 still matches `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`. Its use remains the explicitly supplied Phase 2 scope in the companion workaround/design documents, not a Stage 4 runtime qualification. The directory name `stage3` is not admission evidence.

Current coordination and acceptance criteria: `.spipe/devhub-release-dev-20261030/state.md`. Exact local/remote `release/dev` is absent; the requested branch-base choice is pending. Source diagnosis proceeds in this isolated worktree without changing the unrelated main workspace.
