# SCV Non-Functional Requirements

Status: selected requirements, 2026-05-14.

NFR-001: Private snapshot storage must be byte-exact for text and binary files.

NFR-002: Same-size edits must change content identity when bytes differ.

NFR-003: Parser failure must not prevent private snapshot creation.

NFR-004: Metadata updates that move repository heads, workspace pointers, bookmarks, or operation heads must be transactional or recoverable.

NFR-005: Content-addressed object writes should be idempotent.

NFR-006: First-slice commands should avoid unnecessary full-tree rereads once a status index or parser index exists.

NFR-007: Public-ready promotion must be policy-gated by parser/compiler/test state, not by private savepoint creation.

NFR-008: The implementation must keep files under the repo's 800-line maintainability threshold or split them by MDSOC+ responsibility.

NFR-009: The command surface should be usable from `bin/simple run src/app/scv/main.spl ...` before any compiled wrapper exists.

NFR-010: Platform documentation must avoid implying RISC-V-only support.
