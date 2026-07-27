# In-Tree Counterpart Rule (research-stage process rule)

## Role

Own one reusable research rule: **before recording an "external port" or
"blocked on a third-party library" row, search the host repository for a
pure-in-language counterpart that already exists.**

This is a research-stage rule. It belongs to whoever writes
`doc/01_research/local/<feature>.md` and to whoever maintains a blocked-row
ledger.

## Why it exists

On 2026-07-27 three long-standing blockers in the host repository were found to
be stale in a single session, each because a working in-tree implementation
existed and nobody had looked:

| Blocker as written | What was actually in the tree |
|---|---|
| "real signature verification blocked on a crypto stack" | 25-file / 12,183-line crypto library with zero stub markers, plus a second 46,404-line tree; Ed25519 passing its RFC 8032 known-answer vectors (15 examples, 0 failures); 60 crypto spec files |
| "OpenSSH port (multi-week)" | 9,576 lines of pure-in-language SSH **server**, wired to real crypto and a real socket facade, advertising curve25519-sha256 / ssh-ed25519 / chacha20-poly1305 / aes-gcm / hmac-sha2. Only the **client** was a foreign-library wrapper |
| "SQLite blocked on a C toolchain" | A ~4,440-line pure-in-language SQL engine with DDL, DML, `WHERE`, and transactions. The C dependency was only in the FFI wrapper |

The common shape: **the blocker names the foreign-linked wrapper, not the
capability.** Everyone downstream then reads it as the capability.

## Procedure

1. Grep `src/**` for the capability noun *and* its common synonyms before
   trusting any blocked row (`sqlite` → also `sql`, `database`, `pure_sql`;
   `openssh` → also `ssh`, `sshd`, `kex`; `crypto` → also the primitive names).
2. Measure what you find: file count, line count, and **stub-marker count**
   (`TODO`, `unimplemented`, `not implemented`). A large tree with zero stub
   markers is a strong signal of real work.
3. **Run its specs.** Present is not proven. Record per-block verdicts.
4. Separate the capability from its foreign-linked wrapper, and rewrite the
   blocked row to name only the part that is genuinely blocked.
5. Watch for **tier shadowing**: if the language resolves a module family in a
   fixed order, an in-tree copy may be unreachable. Confirm which copy executes
   before editing or deleting either.

## Output

- Correct the blocked row in the tracking ledger.
- Add or update the host-repository counterpart map so the next session does not
  re-derive this. In this host that map is
  `doc/07_guide/lib/database/sqlite_counterparts.md` plus the *In-Tree
  Counterpart Rule* section of `doc/glossary.md`.

## Constraints

- Do not delete the foreign wrapper just because a native counterpart exists —
  it may be the faster or better-tested path on the host platform. Record which
  is canonical for which target.
- Do not mark a row unblocked on the strength of file size alone. A passing
  known-answer test or spec run is the minimum evidence.
