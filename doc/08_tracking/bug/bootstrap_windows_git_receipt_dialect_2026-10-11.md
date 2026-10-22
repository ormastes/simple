# Windows preflight and Stage3 Git receipt dialect mismatch

REQ-BOOTSTRAP-GIT-DIALECT: preflight must retain validated materialized-link
authority when executing in the hermetic Windows environment. Descriptor
verification must accept strictly validated Windows alias evidence as well as
the legacy two-row Git receipt, while preserving exact before/after comparison.

The observed old bootstrap at `0e0287094ba` reused the preflight Git capture
verbatim (SHA256 `1881f50058e8f69b00eb069ff0d9be97874087013d31b54f5c6930bb359bcad9`).
That capture contained only head and dirty fingerprint. Its postcapture had
the same head but a different fingerprint and sixteen alias-collapse records.
`run_rust_authority_env` used `env -i` without forwarding the materialization
receipt, selecting the plain capture implementation during preflight. The
parent retained that authority and selected the Windows capture afterward.
The two dialects cannot compare byte-identically. Independently, descriptor
verification required exactly two rows and rejected valid Windows receipts.
The affected source was unchanged in frozen candidate `ae2b2f13f792`.

Only the Windows preflight command now forwards the materialization receipt;
the existing native consumer still validates that receipt. The descriptor
schema checker accepts either exact legacy rows or count/hash-bound alias rows,
with bounded reads, canonical numeric/hex fields, UTF-8 byte lengths, canonical
relative Windows paths, strict byte order and exact duplicate rejection. It
uses Perl, already pinned in tool authority on every host; no unconditional
Python dependency is added. Native receipt validation retains ownership of
Windows case-insensitive identity; schema validation does not case-fold valid
distinct Unicode aliases such as `ss` and `ß`. It does not
normalize receipts or replace their captured fingerprints. Original hash
binding and raw before/after comparisons remain unchanged.

Validation: the final focused `bootstrap_git_state_dialect_test.shs` passed
under WSL after the reviewed Perl/tool-binding correction. It exercises both
dialects, empty and Unicode alias sets (including `ss` versus `ß`), malformed
counts/digests/paths/lengths/hex/keys, duplicate and reordered aliases, distinct
valid receipt drift, and the actual hermetic environment owner with a spaced
receipt path. Cargo commands do not inherit this preflight-only authority.
This is contract evidence, not a completed Windows Stage3 run.

No live receipt, old source, or cache was edited. The already-built Stage2 may
remain an admitted parent under its existing source/tool checks; it does not
retroactively prove Git equality. Preserve existing artifacts and create a new
candidate lineage with this repair through canonical admission. Never rewrite
old captures, strip alias rows, or reuse their fingerprints as a substitute for
fresh consistent authority. Native qualification remains pending.
