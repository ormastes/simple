# .gitattributes eol rule corrupts vendored zerocopy .cargo-checksum.json for every cargo build

- **Date:** 2026-08-15
- **Status:** OPEN
- **Area:** .gitattributes vs src/compiler_rust/vendor/zerocopy/
- **Severity:** build friction — every fresh checkout/worktree needs a manual workaround before any seed build

## Symptom

`cargo build` in src/compiler_rust fails vendor verification for the
`zerocopy` crate: the on-disk bytes of a vendored file no longer match the
hash recorded in `vendor/zerocopy/.cargo-checksum.json`. Every agent/session
building the seed in this worktree carries a local uncommitted edit to that
file as a workaround (first noted by the write_span lane, 2026-08-15).

## Cause

`git check-attr text eol -- src/compiler_rust/vendor/zerocopy/.cargo-checksum.json`
reports `eol: lf` — a repo .gitattributes rule applies EOL normalization
inside `vendor/**`. Cargo's checksum was recorded over the crate's original
bytes; git's normalization on checkout changes bytes of one or more vendored
files (or the checksum file itself), so the recorded hash can never match.
Vendored trees must be byte-exact and exempt from EOL rewriting.

## Fix wanted

Add an exemption in .gitattributes:
```
src/compiler_rust/vendor/** -text
src/runtime/vendor/** -text
```
then re-checkout the vendored tree (`git checkout -- src/compiler_rust/vendor/`)
and drop the per-worktree checksum workarounds. Verify with a clean worktree
`cargo check` in src/compiler_rust.

Per CLAUDE.md Owned-Code Scope, vendor content itself is out of scope — this
bug is about OUR .gitattributes rule, not the vendored code.
