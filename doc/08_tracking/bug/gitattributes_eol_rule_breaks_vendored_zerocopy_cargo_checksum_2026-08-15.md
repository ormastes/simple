# .gitattributes eol rule corrupts vendored zerocopy .cargo-checksum.json for every cargo build

- **Date:** 2026-08-15
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
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

## Resolution (2026-08-15)

The diagnosis above was half right. Two distinct defects were found:

1. **Attr rule ordering + eol leakage.** `.gitattributes` ALREADY had
   `src/compiler_rust/vendor/** -text`, but (a) `-text` does not unset the
   `eol=lf` attribute inherited from the repo-wide `* text=auto eol=lf` line
   (check-attr kept reporting `eol: lf`), and (b) the exemption sat BEFORE
   `*.bat text eol=crlf` / `*.cmd text eol=crlf`, and git attributes are
   last-match-wins — so vendored `.bat` files (zerocopy ships
   `win-cargo.bat`) were still EOL-rewritten. Fixed: the vendor exemptions
   are now `-text -eol`, cover `src/runtime/vendor/**` too, and are placed
   AFTER the `*.bat`/`*.cmd` rules. Verified:
   `git check-attr text eol -- src/compiler_rust/vendor/zerocopy/.cargo-checksum.json`
   and `.../win-cargo.bat` both report `text: unset` / `eol: unset`.

2. **Baked-in damage at HEAD (residual).** The checksum JSON itself was
   never the corrupted file — a scratch worktree of HEAD shows it
   byte-identical to its committed blob. The mismatch is that the committed
   blob of `vendor/zerocopy/win-cargo.bat` at current HEAD (commit
   `5958de7d4c7`) is an EOL-mangled variant of the original: sha256
   `dbde5af5…` (768 bytes, MIXED CRLF/LF), while the committed
   `.cargo-checksum.json` records the upstream hash `5da2a90a…` (784 bytes,
   all-CRLF). The byte-exact original blob still exists in history at
   commit `ae55a746719`. So the attr fix alone does NOT cure a fresh
   checkout — reproduced in a scratch worktree of HEAD:
   `cargo check` fails with `error: the listed checksum of
   .../vendor/zerocopy/win-cargo.bat has changed`.

**Proof the full fix works:** restoring the working-tree file via
`git show ae55a746719:src/compiler_rust/vendor/zerocopy/win-cargo.bat >
src/compiler_rust/vendor/zerocopy/win-cargo.bat` (sha256 verifies as
`5da2a90a…`) and dropping the local checksum-JSON workaround,
`cargo check --release --bin simple` in `src/compiler_rust` finishes
`Finished release profile` with NO vendor-verification error and NO
workaround.

**Remaining action (deliberately not committed with this fix — vendor
content change, needs explicit sign-off):** commit the one-file restore of
`src/compiler_rust/vendor/zerocopy/win-cargo.bat` from `ae55a746719`. It is
left restored in the main worktree. Until it lands, fresh checkouts still
need the restore command above (the checksum-JSON workaround is obsolete —
do not use it; it papers over the wrong file).
