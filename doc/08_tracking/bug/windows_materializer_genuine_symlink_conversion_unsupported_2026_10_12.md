# Materializer rejects genuine tracked Windows symlinks

Status: FIX-IMPLEMENTED-VERIFICATION-PENDING

Diagnostic38170943932 proves a valid genuine link to the exact tracked target is rejected as tampered placeholder bytes. approve-symlink-conversion is parsed/exported but native creation still only accepts a non-reparse placeholder. General conversion remains OPEN; no arbitrary reparse deletion or guard relaxation introduced. Windows CI placeholder configuration is a narrow workaround only.

**Revalidated 2026-11-02: still plausible because the report title (Materializer rejects genuine tracked Windows symlinks) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 (lane-a6dffc9c) - already fixed, verification pending

Stale: fix `ea78cb1ed76` (2026-10-26, "fix Windows materialization of real symlinks") is an ancestor of
`release/1.0.0`. `scripts/setup/materialize-symlinks-windows.shs` now, for an existing `-L` path whose
`readlink -z` equals the HEAD target and whose index entry equals HEAD, runs native `normalize-symlink`
(`MaterializerApi.NormalizeSymlink`: reparse-tag/relative-target/HEAD-target checks on a held handle,
file symlinks reparse-deleted in place, directory symlinks unlinked and recreated as a placeholder) and
then proceeds through the normal hardlink/junction path. Retargeted symlinks and ordinary files still
fail closed ("existing symlink target differs from HEAD" / "tampered placeholder bytes").
Regression: `test/01_unit/scripts/materialize_symlinks_windows_real_checkout_test.shs` (positive exact
link, directory symlink, junction, negatives). Not run here: this host cannot create native symlinks
(`ln -s` -> Operation not permitted; test exits non-zero before reaching the materializer), so it needs
a Windows host with symlink privilege (Developer Mode / admin) to confirm.
