# Materializer rejects genuine tracked Windows symlinks

Status: OPEN

Diagnostic38170943932 proves a valid genuine link to the exact tracked target is rejected as tampered placeholder bytes. approve-symlink-conversion is parsed/exported but native creation still only accepts a non-reparse placeholder. General conversion remains OPEN; no arbitrary reparse deletion or guard relaxation introduced. Windows CI placeholder configuration is a narrow workaround only.

**Revalidated 2026-11-02: still plausible because the report title (Materializer rejects genuine tracked Windows symlinks) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 — fix-implemented, verification pending

Fix landed in `ea78cb1ed76` (PR #4854, "fix Windows materialization of real
symlinks"): the materializer now opens the reparse point, reads the
`IO_REPARSE_TAG_SYMLINK` substitute name and admits a genuine link to the exact
tracked target. Regression: `test/01_unit/scripts/materialize_symlinks_windows_real_checkout_test.shs`.
Not verified on this host: it lacks SeCreateSymbolicLinkPrivilege
(`ln: failed to create symbolic link 'alias': Operation not permitted`, also with
`MSYS=winsymlinks:nativestrict`). Repro: on a Windows host with Developer Mode
enabled, `MSYS=winsymlinks:nativestrict sh test/01_unit/scripts/materialize_symlinks_windows_real_checkout_test.shs`
must exit 0, then set status fixed.
