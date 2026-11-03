# Windows native checkout violates materializer placeholder contract

Status: OPEN

Actual failed run38169498820 and diagnostic38170943932 prove core.symlinks=true creates a genuine file symlink: tracked blob17 bytes versus dereferenced target2649 bytes. Scope CI selects core.symlinks=false before Windows native checkout; exact production placeholder predicate passes real Git false checkout and rejects true checkout and tampered bytes. Complete Windows native materialization/bootstrap remains pending.

**Revalidated 2026-11-02: still plausible because the report title (Windows native checkout violates materializer placeholder contract) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 (lane-a6dffc9c) — scoped fix present, verification pending

The scoped fix is on `release/1.0.0`: `.github/workflows/rust-bootstrap-multiplatform.yml:226`
and `:282` run `git config --global core.symlinks false` before the Windows
native checkout, so mode-120000 paths land as placeholders that the
materializer predicate (`placeholder_looks_like_target`,
`scripts/setup/materialize-symlinks-windows.shs`) accepts.

Local run of `test/01_unit/scripts/windows_checkout_placeholder_contract_test.shs`
on Windows 11 without Developer Mode: the `core.symlinks=true` arm fails at
`git checkout-index` (exit 1, no symlink privilege) before any assertion, so
the host cannot exercise the true arm. That is a host limitation, not a
regression.

Status: fix-implemented-verification-pending. Verify: re-run the Windows
native job of `rust-bootstrap-multiplatform.yml` and confirm the materializer
step passes; or run the test above on a host with symlink privilege (Developer
Mode or Linux) and expect `PASS: real Git checkout true fails ...`. The full
Windows native materialization/bootstrap remains a separate open item.
