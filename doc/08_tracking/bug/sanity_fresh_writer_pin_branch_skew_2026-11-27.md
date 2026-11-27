# Sanity FRESH_WRITER pin: branch skew between release/1.0.0 and main (2026-11-27)

Status: open, owner review. Not re-pinned (pre-p2 trust-gate pins are owner-only).

Reported premise: "`315ea01f…` in `sanity-base-controls` does not match the
committed writer". Measured, that is **not** true on `release/1.0.0`; the skew is
on `main`.

| ref | `FRESH_WRITER` in `scripts/check/lib/bootstrap-stage3/sanity-base-controls.py` | sha256 of `sanity-control-functions.shs` | match |
|---|---|---|---|
| `origin/release/1.0.0` `a4c98d2afb7` | `315ea01f8d725590…adffead8` | `315ea01f8d725590…adffead8` | yes |
| `origin/main` (fetched 2026-11-27) | `ed4787d0704093d7…617e0a74e` (set by `b5a6d078671`, 2026-10-11) | `315ea01f8d725590…adffead8` (writer changed by `8fe2ea406e0`, 2026-10-22) | **no** |

On release, `scripts/bootstrap/tests/sanity-base-controls-test.py:63` lists
`ed4787d0…` only as a *rejected* prior writer (negative case), which is correct.
On main the module still pins the pre-`8fe2ea40` writer, so `verify_actual_writer`
fails and `sanity-base-controls-test.py` (run by `.github/workflows/repo-hygiene.yml`)
is expected to be red there (not checked against a CI run). Fix for main: forward-port the release re-pin (owner
decision; the writer change `8fe2ea40` was reviewed on release as the
`SIMPLE_NSCOPE_HIR_TRACE` passthrough). Checkout line endings were ruled out:
`core.autocrlf=false`, blob `e877cfc781ea` hashes identically in both checkouts.
