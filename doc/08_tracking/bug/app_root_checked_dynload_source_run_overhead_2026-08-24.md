# App-root checked dynload source-run overhead

Status: RESOLVED FOR SOURCE IMPORT CLOSURE, measured on 2026-08-24. Scope: Rust-seed source-run only; no
Pure-Simple production binary claim.

The checked product dynload cutover was measured against commit `3641c91c8f3`
with the same Rust seed and five `src/app/main.spl --dynsmf-status` samples.
The first checked-config candidate added a product-startup module and measured
p50 1.36 s (+10.6%) with max RSS 123,848 KiB (+0.6%), so it was rejected.
Folding the product owner into the already-imported `dynsmf_autoload` module
removed that extra import edge. An identical fresh five-sample campaign then
measured baseline p50 1.22 s and max RSS 122,856 KiB versus folded-candidate
p50 1.28 s (+4.9%) and max RSS 123,428 KiB (+0.47%). Samples:

- fresh baseline wall: 1.56, 1.62, 1.22, 1.21, 1.18 s; RSS max 122,856 KiB;
- folded candidate wall: 1.25, 1.28, 1.35, 1.29, 1.27 s; RSS max 123,428 KiB.

An eager attempt to co-own `SIMPLE_ASPECT_PACKS` was rejected: even after
moving its implementation out of the `app.cli` package, importing the full
aspect-pack graph raised p50 to 1.97 s and max RSS to 184,812 KiB. Raw APK
compatibility therefore remains the explicit deferred
`app.cli.startup_aspect_packs` path and its counters are marked not-owned,
never zero-measured.

The residual 60 ms p50 and 572 KiB max-RSS deltas are not meaningful against
the observed Rust-seed source-run spread. The empty-config path reads zero
config files, starts zero children, and performs zero tree scans. Re-measure
with the admitted Pure-Simple compiled app-root artifact before promoting the
450 ms compiled SMF-load target or claiming RSS admission; these source-run
samples are comparative evidence only, not an outer-harness receipt.
