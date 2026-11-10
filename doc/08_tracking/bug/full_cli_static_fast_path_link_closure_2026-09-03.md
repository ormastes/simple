# Full CLI static fast path retains the product link closure
## Open 2026-11-11 — BLOCKED (host-blocked: needs Apple-Silicon mac + producer auth), keep OPEN (lane ne10; see addendum)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** open optimization opportunity
**Observed:** 2026-09-03 on macOS arm64

Exact `simple --version` and `simple --help` execute no compiler operation, but
the admitted 24 MiB full CLI still links AppKit, Foundation, CoreServices,
IOKit, SystemConfiguration, Security, CoreFoundation, libc++, and libSystem.
The source-level runtime registry construction has been removed from ordinary
exact static requests, but dynamic-loader and image costs remain inseparable
from the monolithic product closure.

Any fix must preserve the single user-facing executable contract, K1 policy
validation, exact output, global-option behavior, Phase-7 activation, signing,
and plugin admission. Candidate solutions are an entry-closure-erased CLI-0
front executable or equivalent linker dead-stripping; neither should introduce
runtime source interpretation or a Rust-seed fallback.

Acceptance requires a producer-authenticated rebuilt arm64 full CLI and at
least 30 before/after process samples reporting p50, p95, max RSS, binary
segments, linked images, binary digest, and output parity.


## Round-10 verdict note (2026-11-06)
Verdict: host-blocked + feature-sized. macOS arm64 link-closure optimisation; acceptance needs a producer-authenticated arm64 full CLI and 30 before/after samples. Not reproducible on Windows.

---

## 2026-11-11 addendum — lane ne10 (P3 traverse, batch ne10)

**Verdict: BLOCKED — keep OPEN.** Corroborates the Round-10 verdict note (2026-11-06): this is a
host-blocked, feature-sized macOS arm64 link-closure optimisation; it is not reproducible on
this Windows lane, and no Windows-side signal can advance it.

- **Why blocked here:** the acceptance criteria require a producer-authenticated rebuilt arm64
  full CLI and ≥30 before/after process samples (p50, p95, max RSS, segments, linked images,
  digest, output parity). Producing and signing an `aarch64-apple-darwin` full CLI requires an
  Apple-Silicon macOS host plus the release producer credentials; the monolithic product
  closure (`--version`/`--help` linking AppKit/Foundation/…) cannot even be observed from this
  host.
- **Grant command (on an Apple-Silicon macOS host with producer credentials):**
  `sh scripts/bootstrap/continue-macos-self-host-chain.shs` (its Darwin phase runs
  `"$producer" native-build --target aarch64-apple-darwin --backend <backend> …` for the full
  CLI per `scripts/bootstrap/continue-macos-self-host-chain.shs:361-373`), followed by the
  30-sample before/after harness against the admitted binary. Any fix must preserve the
  single-executable contract, K1 validation, exact output, global-option behaviour, Phase-7
  activation, signing, and plugin admission, per the body above.
