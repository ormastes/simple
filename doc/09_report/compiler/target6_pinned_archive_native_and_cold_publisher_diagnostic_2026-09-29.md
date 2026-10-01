# Target 6 pinned archive native diagnostic (Linux ARM64)

Status: focused pinned read PASS; cold publisher replacement REJECTED pending
clear joint time/RSS improvement. Target 6 production qualification remains
open.

The no-stub Stage-2 native integration fixture now follows the published SCC
batch mapping to its receipt, opens the same 542-byte CAS archive through a
root-relative pinned descriptor, reads `interface.smf`, checks its SHA-256, and
closes the capability. All 8 scenarios pass in 0.14 s with 8,236 KiB peak RSS
under a 2 GiB virtual-memory cap. This exercises the path that previously ran
at roughly 15 GiB RSS without finishing; it does not by itself establish a
release memory budget or identify which prior type error caused the runaway.

The integration scenario checks the returned member bytes with
`sha256_u8_hex`. A second candidate used `sha256_u8_fast_hex` in the pinned
digest owner to request the runtime accelerator with a pure-Simple fallback.
That candidate was reverted along with the publisher switch after the joint
cohort did not show a stable gain.

## Cold publisher candidate and decision

A trial replaced the cold publisher's whole-blob CAS read and byte-by-byte
member copies with the pinned capability while preserving exact layout,
UTF-8, manifest, semantic payload, and `CURRENT` checks. All 8 native
scenarios passed. Two 30-pair alternating-order cohorts used the same fixture,
host, and 2 GiB cap. Each binary's output was checked for `8 examples, 0
failures`; the TSV files retain every wall-time and max-RSS sample.

| Candidate | Baseline p95 ms | Candidate p95 ms | Baseline max RSS KiB | Candidate max RSS KiB | Time + memory ratios | Faster pairs |
|---|---:|---:|---:|---:|---:|---:|
| Pure-Simple hex | 143.437 | 140.074 | 8,444 | 8,604 | 1.9955 | 15/30 |
| Accelerated hex | 145.022 | 137.810 | 8,456 | 8,616 | 1.9692 | 13/30 |

The accelerated cohort's time ratio is 0.9503 and memory ratio is 1.0189.
Its median paired time difference is -0.589 ms (candidate slower), and only
13 of 30 pairs favored the candidate. The first cohort's median paired gain
is 0.383 ms. Thus the apparent p95 gain is not consistent across pairs and
the 160 KiB RSS increase is not offset beyond measurement noise. The cold
publisher trial was reverted; its whole-blob verifier remains in production.
The retained samples are
`target6_pinned_cold_publisher_30pair_2026-09-29.tsv` and
`target6_pinned_cold_publisher_fast_30pair_2026-09-29.tsv`.

Baseline executable SHA-256:
`aea0429221d2e1a72abdcf4361d8bb7308505ee0f7399fd905bc830952889760`.
Accelerated candidate SHA-256:
`e956433a400d9aa78fe9026c8cd503e31c84444e617fc19fe59a15764540c8e0`.
These are Stage-2 hosted diagnostic workers, not Stage-4 authority.

Next: bound the pinned archive digest memory independently of blob size,
measure a realistic large archive on matched binaries, and admit the publisher
only after the joint ratio and hard budgets pass beyond measurement noise.
