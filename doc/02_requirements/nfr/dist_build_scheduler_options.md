<!-- codex-research -->
# Build platform and fast feedback: NFR options

**Status:** N2 selected by the user on 2026-09-26. The final numbered requirements are in [dist_build_scheduler.md](dist_build_scheduler.md). Unchosen alternatives were removed. Every target requires zero known false cache hits, fail-closed incomplete work, current exact-tree/merge-candidate evidence, bounded scheduler resources and fenced publication. Measure on pinned fixtures, host/toolchain identity and stated warm/cold state.

| Option | Proposed measured targets | Pros | Cons | Effort |
|---|---|---|---|---|
| N2 — Fast feedback **(selected)** | On named fixtures: staged hook P95 ≤5 s, end-to-end pre-push P95 <10 s for one outgoing ref, and eligible warm ordinary-change preflight P95 <60 s. Preserve all mandatory evidence; report multi-ref and cold cases separately. | Makes the ZIP's warm-preflight goal and fast-push request falsifiable. | Needs stable benchmark hosts and careful ref/fixture eligibility. | L, about 8–14 benchmark/telemetry files and CI settings. |

For the selected option, include queue and admission time, action/receipt cache hits, executed mandatory checks, transferred bytes, unique/PSS memory, cold builds, exact baseline binary/toolchain digests, and an `INCOMPLETE` verdict with remaining work IDs at a deadline. Container worker measurements must identify physical host OS, execution OS/architecture, runtime/isolation class and provider, image/artifact digest, network mode and whether the execution is native or guest-backed. Report unsupported hosts as `BLOCKED`/`UNSUPPORTED`, never as another host's success. The ZIP's twelve native probes did not measure these targets. Numeric distributed throughput targets must be finalized from a recorded two-node baseline, not guessed.
