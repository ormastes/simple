# MCI-v2 stress producer

`scripts/check/check-mci-v2-stress.shs` is the sole producer for
`mci-stress-evidence-v1`. It validates, but does not launch, a stress campaign.
Each certified-platform campaign must supply independently signed receipts for
the platform, allocation, process, and rendering lanes. All four receipts bind
the same certified platform, run ID, source hash, configuration hash, and exact
start/end interval. The interval must be exactly 86,400,000,000,000 ns.

Every lane binds a tab-separated resource series with samples at both interval
boundaries and reports configured RSS, CPU, queue, and storage ceilings plus
the observed minimum and maximum for each resource. The producer recomputes
the sample count and extrema, requires every arbitrary-width decimal timestamp
to be in range and strictly increasing, and rejects any sample over its ceiling.
It also requires zero invariant, timeout, leak, and queue violations.
Missing samples, mismatched correlations, non-exact time, modified resources,
nonzero counters, or invalid signatures fail closed. Inputs are snapshotted and
outputs are published with the shared `openat`/`O_NOFOLLOW`, fsyncing,
atomic-no-replace publication owner.

The producer emits `artifacts/stress.evidence` and
`receipts/stress.receipt.unsigned.template`; it never emits a signed aggregate
receipt. An independent producer-key operator must review and sign live output.
`--contract-fixture` additionally requires `MCI_STRESS_CONTROLLED_FIXTURE=1`
and always emits `artifact_mode=contract-only`, `release_eligible=false`, and
`result=contract_only`. The aggregate therefore rejects fixture output even if
someone signs a fixture-shaped receipt.

The focused contract is
`test/01_unit/scripts/mci_v2_stress_contract_test.shs`. It covers exact-time,
resource-series, signature tamper, violation-counter, and aggregate-rejection
negatives. It does not perform or claim a real 24-hour run. Until a current,
signed real bundle exists, MCI-NFR-015 and MCI-NFR-016 remain `BLOCKED`.
