# Staged true Phase3 → full CLI continuation

No observer or dispatch is armed for this work ref. The existing input ref
work/linux-656fa39e-children-20261124 at9c1de732ab6c0a57c1bed650ee65e55175584844
and its manual45326410090 observer remain untouched.

The existing successful P3 runner exports phase3-a/simple, its dynload
companions, actual native Hello executable/compile log/expected+stdout,
BEHAVIOR_PASS terminal, original producer/runtime hashes, build command,
resource policy and quiescent enforced owner receipt. Its archive is
linux-656fa39e-phase3-RUN. The exact runtime comes from the same run's sealed
qualified-656fa39e-parent-RUN artifact. Neither archive exists yet as a
successful P3 result; no ID or compiler digest is invented here.

The original child controller accepts only qualified Phase2, so it cannot be
reused unchanged for true Phase4. This isolated branch adds a strict P3 intake
and explicit parent-phase3 binding to the existing full CLI job. It does not
rename P3 to Phase2, rerun its successful Hello, rebuild Phase3, or reuse its
compiler caches. Complete retained P3 product companions are preserved and
checked after use. New product caches and qualification caches stay separate.

After genuine P3 success, the sole eligible command is:

`gh workflow run bootstrap-sanity-evidence.yml --repo ormastes/simple --ref work/linux-656fa39e-phase4-20261124 -f parent_run=ACTUAL_9c1de_CHILD_WORKFLOW_RUN`

Prerequisites enforced before any compiler:

* Exact parent control9c1de, workflow_dispatch and original input ref; successful
  New656fa39e phase3 and intake jobs. The unrelated early-CLI job need not pass.
* Exactly one artifact of each expected name, source/control/run metadata,
  nonexpired ZIP digest+size, safe unique member paths and actual member hashes.
* Actual P3 ELF and recorded digest, exact Hello ELF/digest and hello LF output,
  original successful wrapper argv, enforced cap/quiescence and immutable inputs.
* Matching original Phase2/runtime identities and new manual-run45326410090
  ancestry. Compile sources remain exactly656fa39e.

One full CLI job uses unchanged production entry/flags, same-source static
CUDA, one low-memory worker/batch4, measured75% available cap and2GiB reserve,
four-hour owner, and the reviewed version/help/run/positive+negative tests and
actual new-product native Hello. It remains provisional, not formal scheduler
admission or deployment. No runtime/manager receipt is synthesized.

The gate and payload upload retained evidence even on failure. Syntax and
source review do not establish that full CLI fits this envelope; only the
future actual product can qualify it. Do not dispatch a second run for the
same parent without checking existing run/intent evidence first.
