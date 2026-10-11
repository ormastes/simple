# Traceability Phase 2 runtime frontier

Status: **verification incomplete; release blocked**. The user explicitly
authorized continuing beyond the exhausted three-cycle limit with “go break
limit”. This supersedes the earlier stopping boundary, without relaxing source
provenance, resource enforcement, no-stub rules or protected release admission.
All **20 REQ-TRC /40 AC-TRC /WP0–WP7** retain their complete scope and open gates.

## Corrected construction and failed qualification

Canonical attempt4 used source
`102e4e11f29637a9bca009bbf1fac12db2449aaa`. Construction compiled1231 modules
with zero failed and produced a pure-Simple Stage2 compiler. Both frontend
sanity lanes and the struct receiver proof passed. The canonical owner emitted
construction admission and a frozen runtime capsule. Compiler SHA-256:
`a87555344143c2f8495c78fc849adfa07118d2573ba453def98cfb30188c5652`.
These receipts do not establish full compiler-matrix qualification.

| Required tool | Actual failure |
| --- | --- |
| Test runner | RSS cap88; sampled peak5937924KiB versus5859375KiB; after the native-compile marker and before backend dispatch. Witness/capsule preparation is an inferred location, not a measured boundary. |
| Full CLI | RSS cap88; sampled peak5876340KiB; HIR338/2536, before MIR |
| MCP | Native worker signal11; coordinator117 |
| LSP | Native worker signal6; coordinator122 |

Both runner and CLI argv included `--low-memory`. `--timeout600` did not bound
the entire command; the outer guard was3600s. The failed matrix was deliberately
terminated after these four mandatory failures. Only owned descendants were
signaled; the cancellation and cleanup are recorded. No matrix PASS or test
admission was emitted. Retired outputs/caches are preserved in byte-verified
archives; the a875 compiler, admission and frozen runtime capsule remain intact.

## Producer-bound native observations

An a875 native probe compiled and executed successfully. An independent host
oracle confirmed all ten printed observations: literal and omitted scalar/class
factory results42, counted omission deltas1/2, and explicit override delta0.
The probe itself always returns0; its exit is not an assertion verdict. The
historical seed-produced nil-default failure was not reproduced by this producer.
A separate asserted named-function and explicit literal-lambda probe returned7
for both and exited0. Both probes are **UNQUALIFIED diagnostic evidence**.

The actual nine-case SSpec remains unverified. A stripped compile wrapper failed
HIR because `describe`/`it` were unresolved. Importing the full framework failed
MIR on unresolved generic/method types. A typed helper prototype compiled but
crashed at a null callback; its compilation had reported `E-MIR-EXPR-Lambda`
yet continued. None of these prototypes replaces the nine-case or46-case suite.

## Concrete repair and remaining gates

`unsupported_expr_kind` recorded nonfatal errors that the driver downgraded by
its legacy message allowlist. It now uses `error_fatal`, retaining recovery
temporaries for diagnostic collection while blocking invalid publication.
Astra reviewed this causal correction: scoped source PASS, P0=0/P1=0.
Three modern behavioral SSpec cases cover fatality/code/span, diagnostic draining
and an unchanged advisory control. Recovery checks inspect the actual builder
locals and their unit types; execution is pending a corrected producer.

The first corrected-producer disk preflight failed at16GiB against the mandatory
20GiB floor. Retired owned checkouts and failed outputs were preserved before
reclaiming space. Canonical attempt5 used committed repair
`61c244201875640a90693469c573040140855d91`. Its initial disk gate passed at20GiB,
but its full preflight subsequently failed at19GiB against the same20GiB floor.
The seed, Cargo, lazy-import probe and source-marker checks passed; the canonical
command terminated with exit1 before corrected Stage2 construction. The prior
a875 producer remains historical evidence and cannot validate this changed
source. All three new SSpec cases and the corrected-producer rejection gate
remain **UNRUN**. The identical reproduced fixture and fresh-cache launcher are
prepared under `build/native_probe/traceability-fatal-rejection-stage2-61c244201875/`.

Incremental Astra source/manual review passed with P0=0/P1=0 after the local-type
assertions and inference wording were refined. This is not execution or release
admission. A focused four-file draft is prepared against the fetched release
snapshot `0d9a84736474555f6b3cd98d6b36f92561841b8f`; independent release validation
is pending. No protected branch, tag or admission was changed.

The integration gate must reject the reproduced callback fixture with nonzero
compile status, its named diagnostic and no executable. Closure body/capture
support, native SSpec helpers, separate HIR/MIR memory failures, complete graph
acceptance, core/MCP/LSP checks, coverage and authenticated release admission
remain open. Do not move HIR eviction earlier or change capture classification
without causal evidence. MIR hash streaming cannot repair the earlier CLI HIR
failure. No additional closure-support or memory change is claimed here.

Private evidence: `build/session/traceability-producer-repair-20261011/` and
`build/native_probe/traceability-*-stage2-a875/`; archive inventories bind every
retired leaf. Host hashes and Astra review are not broker-signed admission.

## Focused release backport bounds

This draft contains the unsupported-expression fatality change, its three
behavioral unit scenarios, authored manual and this evidence report only.
The diagnostic producer and preflight observations above were collected in
`/home/yoon/dev/simple-traceability-release-land-20261011`, on their exact
recorded source commits. They do not establish runtime qualification for this
release-base backport. The backport requires its own qualified producer, unit
execution, compiler/core/MCP/LSP checks and protected admission before landing.
