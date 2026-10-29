# Phase2 Linux CLI parse fanout underprices worker memory

Status: focused policy regression and Astra source review PASS; bounded CLI work stayed within the tree cap, but compilation remains incomplete.

## Observed failure

Attempt 6 admitted Cranelift compiler `72b21f6a771c5df38094af04863f9354328d8f95de0406dec641ac08e733a06d` from source inventory
`88d9a448e1c488b44f8831e525994b30b4f021df97dc7bbac45e307ea81894c7`. Its
full CLI build requested 20 threads under the unchanged 50,331,648 KiB (48 GiB)
process-tree RSS cap. The policy admitted seven parse children using a
3,800,000 KiB per-worker estimate. A live process sample showed one parse child
at 18,432,644 KiB and the other six between 4,614,380 and 5,111,896 KiB. This
is a sampled child RSS, not a measured per-process peak. The watchdog measured
tree peak 50,349,068 KiB, 17,420 KiB above the enforced cap, and refused the
CLI artifact. The evidence values are retained in
`scripts/bootstrap/tests/fixtures/phase2_cli_parse_rss_sample_2026-10-29.sdn`.

The mismatch is specific and actionable: the configured parse estimate is
about 4.8 times below one observed Linux parse child's RSS. Under the policy's
60% tree share, the old estimate admits seven workers at a 48 GiB cap:
`floor(50,331,648 * 0.60 / 3,800,000) = 7`.

## Candidate response

For Linux only, price parse workers at 24 GiB (25,165,824 KiB). At the same
48 GiB cap and 60% share, this admits one parse cache-warmer:
`floor(50,331,648 * 0.60 / 25,165,824) = 1`. The estimate is about 36% above
the observed 18,432,644 KiB sample; it is a conservative admission price, not
a claim that the worker is capped at that amount. The process-tree watchdog
continues enforcing 48 GiB and remains authoritative.

The 20-thread build request remains intact. This prices down Linux parse
warm-up concurrency only; HIR remains independently priced at 9,000,000 KiB
(three workers under the same cap), and codegen's requested thread ceiling is
unchanged. Expected tradeoff: parse warm-up has one worker and may take longer.
No end-to-end throughput measurement has been made for the candidate.

Other fanout platforms keep their previous estimate until they have equivalent
process-level evidence. Windows retains its existing single-frontend policy.
The #5307 `SIMPLE_BUILD_MEMORY_RESERVE_BYTES` scrub fix is separate host
RAM/commit admission and does not change this tree-cap or worker count.

## Regression and next evidence

The focused shell regression consumes the retained measurement fixture, checks
that the previous estimate is below the observed sample, and verifies that the
old/new estimates imply seven/one workers under the same cap while HIR remains
three. It also checks the non-Linux and Windows policy paths.

The focused policy regression passed before source freeze. Its constant 20-job
assertion is not execution evidence for thread propagation; the production
request and receipt below establish the bounded attempt configuration. Do not
treat the 24 GiB estimate as a hard limit or raise the 48 GiB cap to mask worker
under-accounting.


## Attempt 7 production boundary evidence

The combined frozen source commit `36d94ddbc095308ab18b6bed30555350bee7f18b`
(inventory SHA256 `77b0c97831ffd7f1f7c04e1b85b9088369e30c2714697e3f2d4bc55c3444864a`)
produced admitted compiler SHA256
`a9ed5e4b92a811fa14f5ae351948c8d4350527f966139ea72ac13ccee3633e4f`.
Its 20-thread CLI attempt completed within the unchanged enforced process-tree
cap: watchdog peak 43,187,920 KiB, limit 50,331,648 KiB, status `complete`, exit 1,
and `quiescent=1`. Exact receipt:
`/tmp/simple-release-1.0.0-phase2-runner-recovery-build-20261030-attempt7/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/tmp/simple-process-tree-rss.786633.env`.

The CLI failed on unresolved `file_is_symlink` at
`src/app/stats/inventory_scan_v2.spl:63:12`, not an RSS-cap rejection. Its summary
reported 451 seconds and per-process maximum RSS 15,600,152 KiB; the latter is
not the aggregate tree measurement. This is bounded partial-workload evidence,
not full CLI success, a guarantee for later phases, or a causal percentage
memory/performance improvement: the combined source contains other changes.
The reduced parse pool trades concurrency for admission headroom; throughput
remains unqualified. Independent Astra source review found no P0/P1/P2 issues.
