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

The focused policy regression passed before source freeze. The production
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

## Re-check 2026-11-22 (aarch64 Linux) — still verification-pending

- `sh test/01_unit/scripts/product_frontend_worker_estimates_test.shs` ->
  `PASS: measured product worker estimates, unchanged caps, and Windows owner` (rc 0).
- The price is live in production: `scripts/bootstrap/lib/product-frontend-policy.shs:48`
  exports `SIMPLE_PARSE_SHARD_WORKER_KB=25165824` on Linux, read by
  `native_build_main.spl:833`. The integ25 Stage 2 compiler-CLI verification
  (compiler `ef46f0d2ab4274c4550530851db407bf9bad7f21bfabd50f9b56e87e77fd58d6`,
  `stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/summary.env`)
  records `verification_frontend_policy=SIMPLE_PARSE_SHARD_WORKER_KB=25165824`
  under a 62,914,560 KiB tree budget and admitted 2 parse shards
  (`fits 2 x 25165824 kB`), with no tree-cap refusal.
- Not verified: that CLI run has no terminal receipt. Both parse shards died
  with `exit=-139` (SIGSEGV) and the run fell back to in-process parsing and
  reached HIR, but as of 2026-11-22 10:15 no process of it is alive, its log was
  last written 07:26, `outputs/` is empty and `compiler_cli_build.max-rss-kib` is
  empty, so no whole-run tree peak exists under the 24 GiB price. Candidate
  records for the SIGSEGV (both show `[parse-shard] shard=N/2 ... FAILED exit=-139`):
  `stage2_parse_shard_segv_named_type_find_2026-11-13.md` and
  `native_build_fresh_hir_cache_dir_parse_shard_segfault_2026-11-12.md`. The old `file_is_symlink` blocker is gone
  (no longer referenced in `src/app/stats/inventory_scan_v2.spl`).
- The p4 `cli-f26` direct `native-build` is NOT evidence here: it never sources
  the product policy, and its 10 parse shards use the compiler's 3.8 GB clamp.
- Missing evidence: one completed bootstrap-script Phase 2 CLI build with this
  policy plus its `simple-process-tree-rss.*.env` receipt (status complete, peak <= cap).
