# FreeBSD worker memory admission focused verification

Date: 2026-10-08. Source base: `3001767f85eba3b6e401135aab1e1bfc18fac110`.
Producer: admitted Phase 1 FreeBSD seed SHA256
`daadf4c854c0ef8d5a0d9cf33379c3dd28a1f7ba7c93a6b915c77973943fb721`.
Execution: explicit `SIMPLE_EXECUTION_MODE=interpreter`, isolated guest source
`/root/simple-worker-memory-20261008`; original release source and caches preserved.
This evidence is Phase 1 focused evidence, not Stage 4 or whole-suite admission.

## Changes

The owning parallel scheduler retains CPU concurrency while admitting workers
against a separate MiB budget. A bounded, at-most-once-per-500-ms observer charges
owned roots and descendants, retains reservations for missing roots, and blocks
refill on unknown samples. The external sampled RSS watchdog remains necessary.
The callback defaults to disabled admission for cross-platform compatibility;
the FreeBSD 20-worker lane explicitly requests `--worker-memory-mb 20480`.
Unsupported hosts reject explicit positive budgets before worker spawning.

The canonical application entry imports the modified std parser and scheduler.
Child specs receive `run <spec>` from the production argv builder; they do not
receive the parent's aggregate budget. Help and callback source identity include
the new policy. The unused app-local parser duplicate was not modified.

## Bounded repair history

1. Dictionary keys required explicit text identity.
2. The standalone fixture's unavailable assert intrinsic was replaced with
   explicit nonzero assertion failures.
3. Default AArch64 JIT aborted before assertions with an out-of-range BL relocation.
4. The user-authorized interpreter exception exposed malformed RSS accepted by
   `to_int`, whose invalid multi-character conversion returns zero. Cycle 4
   stopped immediately; live tests remained unrun. Peak RSS349316 KiB; quiescent1.
5. After strict parsing repairs, actual FreeBSD `ps` column/PID0 corrections,
   platform opt-in and independent static review, the final authorized cycle passed.
   The reviewer also removed a prospective session escape in the probe harness
   before execution; child groups remain in the admitted session.

No unchanged failing commands or already-green checks were retried. The callback
checks were rerun once because their source-pinning/default policy changed.

## Cycle 5 evidence

| Criterion | Result |
|---|---|
| Numeric lexical/negative/overflow rejection; PID0 snapshot; zero RSS; CLI forms | PASS, 0.199 s |
| Actual pinned seed `test --help` advertises the option | PASS, 0.074 s |
| 20 owned roots and 20 descendants sampled on FreeBSD | PASS, 0.235 s wall; sampling 41,898 us |
| Live per-tree RSS charges | 4492–4512 KiB, all 20 present |
| Production scheduler, 3 BDD fixtures / 2 workers / 1 MiB | PASS, 3 real examples, 5.535 s |
| Refill with spare CPU slot and over-budget remaining worker | Known 1-root sample: 179824 KiB; refill waited until long worker completed |
| Long completion to refill start | 410560 us |
| Updated callback contract checks | 7 PASS, 0.013 s |
| Enclosing watchdog | exit0, quiescent1, peak804836 KiB against5859375 KiB; 150 s bound |
| Observer behavior | no errors/overruns; max gap107.274 ms, max sampling duration6.277 ms |

Exact input hashes are retained in `build/worker-memory/final-source-pins.json`;
the static review receipt is `build/worker-memory/static-review-cycle5.json`.
Raw logs, result, watchdog receipt and harness are in the same directory, with
matching guest evidence. Prior source is preserved under guest `cycle4-source`.
Tracked negative assertions are in
`test/01_unit/lib/test_runner/worker_memory_probe.spl`.

## Qualification boundary

Focused worker-memory validation: PASS. Production verification: NOT QUALIFIED.
Core/lib/MCP checks, independent final review and the configured whole-suite
attempt remain required. The small scheduler test does not prove a 20-worker
whole-suite completion or Windows RSS support. No whole-suite retry was performed.
