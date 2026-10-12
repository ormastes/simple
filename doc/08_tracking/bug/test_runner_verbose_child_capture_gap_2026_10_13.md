# Verbose aggregate execution discards bounded child evidence

Date: 2026-10-13. Status: confirmed observability gap; private source candidate **HOLD**, not ready for publication. Bug database reconciliation pending because a qualified database writer is unavailable.

## Reproduction and source owner

The immutable current-cut source is `cce267e717684e7f87aea1603df3da7c0745258d`. In `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`, both `run_test_file_interpreter` and `run_test_file_mcdc_interpreter_fallback` parse the existing bounded child stdout/stderr without emitting those streams under the runner's verbose option. The canonical single-file path in `src/app/test_runner_new/test_runner_single.spl` emits both streams. Rust `driver/src/simple_test.rs` also parses captured streams without emitting them; the proposed pure-Simple change does not repair that separate path.

The original twelve-file batch retained reported totals of 175 passes, 20 failures and 17 skips, but lacked raw per-case child lines and child import traces. These numbers are not 175 independently verified passing cases. Three text-import failures were counted by the old summary as one failed test each although their bodies did not execute. Their proper status remains infrastructure-held units. Previously reported passing files were preserved and not replayed.

## Private candidate and bounded qualification

Packet: `build/native_probe/phase1-child-capture-20261013-sol/`. `CANDIDATE_V2.patch` SHA-256 is `ae63370e6c5d9205a9b92f5e644657e49d22f357198e6f2d6dd25f46aade5466`. Baseline owner SHA-256 is `258c22f4955eb7490027027b16e76a9df6dd98a6828bbc26f77f93af47cf8a30`; candidate owner SHA-256 is `f7592c4255d046681b15db3046ef0fba7936b9b0af17af5c675980ca436d58e8`.

The candidate emits already bounded stdout/stderr only under `options.verbose`, labels streams separately and retains original truncation markers. It adds no subprocess or capture reread. Child completion is sampled before verbose output so printing does not inflate child execution duration. The output markers are unauthenticated human framing, not a case-count or structured-evidence authority. Shared production files were not changed.

Three invocations used the explicitly scoped Phase1 diagnostic producer SHA-256 `d95807daf8725254e6737f12b0a81965ac5ae0a9236b19eedac94940bd9867f1`. This producer is not the default pure-Simple tool and these invocations do not qualify native test products.

| Cycle | Actual outcome | Scope |
|---|---|---|
| 1 baseline | Exit 1, Job0, peak 233744 KiB | Fixture called unavailable bare `assert`; failed before child execution. Infrastructure failure, not semantic RED. |
| 2 baseline | Exit 24, Job0, peak 321324 KiB | Strict expected-passing-child guard failed. Parent-runner closure lacked the child's canonical `std.spec` files; original bounded capture remained unavailable. |
| 3 diagnostic candidate | Exit 24, Job0, peak 331024 KiB | Added 18 original committed closure files, retained strict guards, displayed actual child result. All 375 pinned source files remained unchanged; parent read trace stayed confined. |

The final candidate exposed child exit 0, separate stdout/stderr sentinels and a real named diagnostic assertion, `adds two runtime values`, passing. The production result nevertheless returned 0 passed, 1 failed with `--assert-ran: structured BDD evidence is unavailable for this execution mode` from `test_executor_parsing.spl:803`. The strict guard stopped the diagnostic. The candidate did not disable that evidence requirement or promote scraped text to structured authority.

Read-only follow-up identified a fixture configuration mismatch: its launcher set `SIMPLE_TEST_ASSERT_RAN=1`, but the argument list passed to `parse_test_args` omitted `--assert-ran`. That parser defaults `options.assert_ran` to false; the interpreter owner creates its structured receipt path only when the option is true. The reader correctly rejects the empty path while the environment demands evidence. This does **not** establish that interpreter execution is unsupported. Both current Rust BDD and pure-Simple `std.spec` contain real `simple-bdd-v1` receipt writers, and the canonical top-level runner synchronizes the option and environment. The supported matching configuration remains a separate original-test execution path, not permission to reopen this capped capture feature.

## Remaining acceptance

This feature is closed after three invocations. No fourth unchanged retry is authorized. Empty-stream, fallback failure, actual stderr truncation, quiet-output parity and complete duration/outcome acceptance remain unrun. The supported matching configuration still needs original-test execution evidence; this report does not qualify it. No additional original whole-suite cases were qualified. The six required Phase2 native products remain **0/6**.

Authoritative terminal records, exact command/environment/source pins and logs remain in `cycle1-baseline`, `cycle2-baseline` and `cycle3-candidate` under the packet. Documentation is the only landing-ready artifact from this feature; the source patch remains private and unqualified.
