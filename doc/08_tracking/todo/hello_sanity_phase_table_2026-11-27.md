# Hello-sanity Python group: phase classification (2026-11-27)

I ran the census with `git grep --cached` because C:/dev/simple is a sparse checkout.

| script | lines | callers (non-.py) | candidate stage when it runs | verdict |
|---|---|---|---|---|
| scripts/check/lib/bootstrap-stage3/sanity-base-controls.py | 185 | bootstrap-stage3/sanity.shs:1606 `bootstrap_stage3_base_control_command` (Python313 path plus helper hash 84f2a0d3...); repo-hygiene.yml:759 runs its test | stage2 sanity receipts (`stage2-sanity-error`), consumed by planner admission v2, phase2-runtime-binding, verify-stage2-compiler-tests, check-bootstrap-stage2-sanity-* | PRE-P2. Stays Python, no twin |
| scripts/check/lib/bootstrap-stage3/sanity-version-composition.py | 291 | sanity.shs:1693-1727 (python3.12 pin 1401f5c1...), resume-stage2-version-admission.shs, phase2-runtime-binding.shs, verify-stage2-compiler-tests.shs, check-stage2-candidate-requalification.shs (contract fixtures only) | stage2 version admission | PRE-P2. Stays Python. The reviewed-manifest entry is unchanged |
| scripts/check/lib/item5-hello-receipt.py | 179 | check-stage2-hello-world-native-build.shs:68, which bootstrap-qualify-stage2.shs:173 and build-binaries.yml:303 call (`--candidate bin/simple_stage2`) | stage2 qualification. p3-smoke-stage3.shs only cites it in comments and does not call the helper | PRE-P2. Stays Python |
| scripts/check/run-item5-matched-app-performance.py | 256 | none from scripts; invoked by hand per test/05_perf/app/vector_provider/README.md:39 | mode `production` compiler benchmarking built apps, after bootstrap | P3+. Twin: `src/app/item5_perf/main.spl` (PR a). Its Python test was deleted as dead by 02cd694e250; `test/01_unit/app/item5_perf/matched_perf_spec.spl` ports every case, and `scripts/check/check-item5-matched-perf-parity.shs` proves byte parity |
| scripts/bootstrap/hello-sanity-matrix.py | 920 | hello-sanity-matrix.shs / .cmd / .bash (bare `python3` / `py -3`) | `--phase {1,2,3}` is the bootstrap phase (`phase_capabilities`: 3 => interpreter + buildrunner) | DUAL-USE. Twin for `--phase 3`; wrappers route phase 3 to the twin and keep 1/2 on Python |
| hello-sanity-matrix-darwin.py | 128 | imported by matrix (importlib) | same as matrix | DUAL-USE (follows matrix) |
| hello-sanity-matrix-windows.py | 60 | imported by matrix | same as matrix | DUAL-USE (follows matrix) |
| scripts/bootstrap/hello-sanity-buildrunner.py | 303 | matrix.py:806, loaded only when phase_capabilities(phase)[1] is set, i.e. phases 2 and 3 | phases 2 and 3 | DUAL-USE (follows matrix) |
| hello-sanity-buildrunner-worker.py | 81 | spawned by buildrunner | phases 2 and 3 | DUAL-USE |
| tests (*-test.py, test/01_unit/scripts/*_test.py) | ~1,600 | repo-hygiene.yml:759 plus manual runs | n/a | Python tests stay for the Python copies. Twins get new _spec.spl / .shs tests |

Not in the hello group: repo-hygiene.yml:780 is check-stage3-hir-retained-parser-rss.shs, not a hello helper.

Trust anchor (owner default, 2026-11-27): each p3+ twin takes `--runner-sha256` and hashes the running, already verified p2/stage binary (`self_exe_path()`) before any side effect. It exits 2 when the pin is missing, malformed or mismatched. The Python copies keep their interpreter pins unchanged.

Lane split: (a) the perf-runner twin plus this table (this PR); (b) the matrix core, its Darwin and Windows helpers, and wrapper routing for `--phase 3`; (c) the buildrunner and worker twins.
