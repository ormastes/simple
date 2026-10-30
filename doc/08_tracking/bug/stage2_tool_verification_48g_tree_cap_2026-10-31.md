# Stage 2 tool verification exceeded the 48 GiB process-tree cap

Status: **OPEN — cause attribution incomplete; no source fix identified.**

## Observed failure

On 2026-10-31, Stage 2 compiler verification terminated with exit status 88
(`rss-cap-exceeded`). The outer watchdog measured 50,636,752 KiB against a
50,331,648 KiB cap, an excess of 305,104 KiB. Its terminal receipt reports
complete observation and quiescence. The observer scanned 458 host processes
and selected five processes in two retained process groups. It reports no
independent cgroup limit or OOM kill; `aggregate_workers=0` and
`scope_group=0`, so it does not attribute the measured peak to a product or
process group. This is evidence of a cap crossing, not evidence of a compiler
memory leak or a regression.

The failed attempt used source commit
`b4da851ad01b3b762879014e683635313a8a4a83`. Its admitted Stage 2 compiler was
SHA-256
`be8b7eb90beebb93f64007cd6cfb8e2f26921b0dbbe3e35afd3851db293cb36a`; the
matching frozen runtime capsule was
`phase2-runtime-capsules/be8b7eb90beebb93f64007cd6cfb8e2f26921b0dbbe3e35afd3851db293cb36a`,
with capsule identity
`a2faf6ccf0e6149cadcb574a35d9bd54f455377cd28dd6f5d6ff0748880d6a99`.

The verification summary records 8 build threads, 4 test workers and
in-process test execution. Its only completed task row is `compiler_version`
(PASS, one second). The `compiler_cli_build` log reaches three
`load_sources` progress rows at 4,500/4,500 files, but has no terminal build
record. Its per-task max-RSS file is empty. No CLI executable, test-runner
build result, suite result or test count was recorded. The overall verification
and Stage 2 qualification therefore remain incomplete.

The CLI log records frontend policy values of 25,165,824 KiB for parse
workers, 9,000,000 KiB for HIR workers and 50,331,648 KiB for its tree budget.
It reports one parse worker, then three HIR workers from a request of eight;
the coordinator peak was 1,201,452 KiB. Commit headroom was unavailable, so
the HIR admission used the static worker estimate. The three final
`load_sources` rows reached 4,500/4,500 at 29,615 ms, 31,112 ms and 33,016 ms.
These admission and progress values do not establish actual worker RSS at the
outer cap crossing.

## Attribution limits

In `scripts/bootstrap/bootstrap-phase-verification.shs`, the source default is
`BOOTSTRAP_VERIFY_TOOL_BUILD_CONCURRENCY=2` (line 216). When that setting is
effective for Stage 2 with more than one build thread, lines 2596–2609 launch
the CLI and test-runner builds concurrently, each with half the phase thread
count, then wait for both. The retained attempt has no effective concurrency
setting, worker launch receipt, runner log, or per-group RSS peak. Moreover,
the CLI log says `requested 8`, so it does not establish that the conditional
two-build path ran. Concurrent work is a possible contributor, not a proven
runtime cause; the record cannot determine whether one product or a combined
footprint crossed the cap.

The per-product path in `scripts/bootstrap/phase-c-backend-commands.shs`
(lines 28–45) resolves the tree-RSS policy from `pure_tool_threads`, applies
the product frontend policy, and exports the resulting settings. The attempt
does not retain a worker-specific policy/terminal receipt sufficient to
attribute its aggregate peak. The 48 GiB outer cap and the CLI's logged policy
are known; their relationship to the unrecorded runner execution is not.

There is no comparable baseline proving this is a new regression. No source
change or cap increase is justified by the current evidence.

## Evidence retained

The original attempt remains under
`/tmp/simple-phase3-stage2-generic-v2-20261031/build/phase3-stage2-generic-v2/`.
The source checkout was commit `b4da851ad01b3b762879014e683635313a8a4a83`.
The key artifact digests are:

| Artifact | SHA-256 |
| --- | --- |
| `stage2-whole-rss-attempt2.env` | `68ad1ebb0beb8e690123a29b470f11124d513839f49cf1c1deb3518359b18716` |
| `stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/summary.env` | `9dae885d2a233e4048212f629fba1439a56ff94f5a19cc039b1ffb1163ecdcaf` |
| `stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/compiler_cli_build.log` | `b28ef90b8376ceb494ee1d00b208343c9d734c25a5810e68741a05b9200d2acd` |
| `stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/compiler_cli_build.max-rss-kib` (empty) | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `stage3/aarch64-unknown-linux-gnu/stage2-admitted/admission.env` | `f83bebf16e7867a4e5778d885b49dfb312bfd364b512947e668b17c87a7e33b7` |
| `phase2-runtime-capsules/be8b7eb90beebb93f64007cd6cfb8e2f26921b0dbbe3e35afd3851db293cb36a/phase2-runtime-capsule.env` | `bc53be4d1a75808164021cf39b98a8fee85a61ec3422e047a7f645f6a74891de` |

The source script digests at the failing source revision are
`bootstrap-phase-verification.shs`:
`37ec5a4766073663594ddb751e17468d7b0c2240d483a099eb5335c62e334805`, and
`phase-c-backend-commands.shs`:
`52ca0406f27fc15ec01d43e3e1ef7b4b8566710a3580a963a8ac7104341370b8`.

## Next bounded diagnostic

After the current Stage 3 owner finishes and approves another attempt, keep the
48 GiB outer cap and cache lineage. The source policy also accepts an explicit
`SIMPLE_BOOTSTRAP_FRONTEND_MEMORY_BUDGET_KIB` product share. A proposed
15,000,000 KiB share would yield a 9,000,000 KiB HIR pool at the policy's 60%
pool fraction, enough for one worker at the logged 9,000,000 KiB static worker
estimate. This is a policy-based diagnostic proposal, not a measured per-worker
RSS target or a proven fix; verify the resolved row values before launching.

To isolate whether the co-resident test-runner build contributes, a separate
same-policy attempt can set `BOOTSTRAP_VERIFY_TOOL_BUILD_CONCURRENCY=1`. Do
not combine these two changes if the goal is to attribute which one changed the
result. The existing `SIMPLE_MEM_SNAPSHOT_FILE` hook in
`bootstrap-phase-verification.shs` lines 1027–1031 creates a fresh per-row
trace and may be enabled if the admitted runtime supports it. Retain separate
row and outer watchdog receipts so the next result can distinguish product
RSS from the enclosing phase total.
