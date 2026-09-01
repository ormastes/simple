# Phase-1 compiler validation — compiler-scoped Simple test suite

## Binary under test (pinned)
- Source: `/mnt/fast/wt/stage-run27/build/phase_snapshots/phase1_1787465153/simple` (read-only, never run in place)
- Copy under test: `/mnt/data/worktrees/phase1-validate-1/valid/phase1-simple`
- size 157,165,888 bytes, md5 `4d7707b9cacc30ab8158bde859dbe7d4`
- `--version`: `Simple Language v1.0.0-RC` + the "Rust-built bootstrap seed only" banner (this IS the Rust seed)
- Worktree: `/mnt/data/worktrees/phase1-validate-1` @ `origin/main` = `ee1431e8138`

## Commands
Pass 1 (as-found worktree, no `bin/simple`):
```
find test/01_unit/compiler test/02_integration/compiler test/01_unit/app/cli test/01_unit/app/compile -name '*_spec.spl' | sort > valid/specs.txt
xargs -a valid/specs.txt -P 4 -n 1 valid/run_one.sh      # SIMPLE_TIMEOUT_SECONDS=0, timeout 600
```
Pass 2 (harness corrected: `bin/simple -> valid/phase1-simple`, `SIMPLE_BIN` exported), over the
466 pass-1 failures + the 565 pass-1 PASSES whose source greps for `bin/simple|SIMPLE_BIN`
(vacuous-pass risk) = 1031 specs, `-P 8`, timeout 900.

## Aggregate — pass 1 (2,184 specs)
| metric | value |
|---|---|
| spec files run | 2184 |
| outcome=OK | 1718 |
| outcome=ERROR | 458 |
| no verdict (timeout rc=124) | 3 |
| verdict w/o outcome (parse-error / zero-examples) | 5 |
| assertions executed | 16,561 |
| assertions passed | 15,386 |
| assertions failed | 1,180 |
| skipped | 0 |
| **phantom (verdict with executed=0)** | **16 — all outcome=ERROR; ZERO phantom passes** |

## Harness defect found in pass 1 (why pass 2 exists)
A fresh `origin/main` worktree has **no `bin/simple`**. 565 of the 1,718 pass-1 "OK" specs and a large
share of the failures shell out to `bin/simple` / `$SIMPLE_BIN` to run probes in a subprocess. Without it
they compared against empty output. Pass 2 symlinked `bin/simple -> valid/phase1-simple` and exported
`SIMPLE_BIN`, then re-ran all 466 failures plus all 565 shell-out passes.
- 42 of 466 pass-1 failures were environment-only and now PASS.
- **1** of 565 pass-1 passes flipped to FAIL — so the vacuous-pass exposure was real but tiny.

## Aggregate — corrected (pass 1 merged with pass 2)
| metric | value |
|---|---|
| spec files in scope | 2184 |
| spec files passing | 1759 |
| **spec files failing** | **425** |
| assertions executed (pass-2 subset: 6,779 over 1,031 specs) | see results2.tsv |
| phantom verdicts (executed=0) | 16 in pass 1, 16 in pass 2 — **all outcome=ERROR, zero phantom passes** |
| specs with no verdict at all (rc=124 timeout) | 3 pass-1 / 4 pass-2 |
| verdict lines with `reason=parse-error` | 4-5 |

## Root-cause clusters (425 failing spec files, post-correction)
| # | cluster | count | what it is | severity for bootstrap |
|---|---|---|---|---|
| G | behavioral divergence | 234 | assertions on real behaviour: interpreter/JIT divergence, pattern-match results, LLVM/MIR text, driver outcomes. Contains the genuine compiler-defect population. Biggest sub-trees: hir 31, codegen 30, backend 17, driver 14, interpreter 13, mir 12. Concrete examples: `cross_engine_silent_divergence_spec` (`expected FALSE got TRUE` on nil-through-bool-param), `match_bare_val_constant_spec` (`expected 4 to equal 1`), `parser_self_parse_spec` (`expected 0 to be greater than 0`). | **HIGH for the codegen/hir/mir/parser subset (~85)**; the driver/verification/cli remainder is off the phase-2 path |
| B1 | stale spec — source-text drift | 76 | spec asserts on a source file's header/`use` lines that have since changed. Fails with ANY compiler. | none |
| B2 | stale spec — API drift | 72 | spec calls compiler APIs that no longer exist. Verified by grep: `lower_module` on `HirLowering`, class `TreeSitter`, `ptx_mir_kind_to_primitive` are absent from `src/` entirely; 11 of 48 named symbols absent outright, the rest resolve to renamed/moved modules. Fails with ANY compiler. | none |
| C | compiler rejects valid-looking code | 35 | `semantic:` diagnostics not in the B2 shape — nil-contract, enum indexing, array/int mismatch, immutable-array mutation, unwrap-on-None. Mixed: some are the spec's own fixture being deliberately bad. Needs per-case triage. | MEDIUM |
| D | optional feature, gated | 4 | positive evidence in the message: "C backend does not support async CreatePromise", "LLVM backend does not support MatMul lowering", "Wasm backend E-BACKEND-WASM-INST-ConditionProbe", SIMD "simd-cfg-liveness-unavailable". Explicit backend gates, not silent breakage. | none |
| E | parse error (real) | 4 | `Unexpected token: expected pattern, found Case` — the phase-1 parser does not accept the soft keyword `case` in pattern position (`case_soft_keyword_spec`, `soft_keyword_identifier_corpus_spec`, plus 2). **Checked: no `case`-as-pattern usage exists in `src/compiler/**` or `src/lib/**`, so it cannot block bootstrap.** | LOW |
| A | environment | 0 remaining | all 42 recovered after the `bin/simple` fix | n/a |

Notes on things that look worse than they are:
- 4 logs contain "Segmentation fault", but all are specs that deliberately kill child processes
  (`supervised_build_survives_worker_death`, `native_build_missing_output_fail_closed`). Every one still
  emitted a SPEC FILE VERDICT, i.e. the harness and the binary survived. **Zero seed crashes observed.**
- One leaked artifact, `test/01_unit/compiler/.spipe_matchers_*_bdd_feature_group_keyword_spec.spl`,
  is another lane's temp file, not a real spec. Excluded from defect counts.

## THE DECISIVE RESULT — phase 2 could NOT be built by this binary
Read-only inspection of the phase-2 lane at `/mnt/fast/wt/stage-run27` (pid 818726, already exited —
it was NOT live during most of this validation):
```
build/bootstrap/bootstrap-progress.state       -> milestone=exit-1
build/bootstrap/logs/.../stage2-native-build.log:
  /usr/bin/ld: .../mod_148.o: in function `compiler__frontend__treesitter__outline':
  undefined reference to `OutlineModule.errors_push'
  clang++: error: linker command failed with exit code 1
  Build failed: link failed
```
`errors_push` is **called** at `src/compiler/10.frontend/treesitter/outline.spl:878` and
`src/compiler/10.frontend/treesitter.spl:122` as `module.errors_push(module.errors, e)`, and is
**defined nowhere in the tree** (`grep -rn "fn errors_push\|me errors_push" src/` -> 0 hits).
So this is a two-sided defect:
1. `origin/main` source carries a call to a method that does not exist (an incomplete edit), and
2. **the phase-1 compiler's semantic analyzer failed to diagnose the undefined method and its codegen
   emitted an undefined reference**, deferring a frontend error to the linker. That is fail-open
   behaviour of exactly the class the ADVISORY guard `check-no-unresolved-runtime-symbols.shs`
   was written for.

## Cross-reference against the Rust seed's own 87 cargo-test failures
| Rust-level defect | corroborated at Simple level? |
|---|---|
| generator lowering `Unknown variable: next` | **No.** 0 log hits across 2,184 specs. Not corroborated — and in-scope specs barely exercise generator lowering, so this is a coverage gap, not exoneration. |
| MIR interpreter constructs returning 0 (`expected 21, got 0`) | **Not by that signature** (0 hits). But the G cluster's 12 mir + 13 interpreter failures are the right shape and are the place to look for an independent manifestation. |
| module-global array aliasing corruption | not isolated by signature; candidates sit inside cluster G |
| unregistered runtime `realloc` provider | 1 in-scope spec touches it (`compiler/backend/rt_extern_decl_arity_spec.spl`); the seed-level finding is not contradicted |
| **(new, not in the Rust list)** undefined-method call reaching the linker | **Yes — and it is the bootstrap blocker.** See above. |

## Method / provenance caveats
- 4 workers for pass 1, 8 for pass 2 (raised only after confirming the phase-2 lane had already exited).
- MemAvailable sampled throughout: 80 GB -> 52 GB low-water -> 79 GB. Never near the 20 GB floor;
  no throttling was required and nothing was killed.
- `SIMPLE_TIMEOUT_SECONDS=0` throughout. Per-spec `timeout 600` (pass 1) / `900` (pass 2).
- The seed's own "this is a bootstrap seed only" WARNING banner is on stdout for every invocation and
  trips a small number of exact-stdout specs; those are environmental-by-design for this lane.

## Data files
- `valid/results.tsv` — pass 1, one line per spec: path, rc, full SPEC FILE VERDICT
- `valid/results2.tsv` — pass 2, same shape
- `valid/final.tsv` — **the full root-cause table**: cluster, spec path, behavior name, assertion message
- `valid/logs/`, `valid/logs2/` — complete per-spec output

## VERDICT — is the phase-1 compiler good enough?

**No — not as the bootstrap parent for this tree, and the proof is not a test statistic.** The phase-2
build this binary parented has already failed: stage2 exited 1 on a link error, because phase-1 codegen
emitted `OutlineModule.errors_push`, a method that exists nowhere in the source, and its semantic
analyzer never diagnosed the call. One undefined-method call in `10.frontend/treesitter` is enough to
stop the bootstrap dead, and it did. Whether the primary fault is the source (an incomplete edit landed
on `origin/main`) or the compiler (fail-open name resolution), the compiler's part is real and is
squarely on the bootstrap path.

Setting that aside, the spec suite alone would have supported a much softer verdict, and it is worth
being explicit about why it is not the deciding evidence. Of 2,184 in-scope specs, 1,759 pass. Of the
425 failures, **148 (B1+B2) are stale specs that would fail against any compiler**, 4 are explicitly
gated optional backends, and 4 are a soft-keyword parse gap proven not to occur in compiler or stdlib
source. That leaves roughly 270 failures with any claim on the compiler, of which the bootstrap-relevant
subset — codegen, hir, mir, parser, frontend — is about **85 spec files**, and those are real:
cross-engine interpreter/JIT divergence, a pattern-match arm binding 4 where 1 is expected, self-parse
returning zero. Those would each be a genuine defect lane. But none of them is what stopped phase 2.

Two secondary results worth keeping. First, the phantom-verdict class did **not** bite here: 16 specs
reported a verdict with `executed=0`, and every one of them was `outcome=ERROR` — zero phantom passes in
either pass. Second, the vacuous-pass exposure from the missing `bin/simple` was real in principle (565
passing specs shell out) but almost empty in practice: exactly 1 flipped to FAIL once the binary was
actually wired in.

**What would have to be fixed before this binary can parent phase 2:** the `errors_push` link failure
(source-side define-or-remove, and compiler-side make undefined-method a semantic error rather than a
linker surprise). Everything else in this report is a fix lane that can be scheduled behind it.
