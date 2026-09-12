# macOS bootstrap chain — runs 1–5 (2026-09-12, aarch64-apple-darwin)

Lane: `bootstrap-from-scratch.sh --stop-after-stage2 --full-bootstrap --mode=dynload
--jobs=half`, from a detached worktree. Evidence root per run:
`<worktree>/.simple/storage/build/bootstrap/`. Times UTC unless marked local.

| run | tip | stage reached | wall | failure class |
|---|---|---|---|---|
| 1 | pre-#670 (+#670 patch) | Stage 2 sanity | 23m22s — seed 8m00s (12:49:38→12:57:37), stage2 build+sanity 15m23s (→13:13:00) | `native-capsule-receipt-invalid` — receipt line 4 (object size) held a heap address |
| 2 | `0e437dec9b1` | pre-Stage-2 refusal | 6m44s (13:15:45→13:22:29), all seed rebuild | `stale-evidence-output-root` |
| 3 | `1e99989ebe9` | Stage 2 env canonical-list gate | 25s (13:58:12→13:58:37), seed cached | wrapper precondition refusal — env allowlist drift (#674), fixed by #684 |
| 4 | `bd64f7eadd9` | post-Stage-2 authority comparator (native build COMPLETED) | 12m24s (13:59:51→14:12:15), admission ~39s, seed cached | comparator operand missing — admitted snapshot deleted mid-Stage-2, misreported as "changed" |
| 5 | `bd64f7eadd9` | **Stage 2 sanity** (admission + build + comparator all passed) | ~18m (23:19→23:37 local), incl. seed rebuild | `darwin-link-tool-unresolved` at the hello-world smoke link |

## Verdict lines (verbatim)
Run 1: `error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)` /
`receipt-content-mismatch:expected-bytes=1648:actual-bytes=1648:first-diff-line=4:expected=53657758209:actual=53657761281`
Run 2: `stage2-sanity-error: stale-evidence-output-root; use a new output root with a cache clone`
Run 3: `error: stage2 env assignment names do not match the canonical list for aarch64-apple-darwin` /
`unexpected: SIMPLE_NATIVE_INCREMENTAL` / `FAIL — 1 check(s), stage stage2 failed (exit 1) with NO diagnostic text in any of 8 log(s)`
Run 4 (from a live tail; the lane log was later truncated to its `rc=1` trailer):
`error: Rust runtime authority after Stage 2 comparator unavailable or I/O failed: <out>/runtime-admitted.txt <out>/runtime-after-stage2.txt status=2` /
`error: frozen runtime authority changed during Stage 2`
Run 5: `candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)` /
`error: in-process native-build: LLVM native linking failed: Linking failed: darwin-link-tool-unresolved` /
`error: Stage 2 bootstrap compiler sanity failed`

## Findings
**The receipt mismatch is cleared.** Runs 4 and 5 both built Stage 2 with the capsule receipt
comparing clean (#670/#677 worked). Only run 1 hit it; runs 2/3 were harness refusals.

**Run 4 was stale-evidence-root interference, not a compiler defect.** `status=2` is a
*missing operand*: `runtime-admitted.txt` passed the pre-Stage-2 check at
`bootstrap-from-scratch.sh:2897`, was gone by `:3013` with every other plain provenance
file, and only `stage2-home/` + the frozen `stage2-runtime-authority/` survived. Run 5
discriminated it — on a virgin root the snapshot survived Stage 2 and the comparator passed,
so the stage-2 child does **not** prune its own provenance and `SIMPLE_NATIVE_INCREMENTAL`
is exonerated; the deletion came from outside, on a root inherited from run 1.
**Rule: one fresh evidence root per run.** The comparator's "changed" wording misattributes
a missing operand and is worth fixing.

**Run 5's blocker, left undiagnosed on purpose.** Producer:
`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:809`
(`publish_darwin_link_tool_identity` → `darwin_resolve_link_tool`, `:798`), which falls back
to `/usr/bin/which <command>` and yields `""` on non-zero exit (`:269`/`:937` return the same
token as `Err`). On this host `which cc|clang|ld` all resolve and the stage-2 *build* child carries a full `PATH`; the *sanity smoke* child is launched separately and its env is recorded nowhere — the `*.bounded.env` files are bounded-process **log** metadata, not env
dumps. A PATH-starved child is the natural hypothesis but unproven; the next step is to make
that child's env observable, not to guess a fix.

## Resume / Stage 4
`SIMPLE_NATIVE_BUILD_THREADS=5 sh scripts/bootstrap/bootstrap-from-scratch.sh
--resume-stage3-from-admitted=<worktree>/.simple/storage/build/bootstrap` — run from the
worktree that produced the admission (the receipt binds to source). Stage 3 resume pins
`--threads 1` unless `SIMPLE_NATIVE_BUILD_THREADS` is set; `--jobs` is rejected. No resume was possible: no run reached an admitted Stage 2 compiler.

**Stage 4 is unreachable from a hand-run lane.** `--resume-stage4-from-admitted` requires a
scheduler lineage admission manifest (`SIMPLE_BOOTSTRAP_LINEAGE_ADMISSION` + `…_SHA256`,
re-verified via `bootstrap-scheduler-contract.shs`) **and** `--deploy` or
`SIMPLE_BOOTSTRAP_STAGE4_QUARANTINE=1` (the no-deploy authority). Without a scheduler lease
the manifest cannot be minted, so no Stage 4 CLI candidate exists to smoke-test.

## Runs 6-7 (2026-09-13, same lane, same host)

| run | tip | stage reached | wall | failure class |
|---|---|---|---|---|
| 6 | `4a8e716719e` (PR #690) | **Stage 2 sanity** | ~26m (23:55→00:16 local), incl. seed rebuild; Stage 2 build 723s (871 compiled, 0 cached, 0 failed, 135785 KB, linked via clang++) | `Linking failed: nil` at the hello-world smoke link |
| 7 | `0a7563eeca9` (PR #694) | **Stage 2 sanity** | ~18m, seed cached | `Linking failed: nil` — unchanged, and now provably NOT the link-tool step |

### Verdict lines (verbatim, run 7)
`error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)` /
`bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true` /
`error: in-process native-build: LLVM native linking failed: Linking failed: nil` /
`error: Stage 2 bootstrap compiler sanity failed` /
`error: --stop-after-stage2 requires a successful admitted Stage 2 compiler`

Rejected Stage 2 candidate, preserved and NOT deployed:
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`,
sha256 `b10911fc830181d11dfcdd59718d2c5d580b039063e25bac5644743171a28ffb`.
No Stage 3 resume was possible: no run has produced an admitted Stage 2 compiler, so
there is still no Stage 3 full-CLI artifact to smoke-test.

### The PATH hypothesis is disproven, and the child's env is now on the record

Run 5's blocker was left undiagnosed on purpose, with a PATH-starved sanity child as
"the natural hypothesis but unproven". It is now **proven false**. The sanity child's
effective environment is dumped to `<evidence>.env.txt` (PR #690, schema
`simple-bootstrap-sanity-child-env-v1`, written in the last shell before the perl
launcher's `exec`, which inherits `%ENV` verbatim; link-relevant names carry values,
everything else is recorded by NAME only). Run 6 recorded:

```
PATH=/opt/homebrew/Cellar/llvm@18/18.1.8/bin:/Users/ormastes/.local/bin:/opt/homebrew/bin:
     /opt/homebrew/sbin:/usr/local/bin:/System/Volumes/Preboot/Cryptexes/App/usr/bin:
     /usr/bin:/bin:/usr/sbin:/sbin:/Library/Apple/usr/bin:/Users/ormastes/.cargo/bin:
     /Users/ormastes/.orbstack/bin
SDKROOT=/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk
DEVELOPER_DIR=  CC=  CXX=  LD=
SIMPLE_DARWIN_CLANG=/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/bin/clang
SIMPLE_DARWIN_LD=/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/bin/ld
```

`/usr/bin` is on that PATH, so `/usr/bin/which clang` had every opportunity to answer
and did not. Spawning, not PATH, is what fails from inside the stage-2 native binary —
which is precisely why the fix's load-bearing step is the pinned absolute path, the one
branch that runs no subprocess at all.

### `darwin-link-tool-unresolved` is eliminated, verified negatively

`darwin_link_tool_unresolved_error` unconditionally PRINTS its message. Run 7's frontend
failure log contains **zero** occurrences of `darwin-link-tool` or `[linker-wrapper]`,
so resolution succeeds and the link now proceeds past it. The remaining `Linking failed:
nil` is a different defect, filed as
`doc/08_tracking/bug/stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`.

### A defect found by the fix, in the fix's own error channel

Between runs 5 and 6 the token changed from `darwin-link-tool-unresolved` to `nil`. The
producing function is declared `-> text` and ends in a concatenation of non-nil texts;
it returned the full message under the interpreter (spec green, message printed
verbatim) and `nil` from the stage-2 NATIVE binary. The difference was a `(text, text)`
tuple return destructured by the caller. Filed as
`doc/08_tracking/bug/native_tuple_return_of_texts_yields_nil_2026-09-13.md` (OPEN).
Nothing on the darwin link path returns a tuple any more, and the error builder also
prints — a returned string is only as trustworthy as the machinery carrying it.

### Operational notes
- **One virgin evidence root per run** (confirmed again). The tree is written
  read-only; `chmod -R u+w .simple/storage/build/bootstrap` before `rm -rf`.
- The post-Stage-2 runtime-authority comparator no longer reports a MISSING OPERAND
  (`status=2`) as "changed" — run 4's misattribution is fixed.
- `${bootstrap_darwin_link_env}` is word-split, matching the existing windows env
  convention, so an Xcode path containing a space would break it. Default Xcode/CLT
  paths contain none; worth quoting if a custom toolchain path ever does.

### Correction, same day: the tuple was a bystander

The paragraph above ("A defect found by the fix, in the fix's own error channel") blamed
a `(text, text)` tuple return for the `nil`. Run 7 disproves it: the tuple is gone and
the `nil` is byte-identical, and run 7's failure log has zero `[linker-wrapper]` lines
even though the error builder prints unconditionally — so that code was never reached.
The `nil` predates the tuple and survives its removal. The tuple record is marked
UNCONFIRMED accordingly. Mechanism for the original `darwin-link-tool-unresolved`
therefore remains **undiscriminated**: PATH is ruled out, but `process_run` not
answering, a nil from `.trim().split("\n")[0]` on the native path, and `file_exists` on
that output are all still live. The discriminating experiment is 10 seconds, not 18
minutes: run the rejected Stage 2 binary directly with `--verbose` and the pins
exported, and read which `[linker-wrapper]` site it reaches. Do that first.

Also not done, and not silently: task item 2 asked for the pinned tool paths **plus
sha256** in the stage receipt. Only the absolute paths are pinned and forwarded; no
digest is recorded or verified. The rejected candidate's own sha256 is recorded above,
but the artifact was deleted in cleanup — reproduce in ~18 min from a virgin root.

## Run 8 (2026-09-13) — the link nil is no longer reached; a new, earlier blocker

Lane: `--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, virgin
evidence root, worktree `agent-adcc9a67a5f248150`, carrying PR #702 (darwin link
error-payload hardening: every `"" == ok` status on that path is site-named and
reported unconditionally; the orchestrator refuses to format a nil into
`Linking failed: ...`). Cold Rust seed, ~35 min. Stage 2 built clean again.

Sanity verdict, verbatim:

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true
error: native capsule collection failed -- module, tag and detail follow
scripts.check.cert.redeploy_gate.fixtures.hello_world
native-capsule-receipt-invalid
receipt-content-mismatch:expected-bytes=1648:actual-bytes=1648
error: in-process native-build: build failed: 1 failed, 0 unverified, 0 not run, 0 ok of 1 unit(s) — ERROR: scripts.check.cert.redeploy_gate.fixtures.hello_world
error: Stage 2 bootstrap compiler sanity failed
warning: stage2 native-build failed (exit 2); Stage 3/full CLI unavailable
```

Stages reached: Stage 2 built, **not admitted**; Stage 3 not attempted.
Rejected candidate preserved at
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`.

What changed and what did not:

- `Linking failed: nil` does NOT appear. The run now fails in `native_compile`,
  before any link, so the run-7 site is not reached and the hardening is neither
  proven nor disproven end to end. `stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`
  stays OPEN.
- The new blocker is filed as
  `doc/08_tracking/bug/stage2_sanity_native_capsule_receipt_content_mismatch_2026-09-13.md`:
  the expected and actual capsule receipts are both 1648 bytes and differ, which
  by the verifier's own comment localises the fault to content — the fixed-width
  `content_hash` field being the obvious candidate.
- T1 reproducer for the bare-`""`-tail hypothesis (a `-> text` helper with
  several `return "literal"` branches and a bare `""` tail, plus an explicit-tail
  twin), native-built by this run's freshly built seed — the tier that emits the
  Stage 2 binary — prints `BARE-TAIL-OK / EXPLICIT-TAIL-OK / AFTER-WRITE-OK`.
  The minimal shape does not bite; whatever produced run 7's nil is narrower than
  that.

## Runs 9-10 (2026-09-13) — the receipt blocker is cleared; the link site is reached

### First, a correction to run 8

**Run 8 executed a compiler built WITHOUT PR #677.** Commit `54660c1a0d4`
(PR #702) is a stale-snapshot clobber of
`src/compiler/80.driver/driver_aot_native_output.spl`: `+22 / -100` on that one
file, of which only 11 added lines are its own work. It reverted `0e437dec9b1`
(#677, the `rt_file_size` receipt sites) and `418399c2d84` (#670, the
`first-diff-line` diagnostic). The history range `0e437dec9b1..54660c1a0d4^` for
that file is empty, and `--stat` lists one file, so the loss is exactly those
two. Restored in PR #708. Run 8's verdict above is therefore **not** evidence
against #677; it is evidence of the clobber. `.claude/rules/vcs.md` § "Sync must
never clobber" requires this disclosure.

### Run 9 — the canary fires, and it is the mode-matched reproducer

`--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, virgin root,
worktree `agent-a87b4c8362f754818`, carrying PR #708. Stage 1 admitted; Stage 2
built clean. Verbatim:

```
error: AOT compile error -- unit, reason and lengths follow on the next lines
error:   unit (bare):
scripts.check.cert.redeploy_gate.fixtures.hello_world
error:   reason (bare):
capsule-receipt-size-implausible:field=34363944961:runtime=632:<...>.o
error:   name-len=53 reason-len=403
```

`receipt-content-mismatch` is gone. On the real 834-unit dynload artifact — the
thing F45's single-entry probes could not reproduce — `rt_file_size` returns
**632**, the true size, while the optional-bound `fp.size` read returns
**34363944961** = `0x8_0010_2001`, a tagged heap pointer in the same `0x8_…`
space as live heap objects in that process. #677's remedy is proven end to end.

The build stopped only because that check was fail-closed, over a codegen defect
the file already routes around, on a run whose receipt was sound. PR #712 split
it: **blocking** on the value actually written (`-1` sentinel, `>= 2^40`),
**advisory** on the field-vs-runtime divergence. Note the 2^40 backstop did NOT
fire — 34363944961 is ~3% of it — so the inequality is the load-bearing half.

Stages reached: Stage 1 admitted; Stage 2 built, not admitted; Stage 3 not
attempted.

### Run 10 — capsule collection PASSES

Same command, virgin root, carrying PR #712. **The smoke build got past native
capsule collection for the first time in this chain.** The advisory canary fired
three times:

```
[receipt-size-canary] optional-bound scalar field read miscompiled: field=51251192833:runtime=632 path=<...>.o
[receipt-size-canary] optional-bound scalar field read miscompiled: field=51251189761:runtime=632 path=<...>.o
```

Same file, same process, field values **3072 bytes apart** — the identical
stride #677 measured — while `runtime=632` is stable across all three reads. The
field read is non-deterministic; the runtime call is not.

The blocker moved forward to the run-7 link site:

```
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
error: in-process native-build: LLVM native linking failed: Linking failed: no error payload from link_to_native (rendered nil); see the unconditional [linker-wrapper] prints for the failing site
```

This resolves run 8's open question: PR #702's link hardening is now **reached**,
and it is **RED**. Its refusal to format a nil into `Linking failed: ...` works —
the message names the condition. But the `[linker-wrapper]` prints it points at
**do not appear in the log at all**, so the failing site is still unnamed. That
is the next blocker and it belongs to
`stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`.

Stages reached: Stage 1 admitted; Stage 2 built, **not admitted**; Stage 3 not
attempted; no Stage 3 artifact exists, so none is offered as a candidate.
Rejected Stage 2 candidate preserved at
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`;
that run-10 binary IS the standalone codegen reproducer, sha256
`67c9c3a25dc6fdda945c3677e5d8a3fe4629a1cd80ac1d6d898596bb9cd049b4`, in worktree
`agent-a87b4c8362f754818`. It is **not tracked in git**; if that worktree is
reclaimed, rerun the command above — the defect has reproduced on every run so
far, so a fresh Stage 2 is a reliable source of a fresh reproducer.

## Run 11 (2026-09-13) — root cause of the link-nil found WITHOUT a lane run; lane then blocked earlier

Worktree `agent-a085dd4a2e26111ba`, branch
`work/macos-stage2-link-nil-dynload-codegen-2026-09-13`, base `a19a9dff461`.

**Method change that mattered.** Instead of a ~90-minute lane, the rejected run-10
candidate (`agent-a87b4c8362f754818/.simple/storage/build/bootstrap/stage2/
aarch64-apple-darwin/simple.rejected`) was run DIRECTLY on the smoke program with
`SIMPLE_COMPILER_TRACE=1` and the pinned darwin tools — ~40 s, and it reproduced the
failure exactly. (`SIMPLE_PACKAGE_INDEX_COLD_INIT=1` plus a private `HOME` is required
outside the lane, or it dies at `scv-authority-missing` before the frontend.)

**Result: the failing site is named.** Trace reaches `[LINKER] linker_info unwrapped`,
emits a BLANK LINE, then returns. The blank is the `[linker-wrapper]` diagnostic itself —
an interpolation carrying a nil collapses in full, tag included. `find_linker()` returned
`Result<(text, LinkerType), text>` and `linker_info[0]` is nil, so
`darwin_resolve_link_tool` returns `""` and the Err payload is nil. Run 10's conclusion
that "the prints did not run" was a false negative from grepping for the tag; the same
blank is at line 42 of run 10's own preserved log. Full elimination and fix in
`doc/08_tracking/bug/stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`;
`native_tuple_return_of_texts_yields_nil_2026-09-13.md` is REOPENED (its closure rested
on the same false negative).

**Fix committed** (`1d89ffc75ad`): `find_linker_path() -> Result<text, text>` +
`linker_type_for_path()`, `find_requested_linker` likewise; the unresolved-error builder
prints the literal line first and each value bare. Spec
`test/01_unit/compiler/native/linker_resolution_no_tuple_spec.spl`.

**Verification BLOCKED, and not by this change.** The Stage 2 rerun from a virgin root
died in ~4 minutes at the very first step — the Rust seed build — with
`error: rust-seed-build failed with exit 101`: 11 `rt_process_*` symbols are defined in
BOTH the Rust runtime (`process_observation_v4_twins.rs`, landed `920b7c2dcb3`) and the C
runtime (`runtime_process_owned.c`), and macOS `ld` rejects the duplicates because the C
archive is `-force_load`ed. **Stages reached: 0.** No Stage 2 candidate, no sanity
verdict, no Stage 3. Filed:
`doc/08_tracking/bug/macos_seed_build_duplicate_rt_process_twin_symbols_2026-09-13.md`.
The link-nil fix is therefore committed on diagnosis + elimination, NOT on an end-to-end
green lane; re-run this lane once the seed builds again.

Pre-push guards on this range, all foreground with `timeout 900`: conflict-markers PASS
(7 files), tree-size PASS (base 136748 files), guard-wiring PASS (1692 guards, 0 new
unwired), no-revert PASS (7 files, 0 reverts), divergence-delta PASS — 3217 pre-existing
offender(s), 0 introduced by this range (base verdict 3945 diverged vs 965 baselined;
recorded here as the delta escape requires).

**Execution evidence for the run-11 fix (interpreter tier, added before landing).** Both
specs run green through the seed's interpreter
(`phase1_1789233412/simple test <spec>`, `SIMPLE_LIB=<worktree>/src`):
`linker_resolution_no_tuple_spec.spl` 5/5 passed, and the pre-existing
`darwin_link_tool_resolution_spec.spl` 7/7 passed after the error builder was rewritten
to print literal-first/values-bare. That is the only tier available while the seed build
is red; it does NOT exercise native codegen, which is where the defect lives.
