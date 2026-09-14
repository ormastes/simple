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

## Run 12 (2026-09-13) — duplicate rt_process_* twin symbols fixed; first macOS seed link since 920b7c2dcb3

Worktree `agent-afb02377e5630cde7`, base `eede7583047` (PR #718 merged), virgin evidence
root (`.simple/storage/build/bootstrap` removed first), invocation
`--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`.

**The run-11 blocker is closed.** Eleven `rt_process_owned_v3_*` /
`rt_process_observation_v4_*` symbols were defined as strong `#[no_mangle]` exports in
BOTH `src/compiler_rust/runtime/src/process_observation_v4_twins.rs` and
`src/runtime/runtime_process_owned.c` (both landed by `920b7c2dcb3`). PR #718 gates the
eleven Rust twins behind the off-by-default cargo feature `process-rust-twin`, so exactly
one lane links; the C provider stays the default. The three `test_force_*` hooks are not
gated — their C counterparts exist only under `#ifdef RT_PROCESS_OBSERVATION_V4_TESTING`
and never collided.

Closing evidence is this lane's OWN log, the artifact the bug record named:
`.simple/storage/build/bootstrap/logs/aarch64-apple-darwin/rust-seed-build.log` —
`Finished 'bootstrap' profile [optimized] target(s) in 2m 36s`, and
`grep -c 'duplicate symbol'` = **0** (run 11: 12 lines, exit 101, stages reached 0).
Independently, a standalone GPU-feature seed built clean:
`cargo build --release --bin simple --features vulkan,metal,simple-compiler/vulkan-graphics`
exit 0, binary `/Users/ormastes/simple/build/cargo-f52/release/simple`,
sha256 `ccb387d05a4e595f0fa74c8cbceda14bb00242a6805ad888047bd0d8cbb73cbb`, 39,415,592 B;
`nm -gU` shows exactly one definition per formerly-duplicated symbol.
`cargo check --release --bin simple` (default/Linux feature set) exit 0, and the Rust lane
is genuinely selectable: `cargo check -p simple-runtime --features process-rust-twin` and
the same with `--tests` both exit 0.

`scripts/setup/build-gpu-seed.shs --verify` exits 1 on one probe,
`FAIL — test/01_unit/lib/sffi/wffi_into_bytes_spec.spl(rc=1: 5 examples, 5 failures)`.
That failure is byte-identical on the PRE-fix Sep-12 seed
(`build/cargo-r2/release/simple`, 39,528,776 B), so it is pre-existing and unrelated.

Linux was not run: this is a macOS host. `scripts/check/check-seed-builds-push.shs` is the
Linux gate for the same property (and per `.claude/rules/vcs.md` it is not push-wired).

Guards on the landed range `cb4f8d82c59..eede7583047`, foreground, `timeout 900`:
conflict-markers PASS (2 files), tree-size PASS (base 136750 files), c-runtime-compiles
PASS (145 files, 0 errors, 6 external-dep skips), runtime-api-regression PASS (3210
symbols, 0 removed), rt-dual-implementation ratchet PASS (2523 symbols, 0 new, 0 stale),
guard-wiring PASS (1692 guards, 0 new unwired), no-revert PASS (2 files), divergence-delta
PASS — 3217 pre-existing offender(s), 0 introduced by this range.

### Stage 2 verdict (verbatim) — the nil-error-payload failure RECURRED

Runs 2-6 are WARM restarts of the same evidence root (each logs
`Seed/runtime current (input content hash matches); skipping Rust rebuild.`); only run 1
was virgin-root, and it is the source of the seed evidence above. Runs 2-5 died on a
SECOND, independent macOS blocker filed as
`doc/08_tracking/bug/bootstrap_stage3_comparator_rejects_homebrew_cmp_symlink_2026-09-13.md`
(Homebrew's `cmp` is a symlink; `bootstrap_stage3_compare_bind` rejects it, and the
documented `BOOTSTRAP_STAGE3_COMPARE_TOOL` override is provably insufficient because
`bootstrap_stage3_compare_files` re-resolves the ambient `cmp` on every comparison).
Run 6 got past it with `env PATH=/usr/bin:$PATH BOOTSTRAP_STAGE3_COMPARE_TOOL=/usr/bin/cmp`
and is the first macOS lane since `920b7c2dcb3` to reach Stage 2 at all:

```
Stage 2: admitted parent → bootstrap_main.spl
  Stage 2: running bootstrap compiler sanity
  real log:  .../stage3/aarch64-apple-darwin/stage2-sanity.env.frontend-failure.log
  2 diagnostic line(s) found there. First 5:
    | candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
    | error: in-process native-build: LLVM native linking failed: Linking failed: no error
      payload from link_to_native (rendered nil); see the unconditional [linker-wrapper]
      prints for the failing site
PASS — 1 check(s), stage stage2 failed (exit 2) and said why
  warning: stage2 native-build failed (exit 2); Stage 3/full CLI unavailable
  warning: see doc/08_tracking/bug/bootstrap_stage2_empty_mir_bodies_2026-07-05.md
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

**Stages reached: 1 (Stage 2 built and was admitted as parent, then its sanity failed).**
No Stage 2 candidate was admitted, so Stage 3 was NOT attempted and there is no candidate
path/sha to record; nothing was deployed. **This is the first end-to-end verification of
`stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md` post-#717, and the answer
is that the failure RECURRED, byte-for-byte the same nil-payload message** — that record
should move from "committed but unverified" to "verified still failing".


## Run 13 (2026-09-13) — reproducer + the trace that settled the codegen defect

`--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, virgin evidence
root, worktree `agent-aa45d51377e3a4e99`, at `origin/main` 42347f19a51.
Stage 1 admitted; Stage 2 built 877 units clean; receipt-size canary fired
(`field=31758752897:runtime=632`, x3); smoke build failed at the link-nil site.
Identical outcome to runs 10 and 12.

Stages reached: Stage 1 admitted; Stage 2 built, not admitted; Stage 3 not attempted.

Two blockers hit before the run would start, both worth knowing:
- `error: Rust inputs changed during full bootstrap` — a tracked-file edit made
  WHILE a bootstrap runs kills it, during the seed build, long before admission.
- `error: Rust runtime authority private-admission origin comparator unavailable
  or I/O failed ... status=2` — `/opt/homebrew/bin/cmp` shadows `/usr/bin/cmp`
  and is a SYMLINK, so `bootstrap_stage3_compare_bind` fails its
  `candidate == canonical` check. Fix: put `/usr/bin` FIRST on PATH and leave
  `BOOTSTRAP_STAGE3_COMPARE_TOOL` unset, so auto-bind derives both the path and
  its sha256. Setting that variable by hand without
  `BOOTSTRAP_STAGE3_COMPARE_TOOL_SHA256` fails a different check in the same function.

**The trace is not visible through the script.** `bootstrap-from-scratch.sh`
sanitises the stage environment to a canonical env-name list, so
`SIMPLE_TRACE_FIELD_GET=1 sh scripts/bootstrap/bootstrap-from-scratch.sh ...`
emits zero trace lines. Replaying the Stage 2 `native-build` verbatim from
`stage3/<platform>/stage2-command.transcript` is what makes it observable, and it
is also a much better iteration loop: ~8.5 min per compile against ~35 min for a
full run, with no admission machinery in the way.

## Run 14 (2026-09-13) — receipt-size defect CLEARED; link-nil is the sole blocker

Same command, virgin evidence root
(`--output=.simple/storage/build/bootstrap-run14`), carrying the seed fix
(`-> T?` constructors no longer lose their struct name — see
`doc/08_tracking/bug/stage2_sanity_native_capsule_receipt_content_mismatch_2026-09-13.md`
§ RESOLVED). Stage 1 admitted; Stage 2 built 877 units clean, 492.5s compile +
10.4s link.

**First run in this chain where the receipt-size canary never fired** — no
`[receipt-size-canary]`, no `capsule-receipt-size-implausible`, no
`receipt-content-mismatch`.

Stages reached: Stage 1 admitted; Stage 2 built, **not admitted**; Stage 3 not
attempted. Verdict verbatim:

```
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
error: in-process native-build: LLVM native linking failed: Linking failed: no error payload from link_to_native (rendered nil); see the unconditional [linker-wrapper] prints for the failing site
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

New datum for the link-nil record: the `[linker-wrapper]` print now fires and the
command it names is a bare `0` with an EMPTY trail — so `find_linker_path()`'s Ok
payload is being read out of the wrong slot and yielding a zero word. Same family
as the receipt-size defect, different route, still open.

## Run 15 (2026-09-13) — comparator fix proven end to end; link-nil survives, and is re-diagnosed

`--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, virgin
evidence root `.simple/storage/build/bootstrap-run15`, worktree
`agent-aa71ab0be877cf286`, at `origin/main` 7dd8b7f509e plus two local commits
(LLVM unwrap routing + Stage 3 comparator restore).

**Run with the STOCK Homebrew-first PATH and no `BOOTSTRAP_STAGE3_COMPARE_TOOL`
override** — deliberately, because that is the configuration every previous run
had to work around. The comparator bind passed and the run reached the Rust seed
build, which is the first end-to-end proof of
`bootstrap_stage3_comparator_rejects_homebrew_cmp_symlink_2026-09-13.md`'s fix
on a real lane. (That bug turned out not to be unfixed at all: PR #670 landed
the fix and a later stale-snapshot commit reverted the `authority.shs` half while
leaving its four self-test fixtures in place. See that record § RESOLVED.)

Seed rebuilt from this tree (`Compiling simple-compiler`, `Compiling
simple-driver` in `rust-seed-build.log`), all four cargo invocations clean.
Stage 1 admitted; Stage 2 built clean; Stage 2 **not admitted**; Stage 3 not
attempted; nothing deployed.

Stages reached: Stage 1 admitted; Stage 2 built, not admitted.

Verdict verbatim:

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
[linker-wrapper] darwin-link-tool-unresolved -- command, trail and PATH follow
error: in-process native-build: LLVM native linking failed: Linking failed: no error payload from link_to_native (rendered nil); see the unconditional [linker-wrapper] prints for the failing site
error: Stage 2 bootstrap compiler sanity failed
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Rejected candidate:
`.simple/storage/build/bootstrap-run15/stage2/aarch64-apple-darwin/simple.rejected`
(139326920 bytes).

**Byte-for-byte the run-14 outcome, and that is the finding.** This run carried a
real, independently verified seed fix (LLVM `.unwrap()` was routed to
`rt_enum_payload`, which returns NIL for a flat nullable) and the site did not
move. The seed the script built was confirmed to carry that fix BEFORE reading
the verdict, by running the 1-unit repro against the run's own
`rust-authority-*/target/aarch64-apple-darwin/bootstrap/simple` — so this is not
a stale seed or a cargo-profile difference.

The re-diagnosis, which is the durable output of this run: **the `0` in the
`[linker-wrapper]` print is the INTEGER ZERO, not a nil** (a nil prints as a
blank line on this lane — measured). So `linker_result` was a well-formed
`Ok(0)` all along, and the defect is upstream, in `find_mold_path` /
`find_lld_path` / `find_ld_path` returning integer 0 at 877 units. Also
established: `is_err=false` never proved the Result was well formed —
`rt_enum_check_discriminant` answers false for a non-`Err` receiver of ANY
shape, and three runs mis-read that line as success. Full argument, the two
probes that did NOT isolate it, and the recommended next step (transcript replay
with `SIMPLE_TRACE_FIELD_GET=1`, reading `[FIELD-TRACE]` for `mold.spl`):
`doc/08_tracking/bug/stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`
§ CORRECTION, run 15.

## Run 16 (2026-09-13) — a fix aimed at the wrong arm; FAILED byte-for-byte identically

`--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, virgin
evidence root, worktree `agent-ac2a80b2450890897`, stock Homebrew-first PATH,
at `origin/main` 9670a991f02 plus one local seed commit.

The commit guarded `resolve_method_call_static`'s str/text/string
single-candidate UFCS arm (`mangle.rs`). Stage 1 admitted, Stage 2 built clean,
sanity FAILED with the identical `Linking failed: no error payload from
link_to_native (rendered nil)`.

**The lesson is the method, not the outcome.** The new Stage 2 candidate was
disassembled BEFORE reading the verdict, and `find_linker_path` still carried
`bl <_lib__nogc_async_mut__async__poll__Poll.unwrap>`. Instrumenting the guarded
function then produced ZERO hits for this program — it is not on the path at
all. **Check the emitted instruction before spending 26 minutes on a bootstrap;
run 16 is what that costs.**

## Run 17 (2026-09-13) — the linker-path defect is FIXED; a new blocker is exposed

Same lane and flags, virgin root, carrying the real fix (see below).

Site clean at instruction level — the range that read `bl <Poll.unwrap>` now
reads `bl 0x100c63430 <_rt_unwrap_or_trap>` — and the nil payload is gone from
the verdict, replaced by a real link error with a real message:

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
[DEBUG] CRT files not found, falling back to cc
error: in-process native-build: LLVM native linking failed: Linking failed: cc linking failed: ld: warning: ignoring duplicate libraries: '-lSystem'
ld: library 'c' not found
clang: error: linker command failed with exit code 1 (use -v to see invocation)
error: Stage 2 bootstrap compiler sanity failed
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Stages reached: Stage 1 admitted, Stage 2 built clean and REJECTED at sanity;
Stage 3 not attempted. Candidate preserved, not deployed:
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`,
139326760 bytes, sha256 `1a653582fc2c01d1203f…`.

Successor blocker filed as
`doc/08_tracking/bug/stage2_sanity_darwin_link_passes_lc_2026-09-13.md`: `-lc`
is a Linux-ism pushed by PURE-SIMPLE source
(`70.backend/linker/_LinkerWrapper/native_linking.spl`, `mold.spl`), a
different lane from the seed fix.

### The fix runs 16-17 bracket

`mangle_mir`'s two bare `.method` scans bound a bare `unwrap` target to the first
import-map key ending in `.unwrap`. The resolvers (`resolve_call_target`,
`resolve_method_call_static`) already refused this, but they run only when the
earlier scans left the name unresolved — once a scan rebinds, `known_mangled`
holds the new name and the resolver is skipped. The Cranelift twin
(`codegen/instr/closures_structs.rs`) had the same split. One
`is_enum_helper_method` predicate now covers both LLVM scans and all three
Cranelift lookups.

### The reproducer that ends the "needs the full closure" era

2 units, 2.6 s. The missing ingredient in every earlier attempt was a COMPETING
user method named `unwrap`:

| | LLVM | Cranelift |
|---|---|---|
| without the rival `unwrap` | `[/usr/bin/ld]` | `[/usr/bin/ld]` |
| with it, before | `[<value:0x4>]` | `[<value:0x4>]` |
| with it, after | `[/usr/bin/ld]` | `[/usr/bin/ld]` |
| genuine `rv.unwrap()` after | `[/real/rival]` | — |

The closure-size dependence belongs to the REBIND, not the payload: a small
closure has no competing symbol to bind to. **When a defect is said to need the
full closure, ask what the closure CONTAINS that a small one does not** — naming
it here turned a 26-minute lane into a 2.6-second loop.

**Residual, measured after run 17:** the fix cleared 62 of the 270 `Poll.unwrap`
call sites; **208 across 109 functions remain** by a second route (qualified-name
single-candidate fallbacks). Stage 2 is not blocked by them — they are latent —
but the population is NOT closed. See
`doc/08_tracking/bug/unwrap_still_rebinds_to_poll_unwrap_at_closure_scale_2026-09-13.md`.

## Run 18 (2026-09-13) — the darwin `-lc` is FIXED; libSystem was hiding behind it

Change under test: PR #752, a target-keyed library/CRT table in
`src/compiler/70.backend/linker/_LinkerWrapper/native_all_support.spl`
(`native_link_std_lib_args(os, mode)`, `native_link_uses_crt_objects(os)`,
`native_link_shared_std_libs(os)`), consumed by the direct-ld path, both
cc-fallback arms, and the shared-library line.

Link line, before -> after:

| target | before | after |
|---|---|---|
| darwin, direct ld64 | `-L /opt/homebrew/lib -L /usr/local/lib -lc -lpthread -lm -lSystem -lSDL2` | `-L /opt/homebrew/lib -L /usr/local/lib -lSystem -lSDL2` (one `-lSystem`) |
| darwin, cc fallback | `-L /opt/homebrew/lib -L /usr/local/lib -lc -lpthread -lm -lSystem -lSDL2` | `-L /opt/homebrew/lib -L /usr/local/lib -lSDL2` (driver adds its own `-lSystem`) |
| linux, direct ld | `-lc -lpthread -ldl --as-needed -lm --no-as-needed` | unchanged, byte for byte |
| linux, cc | `-lc -lpthread -ldl` … `-Wl,--as-needed -lm -Wl,--no-as-needed` | unchanged, byte for byte |
| freebsd | (both arms) | unchanged, byte for byte |

Darwin additionally stops treating a missing CRT set as a strict-link-profile
error. **Behaviour change worth knowing:** `allow_cc_fallback=false` on darwin no
longer fails — it routes to the compiler driver. That is deliberate (a direct
ld64 line was never workable without `-syslibroot`), but it means the strict
profile is not strict on macOS.

Spec: `test/01_unit/compiler/native/link_line_per_target_spec.spl`, 8 examples /
0 failures under the Rust seed. Linux and FreeBSD expectations are the literals
captured from the pre-change code, so a later darwin edit cannot move them.

Verdict: Stage 1 admitted. Stage 2 built its full closure clean — `Build
complete: 886 compiled, 0 cached, 0 failed`, 568.3s compile + 15.6s link — and
sanity FAILED one library further along:

```
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
error: in-process native-build: LLVM native linking failed: Linking failed: cc linking failed: ld: library 'System' not found
clang: error: linker command failed with exit code 1 (use -v to see invocation)
error: Stage 2 bootstrap compiler sanity failed
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

`-lc` is gone; the duplicate-`-lSystem` warning is gone. The new error is NOT a
regression — ld reports only the FIRST missing library, so `library 'c' not
found` had been masking the fact that libSystem was never resolvable here.

Rejected candidate preserved at
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`,
139327304 bytes. Rebuilding a three-line hello world with it reproduced the
failure in ~40 s, which is how run 19's fix was found without a second
25-minute cycle.

## Run 19 (2026-09-13) — the link is FIXED end to end; a non-linker blocker is exposed

Change under test: PR #753. `native_cc_platform_flags` now adds `-isysroot
<sdk>` on darwin, from `SDKROOT` when set else `xcrun --show-sdk-path`, and adds
nothing when no SDK resolves.

Root cause, measured directly rather than inferred:
`darwin_resolve_link_tool("cc")` resolves through `xcrun --find clang`, which
returns `/Applications/Xcode.app/…/XcodeDefault.xctoolchain/usr/bin/clang`. On
this host the active developer dir is CommandLineTools, so that clang's default
SDK is absent:

```
/Applications/Xcode.app/.../usr/bin/clang t.c -lSystem                          -> ld: library 'System' not found
/Applications/Xcode.app/.../usr/bin/clang -isysroot /Library/Developer/CommandLineTools/SDKs/MacOSX.sdk t.c  -> links
/usr/bin/cc t.c -lSystem                                                        -> links
```

The last line is why the failure looked impossible at first: the obvious `cc` on
PATH works fine, and only the xcrun-resolved one does not.

Spec: 9 examples / 0 failures. The new assertion only demands the flag where an
SDK actually resolves, so a host with none is not handed an empty `-isysroot`.

Verdict: Stage 1 admitted, Stage 2 closure clean, and the sanity hello world now
COMPILES AND LINKS — the first time on this lane. Stage 2 is still NOT admitted;
the gate advances past the frontend smoke and fails at the next check:

```
  Stage 2: running bootstrap compiler sanity
  Stage 2: proving struct receiver/runtime capability
error: Stage 2 struct receiver/runtime capability failed
    | error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
    | error: in-process native-build: Module surface registry graph promotion failed after phase 2
exit:  3
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Stages reached: 1 admitted, 2 built and rejected. Stage 3 not attempted. Nothing
deployed. **No candidate is preserved on the exit-3 path** —
`stage2/aarch64-apple-darwin/` is empty — so the 40-second witness loop is not
available for the successor. Filed as
`doc/08_tracking/bug/stage2_sanity_module_surface_registry_promotion_fails_2026-09-13.md`.

**Operational trap, cost one full 25-minute cycle.** A `timeout`-bounded waiter
(or any background waiter that gets killed) signals the bootstrap's process
GROUP. The run dies with a bare `Terminated: 15` that reads like a build failure
and leaves a stale lock, so the next run fails with `timed out waiting for
bootstrap output ownership`. Clear
`.simple/storage/build/.simple-bootstrap-locks` after any killed run, and poll
with short, unbounded foreground checks only.

## Run 20 (2026-09-13) — the phase-2 promotion blocker was already fixed upstream; macOS converges with Linux on site 8

**Headline correction, measured rather than assumed.** Run 19's blocker
(`Module surface registry graph promotion failed after phase 2`) was cleared by
`460aa9781cc`, the Linux BOOT-7 fix, which landed on `main` at 08:12 via PR #754
— **after** run 19's PR #753 merged at 07:58. Run 19 measured a tree without it.
An earlier draft of this entry credited the fix to this lane's rewrite of the
24-operand `not rt_transient_heap_promote(a) or not ...(b) or ...` chain; that
claim was withdrawn after it was tested rather than asserted.

**The counterfactual, because a causal claim about a 25-minute lane deserves
one.** Run 20's Stage 2 `native-build` was replayed verbatim from its own
`stage3/aarch64-apple-darwin/stage2-command.transcript` against `origin/main` @
`601bc2787b2` with the rewrite REVERTED (886 compiled, 0 failed, 450.3s). The
resulting candidate runs the positional Stage-3 route with
`grep -c 'promotion failed'` = **0**, logging
`phase2:surface:file:promote-done` / `commit-done` / `released seq=2`. Phase 2
promotes cleanly with no change of ours. The transcript replay is what made this
affordable: 8.5 min of compile against a 25-minute lane, and it is the right
instrument for any "was my change causal?" question on this chain.

What this lane does contribute: a fail-closed diagnostic
(`module_surfaces_promote_reason` — names the field, the surface index and its
logical/canonical/package names, the registry cardinalities, and a scope
sentinel that separates "the transient array scope is not active+paused, so the
runtime answers false for EVERY value" from a genuinely unpromotable field), so
the next occurrence of these 26 failure routes names itself instead of costing a
cycle.

Two operational notes that cost one cycle each and are not in the reproduction
recipe above:

- **The bootstrap needs `cargo` on PATH.** A PATH trimmed to
  `/usr/bin:/bin:/usr/sbin:/sbin` (to dodge run 13's Homebrew `cmp` symlink trap)
  dies in seconds with `error: failed to fingerprint Rust seed inputs`. The real
  reason is only in `<evidence-root>/rust-authority-fingerprint-error.log`:
  `fingerprint-step=resolve-rust-toolchain` / `resolver-frontend=absent`. Put
  `/usr/bin` FIRST and keep `~/.cargo/bin` on the PATH.
- **Run 19's "no candidate preserved" was a look-in-the-wrong-place error.** The
  exit-3 arm already keeps it, at `stage2-rejected/<PLATFORM>/` with a
  `rejection.env` — `bootstrap-from-scratch.sh:3091-3111` moves it OUT of
  `stage2/<PLATFORM>/`, which is why that directory reads empty. No script
  change was needed.

Verdict: Stage 1 admitted, Stage 2 closure clean (886 compiled, 0 cached, 0
failed), promotion message gone, and the Stage-3 route now advances through
`parse`, `hir`, `monomorphize`, `mir` and `native_cache` before dying in
`native_compile`:

```
  Stage 2: running bootstrap compiler sanity
  Stage 2: proving struct receiver/runtime capability
error: Stage 2 struct receiver/runtime capability failed
    | .../check-bootstrap-stage2-struct-receiver.shs: line 162: 18351 Segmentation fault: 11  env SIMPLE_BINARY=...
    | error: stage2 failed the positional pure-Simple Stage-3 route (status 139)
exit:  3
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

macOS crash report `simple-2026-09-13-083808.ips`, triggered thread frame 0:
`compiler__mir__mir_json__serialize_mir_function`. That is **site 8**
(`doc/08_tracking/bug/stage2_stage3_route_segv_mir_json_shadow_witness_2026-09-13.md`),
previously filed as a Linux BOOT-7 finding. The two lanes have converged: it is
now the single `--stop-after-stage2` blocker on both, and it is not
Linux-specific.

Stages reached: Stage 1 admitted; Stage 2 built and rejected; Stage 3 not
attempted; nothing deployed. Candidate preserved, not deployed:
`.simple/storage/build/bootstrap-run20/stage2-rejected/aarch64-apple-darwin/simple`,
139,327,000 bytes, sha256
`630ad64b7194eec6873fdcd6382c83ecad4b23f760d303a57eac5b26f214e0ed` (mode 400 —
copy out and `chmod +x` before a witness run). The ~40-second witness loop is
therefore available on macOS for site 8.

## Run 21 (2026-09-13) — site 8 confirmed fixed on macOS; site 9 localized

`sh scripts/bootstrap/bootstrap-from-scratch.sh --output=.simple/storage/build/bootstrap-run21
--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, stock PATH,
`cargo` present, no tracked file edited during the run. The tree carried an
independent fix for site 8 authored in this lane (`.values()`-based capsule
identity walk, no key lookup); the Linux lane landed its own fix for the same
root cause in parallel (`native_capsule_sorted_symbol_ids_v1` sorting an index
permutation), and that is the version now on `main`. **The two lanes agree on the
cause and each one's run independently shows the SEGV gone**, which is stronger
evidence than either alone.

Verdict, verbatim:

```
    | error: stage2 failed the positional pure-Simple Stage-3 route (status 124)
PASS — 1 check(s), stage stage2 failed (exit 3) and said why
  warning: stage2 native-build failed (exit 3); Stage 3/full CLI unavailable
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

**Status 139 → 124**, matching the Linux BOOT-8 result. `serialize_mir_function`
appears nowhere. `native_compile` is entered at `elapsed_ms=3950`
(run 20 crashed inside it at `elapsed_ms=94426`),
`current=compiler.common.module_path_naming`.

Site 9 is now LOCALIZED from this lane: every `sample` is self time in
`BuildGraph.topological_order`, with no callees, and macOS RSS is flat/falling
(12.3 → 9.8 → 9.4 GB) rather than growing as on Linux. Evidence and both
candidate causes are appended to
`doc/08_tracking/bug/stage2_stage3_route_native_compile_timeout_2026-09-13.md`.

Stages reached: Stage 1 admitted; Stage 2 built and rejected; Stage 3 not
attempted; **Stage 2 is NOT admitted and nothing was deployed**. Candidate
preserved: `.simple/storage/build/bootstrap-run21/stage2-rejected/aarch64-apple-darwin/simple`,
139,328,040 bytes, sha256
`e1ab37e7ba2caa3e587390c9d0d581b14ca4c93023e4cafe14abe28e5ee0c17f` (mode 400 —
copy out and `chmod +x` before a witness run).

## Run 22 (2026-09-13) — site 9 root-caused and fixed; site 8 confirmed on macOS; site 10 filed

Worked by transcript replay against `origin/main` @ `f26970e9d93` (PR #765), not
a full lane: 8.5 min per candidate against ~25 min, per run 20's note that this
is the right instrument for a "was my change causal?" question. Three builds
were spent (instrumented, then fixed) plus two 2-second native fixtures.

**The prescribed diagnosis was wrong, and the route log said so.** Site 9 was
being treated as a complexity problem in `BuildGraph.topological_order` — an
O(V·E)/O(V²) walk over the 886-unit closure, to be rewritten as Kahn's
algorithm. The route log reports `native_compile ... total=2`. The graph has
**two** units, and instrumentation shows both with **zero** dependencies: V=2,
E=0, correct walk = 4 iterations. No topological-sort algorithm is
distinguishable at that size. The Kahn rewrite was dropped; a Kahn loop written
`while ready.?:` would have failed identically.

**Root cause: `.?` on an empty array evaluates TRUE under native codegen.** The
DFS guard `while stack.?:` entered its body with `stack.len()==0`, popped nil,
and settled into a 2-cycle appending nil to `order` forever. Reproduced
standalone in 10 lines compiled by the same runtime authority — a never-popped
empty `[i64]`, a never-popped empty `[(i64,bool)]`, an array drained by `pop()`,
and a plain `if a.?:` all take the wrong branch while `.len()` reports 0 in the
same binary. Filed as
`doc/08_tracking/bug/native_codegen_dotq_true_on_empty_array_2026-09-13.md`
(compiler defect OPEN; only this call site routed around it, via
`while stack.len() > 0`). That record also explains the Linux lane's monotonic
RSS growth, which run 21 had left as an unexplained difference from the macOS
flat/falling curve: `visited[nil]=true` does not make `visited.has(nil)` true,
so `order` gains a nil every two iterations without bound. Same defect, both
lanes — the Linux signature MATCHES, but no Linux fixture was run, so "this also
unblocks Linux BOOT-8" is a PREDICTION, not a measurement.

Before / after, same fixture and runtime authority:

| | `native_compile` entry | outcome |
|---|---|---|
| before | `elapsed_ms=3747` | frozen; killed at 100 s and at 180 s (status 124) |
| after | `elapsed_ms=3764` | `state=failed` at `elapsed_ms=3983` — **219 ms**, both units attempted |

**Site 8 on macOS: CONFIRMED FIXED, and run 21's confirmation is withdrawn.**
Run 21 read "status 139 -> 124, `serialize_mir_function` absent" as the macOS
confirmation. That inference was unsound: `serialize_mir_function` runs
downstream of `topological_order`, so the 124 meant the code path was never
reached. (Both lanes made the same inference; a correction is appended to
`stage2_stage3_route_segv_mir_json_shadow_witness_2026-09-13.md`.) With site 9
fixed, the route runs MIR serialization and reaches LLVM IR emission and `llc` —
**no SEGV, `serialize_mir_function` absent, status 1.** Main's `driver_types.spl`
fix holds under aarch64 macOS codegen, now on evidence from a route that
actually executed it.

**Site 10, the new blocker**, two unrelated defects in `native_compile` of the
same 2 units: (1) the pure-Simple LLVM emitter reuses a local name —
`llc failed (exit 1)` / `module.ll:109:3: multiple definition of local value
named 'l14'`; (2) capsule identity is computed over empty content —
`capsule-identity=e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
is the SHA-256 of the empty string, making `native-capsule-source-mutated` a
false positive. Recorded in the site-9 record.

Stages reached: no virgin-root lane run in this entry — Stage 2 cannot be
admitted while site 10 is open, and the transcript replay is the stronger and
cheaper evidence for the fix. **Nothing deployed.** Candidates (scratchpad, not
preserved as lane artifacts): instrumented and fixed Stage-2 binaries, each
`886 compiled, 0 cached, 0 failed`, 136,078 KB, ~450 s.

## Run 23 (2026-09-13) — site 10b (capsule identity) FIXED end to end; 10a (duplicate local) is the sole blocker

`sh scripts/bootstrap/bootstrap-from-scratch.sh --output=.simple/storage/build/bootstrap-run23
--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, virgin evidence
root, worktree `agent-aa73a2371df95b0f5`, base `origin/main` `a8c7ecfaaa1` plus
this lane's fix, `/usr/bin` first on PATH with `~/.cargo/bin` present, no tracked
file edited during the run.

Stages reached: **Stage 1 admitted; Stage 2 built clean and NOT admitted; Stage 3
not attempted; nothing deployed.** Verdict verbatim:

```
  Stage 2: running bootstrap compiler sanity
  Stage 2: proving struct receiver/runtime capability
error: Stage 2 struct receiver/runtime capability failed
exit:  3
  real log:  .../stage3/aarch64-apple-darwin/stage2-receiver.log
    | error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
    | error: AOT compile error -- unit, reason and lengths follow on the next lines
    | error:   unit (bare):
    | error:   reason (bare):
    | llc failed (exit 1): .../module.ll:114:3: error: multiple definition of local value named 'l22'
    |   %l22 = add i64 %l35, 0  ; copy
PASS — 1 check(s), stage stage2 failed (exit 3) and said why
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

### Site 10b — capsule identity over empty content: FIXED, and it was a source-level defect

`native-capsule-source-mutated` and `capsule-identity=e3b0c442…b855` do not
appear anywhere in this run. The route now reaches `native_compile` with capsule
collection clean.

Cause: `frozen_native_cache_source_identity_v1` (`80.driver/driver_types.spl`)
hashed `SourceFile.content` at capsule-freeze time. Phase 3 runs
`reclaim_source_contents` → `reclaim_streaming_source_contents_owner` →
`evict_sources` **unconditionally** at
`80.driver/driver_hir_pipeline_lowering.spl:501-506`, and all three free or blank
that text; the same file already documented the fact at
`driver_native_extern_decl_site` ("Source CONTENT may already be evicted"). So
the digest was always taken over `""` — `e3b0c442…b855` is `sha256("")`. No
miscompile is involved, which is worth stating because every earlier site in this
chain (8, 9, the receipt size) was one.

`driver_native_frozen_source_lookup` (`driver_aot_native_output.spl`) carried the
SAME defect by a second route: it hashed `ctx.source_contents_owner`, which
`reclaim_streaming_source_contents_owner` empties.

Fix: `CompileContext.source_identities_owner` captures `sha256_text(content)` in
the phase-1 owner-promotion loop while the content is live, memoised per physical
path, never reclaimed (64 chars per source). Both lookups read that owner instead
of re-hashing; the lookup's `source_contents` parameter becomes
`source_identities`. `driver_native_capsule_identity_empty_v1` rejects `""` and
the digest of empty content fail-closed, and the collection site reports
`capsule-identity-empty` rather than a mutation.

Also removed: a DUPLICATE `driver_native_module_source_identity` /
`driver_native_disk_source_identity` pair at `driver_aot_native_output.spl:895-947`
— a stale-snapshot artifact whose `ctx.sources`-based version shadowed the
owner-array versions above.

Spec: `test/01_unit/compiler/driver/native_capsule_source_identity_survives_eviction_spec.spl`,
7 examples / 0 failures on the Rust seed.

### Site 10a — `llc: multiple definition of local value named 'l22'`: OPEN, but now localized

Not fixed here, and deliberately not guessed at. What this run establishes:

- **The emitting site is `translate_copy`.** Run 22 reported
  `%l14 = getelementptr i8, ptr %l25, i64 0  ; copy` (the ptr arm,
  `_MirToLlvm/core_codegen.spl:1865`); run 23 reports
  `%l22 = add i64 %l35, 0  ; copy` (the integer arm, `:1869`) at
  `module.ll:114:3`. Different local, different type, same instruction kind — a
  Copy whose destination local was already defined earlier in the same function.
- **It is NOT a `%t`/`%l` namespace collision.** `LlvmIrBuilder.fresh_local()`
  emits `%t{n}` from a module-monotonic counter, and its docstring records that
  the distinct prefix exists precisely so it cannot collide with `%l{mir_id}`.
  So this is two definitions of ONE MIR local id inside one function.
- **`defined_locals` already knows.** `MirToLlvm.defined_locals` is maintained as
  an emission receipt (`core_codegen.spl:1694`, `:1779`, `:2261`) and consulted
  at `:743`, `:933`, `:1386` — but it is never used to REFUSE a second
  definition. Whatever the right repair is (an SSA rename at emission, or fixing
  the pass that should have renamed), that receipt is where the condition is
  already observable.
- **Hypothesis, recorded so the next run can kill it in one grep.** The failing
  unit is `src/compiler/common/module_path_naming.spl`, whose
  `module_logical_name_from_path` (`:61-93`) reassigns a single `var mod_path:
  text` **seven times** — inside a `while`, across an `if`/`elif`, and after two
  early-exit-shaped branches. That is exactly what `var_reassign_ssa`
  (`60.mir_opt/mir_opt/var_reassign_ssa.spl`) exists to rename. When the IR is
  finally captured, the FIRST `%l22 =` definition and whether it shares a basic
  block with line 114 confirms or kills this immediately.

**`SIMPLE_LLVM_KEEP_STAGE=1` (added by this change) works, and is still not
enough.** `llvm_object_stage_fail` (`70.backend/backend/llvm_backend_tools.spl:273`)
`dir_remove`s the staging directory before its message is printed, so the
`module.ll` the diagnostic names was always already gone. With the flag the
message now ends `; staging kept at <dir>` and it did — but
`check-bootstrap-stage2-struct-receiver.shs` removes its own probe directory when
it exits, and the staging lives underneath it. The next step is therefore to copy
`module.ll` beside `diagnostic_path` (caller-owned, survives the probe teardown)
rather than rely on the staging directory.

### The 40-second witness: a replay-built candidate is NOT equivalent to a lane-built one

A Stage-2 candidate was rebuilt by transcript replay from run 21's
`stage2-command.transcript` against this tree (`886 compiled, 0 cached, 0 failed`,
452.9s compile + 11.0s link, 136078 KB). Every witness route on it failed BEFORE
`native_compile`:

- the positional Stage-3 route, replicating the gate's second probe exactly (with
  and without the stage-2 transcript env, warm and cold cache): `[ERROR] phase 1
  FAILED` immediately after `phase1:load_sources:owner_copy:done n=2`, with
  `SIMPLE_DUMP_COMPILE_ERRORS=1` printing no `[compile-error]` line — an error
  counted on a path that does not go through `CompileContext.add_error`;
- the gate script itself: its FIRST probe tries to rebuild the core-C runtime
  archive in a fresh `HOME` and dies in `src/runtime/hosted_cocoa.c` (Objective-C
  compiled as C, `@class` → `expected identifier or '('`);
- the interpreted route (`<seed> run src/app/cli/bootstrap_main.spl native-build …`):
  the Sep-13 seed cannot parse current source (`namespace` as an identifier at
  `src/app/build/targets/action_identity.spl:364,368`) and dies at
  `PLUG-E-K1-POLICY: bootstrap backend composition admission failed`.

**The discriminator was run rather than assumed.** The same script, env and
fixture pointed at run 21's PRESERVED lane-built candidate
(`bootstrap-run21/stage2-rejected/aarch64-apple-darwin/simple`, copied out,
`chmod +x`) passes phase 1 and reaches `phase=native_compile … total=2` at
`elapsed_ms=4642` (then hangs in `topological_order`, expected — it predates the
site-9 fix). So the witness ENV is correct and the phase-1 failure is a property
of the REPLAY-BUILT candidate. Run 20's advice that transcript replay answers
"was my change causal?" needs this caveat: on this host a replayed candidate is
not yet a faithful substitute for a lane-built Stage 2, and no claim resting on
one should be made without checking that it reaches the phase under test.

### Divergence-delta escape record (required by `.claude/rules/vcs.md`)

`check-test-tree-divergence-delta` PASS over a pre-existing red:
`PASS — 3218 pre-existing offender(s), 0 introduced by this range`; base verdict
`FAIL — 3946 diverged vs 965 baselined (3084 new, 103 fixed-but-still-baselined);
32 mirror-only (31 unallowlisted, 0 stale-allowlist)`. Offender list saved by the
helper to `/var/folders/94/j3lc49d93bx148gqls5kx5d40000gn/T//test_tree_divergence_preexisting.txt`
(host-local temp; regenerate with the helper). The range's only test file is the
new capsule-identity spec, which has no mirror twin.

Other guards, foreground, `timeout 900`: conflict-markers PASS (5 files),
tree-size PASS (range base 136957 files), no-revert PASS (5 files, 0 reverts),
guard-wiring PASS (1697 guards, 0 NEW unwired).

### Run 23 corrections (same day)

Two things above are stated more strongly than the evidence supports, and one
number is wrong. Correcting them here rather than editing the entry, so the
reasoning stays auditable.

- **"Not a `%t`/`%l` namespace collision" was argued from a docstring, which
  this chain has been burned by before (run 16).** The sound argument is the
  observed text: every operand in both reports is `%l<n>`
  (`%l22 = add i64 %l35, 0`, `%l14 = getelementptr i8, ptr %l25, i64 0`) and no
  `%t` appears in any reported line. That is what rules out the two namespaces
  overlapping — not `fresh_local`'s comment about `%t`.
- **`translate_copy` records no `defined_locals` receipt on its ordinary path.**
  The entry cites `:1694`, `:1779`, `:2261`; of those, `1694` is
  `translate_const`, `1779` is inside `translate_copy`'s `inttoptr` handle-unbox
  branch (which returns early), and `2261` is `translate_call`. The ordinary
  scalar/ptr/float copy tail sets `local_types` and `value_types` and never
  `defined_locals[dest_id]`. So `translate_copy` cannot refuse a second
  definition because it never asks.
- **Stage 2 built `886 compiled, 0 cached, 0 failed`**
  (`logs/aarch64-apple-darwin/stage2-native-build.log:3`). The
  `done=1 total=2 … failed=1` counts quoted from the receiver log are the
  two-unit STAGE-3 ROUTE PROBE, not the Stage 2 closure.
- Rejected candidate preserved, not deployed:
  `.simple/storage/build/bootstrap-run23/stage2-rejected/aarch64-apple-darwin/simple`,
  139,349,256 bytes, sha256
  `3b7b620a2e50ef8a0d875535ebf3478831f30d38d26136cc50799682d4945e36` (mode 400 —
  copy out and `chmod +x` before any use).

**Recommended first two moves for site 10a**, in this order, because together
they make the next lane self-diagnosing instead of another evidence run:

1. In `llvm_object_stage_fail`, copy `module.ll` to `"{diagnostic_path}.module.ll"`
   before the staging directory goes away. `diagnostic_path` is caller-owned and
   survives the struct-receiver gate's probe-directory teardown, which is what
   swallowed the IR this run even with `SIMPLE_LLVM_KEEP_STAGE=1` working.
2. Add a `defined_locals.contains_key(dest_id)` refusal at the top of
   `translate_copy` — it converts the llc rejection into a compiler-side
   diagnostic naming the MIR function and block, which is the information the
   fix actually needs.

## Run 24 — the guard fires, and it names the reason: `invalid terminator operands`

Lane: `--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, virgin
root, worktree `agent-a341b458ad89118a2`, carrying PR #784 (the fail-closed SSA
guard + the alloca-transform reject log + the `module.ll` keep). Seed rebuilt
(2m53s), Stage 1 admitted, Stage 2 built **clean**:
`Build complete: 886 compiled, 0 cached, 0 failed` / `418.7s compile + 10.5s link
= 429.3s total` / `136084 KB`
(`logs/aarch64-apple-darwin/stage2-native-build.log`). Verdict, verbatim:

```
error: stage2 failed the positional pure-Simple Stage-3 route (status 134)
PASS — 1 check(s), stage stage2 failed (exit 3) and said why
  warning: stage2 native-build failed (exit 3); Stage 3/full CLI unavailable
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

`status 134` is SIGABRT — the new guard, not llc. Stage 3 / full CLI were never
reached, so there is no candidate to smoke-check and nothing was deployed.

### What the lane now says that it could not say before

From `stage3/aarch64-apple-darwin/stage2-receiver.log`, verbatim:

```
llvm-emitter-ssa-violation::%l50 = getelementptr i8, ptr %l3, i64 0  ; copy -- a value is defined twice in one function
[llvm-ssa] fn=module_logical_name_from_path alloca-transform rejected: invalid terminator operands
[llvm-ssa] fn=_module_path_naming_strip_numbered_dirs alloca-transform rejected: invalid terminator operands
[llvm-ssa] fn=_module_path_naming_text_index_of alloca-transform rejected: invalid terminator operands
```

Three findings, in order of weight:

1. **Run 23's hypothesis is CONFIRMED, and its mechanism is now named.**
   `src/compiler/common/module_path_naming.spl` is the failing unit, and the
   reason the emitter saw un-renamed multi-def locals is that
   `ssa_alloca_transform_blocks` **refused all three of its functions** with
   `invalid terminator operands`. That reject comes from
   `ssa_term_operand_payloads_valid` -> `ssa_operand_local_payload_valid`
   (`60.mir_opt/mir_opt/var_reassign_ssa.spl:885-947`), whose own comment says
   why it exists: *"Struct-backed operands can arrive as nil in the staged-native
   lane."* So the root cause is NOT that the transform is too narrow by design —
   it is that a terminator operand's payload is **lost in transport inside the
   native Stage-2 candidate**, the transform correctly refuses to decode a nil,
   and the whole function then bypasses the only mechanism that would have made
   it SSA. Same defect family as `var_reassign_ssa.spl:35` ("Returning MirInst +
   [MirInst] through nested anonymous tuples can ... lose the defining
   instruction and appended Store in a pure-Simple bootstrap binary").
2. **The defect is native-lane-only, which is why no seed probe reproduced it.**
   Under the Sep-5 seed interpreter, the same `module_path_naming.spl` lowers and
   emits with **zero** duplicate `%l` definitions and **zero** rejects, as do a
   `var` re-assigned in a loop, a copy of a copy, and a struct-receiver method
   with a loop-carried accumulator (all four are now pinned in
   `test/01_unit/compiler/backend/llvm_emitter_ssa_violation_guard_spec.spl`).
   Any future probe of this site must run in the native lane; a green seed run
   proves nothing about it.
3. **A text-primitive divergence in the native lane, and the honest reading of
   it.** The violation line above is `llvm-emitter-ssa-violation::%l50 = ...` —
   an EMPTY function name, and a value "name" that is the whole instruction
   text. The obvious story ("`substring` ignores its end index") does NOT fit:
   if `substring(0, n)` always returned the whole string, the `define`-line path
   (`rest = substring(at+1, len)`, then `rest.substring(0, paren)`) would have
   produced the whole line, not "". **One fault explains both symptoms:
   `index_of` returning a not-found sentinel that is `>= 0`** (e.g. the string
   length). Then `eq = len` clears the `eq < 0` test and `substring(0, len)` is
   the whole line; and `at = len` makes `rest = substring(len+1, len) = ""`, so
   the function name is empty. The repo already carries a record for this
   primitive: `.claude/memory/bug_index_of_brace_needle.md`. `substring` itself
   is **unconfirmed** and should not be chased first.
   Consequence for the guard: the duplicate was still caught (the two
   definitions were byte-identical), but one whose definitions differed on the
   right-hand side would have been MISSED. Both extractions now use `split`,
   which is a different primitive — **assumed, not measured**, to be sound
   natively; if it also diverges the seen-key is no worse than the whole-line
   key it replaces.

### Correction to run 23's recommendation #1

`llvm_object_stage_fail` does now copy `module.ll` to
`"{diagnostic_path}.module.ll"` before the staging teardown, and that is the
right fix for every llc-side failure — but it does **not** help this one, and no
`.module.ll` was produced this run. The guard aborts inside `translate_module`,
before any IR file is written. The IR-keep is retained for the failure classes it
does cover.

### Next move for site 10b

Stop looking in `_MirToLlvm/**`: the emitter is now provably fail-closed on this
class. The open question is why a `Ret`/`If`/`Switch` operand payload reads as
nil inside the Stage-2 candidate for these three functions and not under the
seed. Dump the refused terminators from the native lane (the reject log already
names the functions, so the scope is three functions in one file), and treat the
`index_of` sentinel divergence above (`bug_index_of_brace_needle.md`) as a
candidate common cause rather than a separate cosmetic issue — a search
primitive that answers "found" when it did not is exactly the shape that would
leave an operand payload reading as nil.

Rejected candidate preserved, not deployed:
`.simple/storage/build/bootstrap/stage2-rejected/aarch64-apple-darwin/simple`,
139,350,072 bytes, sha256
`c7e536c1c5b743cd7b845a9596e6a3b7914decca1894b99a80c12badf08cbaa3` (mode 400 —
copy out and `chmod +x` before any use). Stage 3 and the full CLI were never
reached, so there is no Stage-3 artifact and no smoke-check result for this run.

### Divergence-delta escape record (required by `.claude/rules/vcs.md`)

`check-test-tree-divergence-delta` PASS over a pre-existing red:
`PASS — 3219 pre-existing offender(s), 0 introduced by this range`; base verdict
`FAIL — 3947 diverged vs 965 baselined (3085 new, 103 fixed-but-still-baselined);
32 mirror-only (31 unallowlisted, 0 stale-allowlist)`. Offender list saved by the
helper to `/var/folders/94/j3lc49d93bx148gqls5kx5d40000gn/T//test_tree_divergence_preexisting.txt`
(host-local temp; regenerate with the helper). The range's only test file is the
new SSA-guard spec, which has no mirror twin.

Other guards, foreground, `timeout 900`: conflict-markers PASS (4 files),
tree-size PASS (range base 136961 files), no-revert PASS (4 files, 0 reverts),
guard-wiring PASS (1697 guards, 0 NEW unwired).

## Run 25 — site 10a root-caused: the STOLEN UNWRAP, not a text primitive

Lane: `--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, virgin
root, worktree `agent-a797b495fc872651f`, carrying the one-file fix below.

### The reproducer is five seconds, not ninety minutes

Run 24's rejected candidate
(`c7e536c1c5b743cd7b845a9596e6a3b7914decca1894b99a80c12badf08cbaa3`) is a
working compiler, and the failing lane step is a **two-module** native-build of
`scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl`. Copied
out and re-run directly it reproduces the abort in ~5 s, with the same three
`[llvm-ssa] ... rejected: invalid terminator operands` lines. Every finding below
came from that loop; no lane rebuild was needed to root-cause.

Bisecting shapes against that candidate collapsed the problem immediately:

```
fn f_ret(a: i64) -> i64:
    return a + 1

fn main():
    print(f_ret(1))
```

```
[llvm-ssa] fn=f_ret alloca-transform rejected: invalid terminator operands
```

`main` — void — is **not** rejected. That is the whole signal: **every
value-returning function in the tree was refused, and only value-returning
functions.** The three `module_path_naming.spl` functions were simply the
functions in the first unit the lane compiled; nothing about paths, `index_of`,
loops or struct receivers was involved.

### Root cause: `.unwrap()` on the staged-native lane answers raw 0

`ssa_term_operand_payloads_valid`'s `Ret` arm
(`src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl:940`) read its operand as
`value.unwrap()`. The repo already documents what that does on this lane, in two
places, both of which this site had missed:

- `src/compiler/50.mir/mir_instruction_graph.spl:55` — *"`??`, NOT `.unwrap()` --
  the STOLEN UNWRAP: a bare `unwrap` published by another module can steal every
  `Option.unwrap` binding on this lane and return raw 0"*
- `var_reassign_ssa.spl:1216`, in the same file — *"`??` NOT `.unwrap()`: a bare
  `unwrap` published by another module (Poll, FailSafeResult) steals every
  `Option.unwrap` binding on this lane and returns raw 0."*

So `value.unwrap()` handed back raw 0; `ssa_operand_local_payload_valid`'s first
line is `if operand == nil or operand == 0: return false`, correctly reading that
as an absent payload; and `ssa_alloca_transform_blocks` refused the whole
function. `Ret(None)` never reaches the unwrap — it takes the `else: true`
branch — which is exactly why void functions passed and value-returning ones did
not.

Refusing the transform is what left those functions' multi-def locals unslotted,
which is the duplicate `%l50` that run 24's emitter guard then aborted on. Site
10a and the run-24 abort are one defect, not two.

### The `index_of` sentinel hypothesis is REFUTED

Run 24 proposed a native `index_of` returning a `>= 0` not-found sentinel as a
plausible common cause. Measured this run, same probe under the seed interpreter
and under a seed `native-build --mode=dynload` binary — **byte-identical, and
correct on both**:

```
index_of found slash = 3          index_of notfound ZZ = -1
index_of brace open = 5           index_of notfound brace needle = -1
index_of found brace needle = 5   last_index_of found slash = 13
last_index_of notfound ZZ = -1    contains found = true / notfound = false
```

Not-found is `-1` on both lanes, and brace-containing needles are found
correctly. Two further notes so this is not re-opened on the old evidence:
`module_path_naming.spl` never calls `text.index_of` at all (it hand-rolls
`_module_path_naming_text_index_of` over `byte_at`); and the
`bug_index_of_brace_needle` memo's `{app.mode}` needle is **string
interpolation** in a `"..."` literal, not a brace passed to `index_of` — writing
that needle literally in a probe fails at compile time with `variable
'app' not found`, which is a different defect from the one the memo names.

### Fix

One file, `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`: the reject site
plus the four sibling `Ret` sites on the same lane (rewrite, replace, collect,
alloca-rewrite) move from `.unwrap()` to the file's own `??` idiom via a named
`ssa_unreachable_operand_fallback()`. The four siblings are not cosmetic — once
the transform is admitted they run, and each would have fed a raw-0 operand into
the rewritten MIR. Presence is established by the `!= nil` / `.?` test above each
site, so the fallback is unreachable by construction.

Ownership note: the fix is in `60.mir_opt`, not `50.mir` — the defect was in the
SSA guard, not the MIR builder, and the builder's terminators were correct all
along.

### Note recorded, not chased

The run-24 candidate **SEGVs** (rc 139) while native-building any probe that puts
a struct behind `?` inside an enum payload, and reports `unresolved method call:
last_index_of` on a probe the seed compiles fine. Both are distinct from the
defect above and are not fixed here.

### Verdict, verbatim

```
error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
PASS — 1 check(s), stage stage2 failed (exit 3) and said why
  warning: stage2 native-build failed (exit 3); Stage 3/full CLI unavailable
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Read the status, not the word "failed": run 24 was **134** (SIGABRT, the SSA
guard); run 25 is **1** (a linker error). The abort is gone, `stage2-receiver.log`
carries **zero** `[llvm-ssa]` lines where run 24 carried six, the receiver probe
reports `bootstrap_stage2_struct_receiver=PASS`, and both units of the route
fixture now lower, codegen and emit objects. Independently confirmed at fixture
level: the minimal `fn f_ret(a: i64) -> i64: return a + 1` program, which the
run-24 candidate refused with 2 reject lines, builds on the run-25 candidate with
`status=0` and `llvm_ssa_rejects=0`.

Stage 3 and the full CLI were never reached, so there is no Stage-3 artifact, no
smoke-check result, and nothing was deployed. Rejected candidate preserved:
`.simple/storage/build/bootstrap/stage2-rejected/aarch64-apple-darwin/simple`,
139,350,072 bytes, sha256
`0341655b1fa369d8fcb0f05ed5632a337988c5f608588600a75d394ca130e342` (mode 400 —
copy out and `chmod +x` before use).

### Site 10c — the new first blocker (a different defect; do not re-file as 10a)

```
Undefined symbols for architecture arm64:
  "_compiler.common.module_path_naming.module_logical_name_from_path", referenced from:
      ___simple_main in 1-0b131fd108e7f872e3a2d6fbb4dbebeb3ede3aaaac563088e3442c7d4028b195
```

The CALLER emits a cross-module reference under the **dotted logical module
name**, while the callee's object defines the symbol under some other spelling —
a mangling mismatch at the cross-module call site, in the backend's symbol
naming, not in MIR or the SSA transform. Note the irony worth recording: the
symbol that fails to resolve is `module_logical_name_from_path` itself, the
function whose whole job is deriving that dotted name. Both objects compiled and
linked as objects; only the reference between them is unresolved.

### Divergence-delta escape record (required by `.claude/rules/vcs.md`)

`check-test-tree-divergence-delta` PASS over a pre-existing red:
`PASS — 3219 pre-existing offender(s), 0 introduced by this range`; base verdict
`FAIL — 3947 diverged vs 965 baselined (3085 new, 103 fixed-but-still-baselined);
32 mirror-only (31 unallowlisted, 0 stale-allowlist)`. Offender list saved by the
helper to `/var/folders/94/j3lc49d93bx148gqls5kx5d40000gn/T//test_tree_divergence_preexisting.txt`
(host-local temp; regenerate with the helper). This range touches no test file.

Other guards, foreground, `timeout 900`: conflict-markers PASS (1 file),
tree-size PASS (range base 136963 files), no-revert PASS (1 file, 0 reverts),
guard-wiring PASS (1697 guards, 0 NEW unwired).

### Regression coverage — stated honestly

There is **none automated**. The defect is native-lane-only: under the seed
interpreter the guard was always correct, and
`test/01_unit/compiler/backend/llvm_emitter_ssa_violation_guard_spec.spl` stays
6/6 green both before and after the fix. A spec that cannot fail before the fix
does not pin it. What pins it today is the fixture loop above against a real
staged-native candidate; the durable form would be a check that no `Ret` arm
under `60.mir_opt` reaches for `.unwrap()`, which is not built here.

## Run 27 — site 13 (cross-module symbol mangling) root-caused and fixed

Lane: `--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, virgin
root, worktree `agent-aee4c61a47998a6a9`, carrying the one-emitter fix below.

### The reproducer is five seconds, and it needs the route's env, not bare `native-build`

Run 25's rejected candidate
(`0341655b1fa369d8f cb0f05ed5632a337988c5f608588600a75d394ca130e342`) reproduces
site 13 in ~5 s, but ONLY through the positional Stage-3 route's environment.
A bare `native-build` of the same fixture dies EARLIER and elsewhere —
`MIR lowering transient scope failed ... bootstrap fn registry promotion failed`
— because the route sets `SIMPLE_BOOTSTRAP=1` (+ `SIMPLE_STAGE3_STREAMING_SURFACES`,
`SIMPLE_FRONTEND_CACHE=0`, `SIMPLE_NO_STUB_FALLBACK=1`,
`SIMPLE_BOOTSTRAP_STAGE3_REQUESTED_ROUTE=direct`, a `--runtime-path` and
`--runtime-bundle core-c-bootstrap`), which selects the bootstrap-flat pipeline.
Copy the env block out of `scripts/check/check-bootstrap-stage2-struct-receiver.shs:134-160`
rather than inventing one; point `--cache-dir` at a directory you keep, since the
probe script's own `trap ... EXIT` deletes the objects you need to `nm`.

### Defining vs referencing spelling (measured)

Both objects are produced by the SAME candidate, so this was never a
seed-vs-pure-Simple disagreement:

| side | `nm` |
|---|---|
| provider object `0-…` | `T _module_logical_name_from_path` (bare) |
| consumer object `1-…` | `U _compiler.common.module_path_naming.module_logical_name_from_path` |

The provider's two siblings are bare as well
(`__module_path_naming_strip_numbered_dirs`, `__module_path_naming_text_index_of`),
so it is the provider's rule, not a one-symbol slip.

### The oracle, measured rather than assumed

The Rust seed built from the same tree
(`rust-authority-a0d82ed5…/target/aarch64-apple-darwin/bootstrap/simple`) compiles
the identical fixture through the identical route with `rc=0` and defines
`_compiler__common__module_path_naming__module_logical_name_from_path` — also
module-qualified (`__` join, per `native_project/imports.rs:880`
`sanitize_mangled(format!("{}__{}", sibling.prefix, name))`). Two further in-tree
witnesses agree on the qualified-ness: every cross-module call site emits the
dotted name (`_MirLoweringExpr/method_calls_literals.spl:3809` `symbol_to_operand`),
and the flat bootstrap lowering path already emits non-entry defines as
`{logical_module}.{fn}` (`_MirLowering/bootstrap_globals.spl:523-527`). The
DEFINITION side is what deviates.

### Fix — one emitter, ordered last

`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` emitted each
function as `self.llvm_function_symbol_name(fn_.name)` with the bare MIR name,
and `_MirToLlvm/class_def.spl:184` `llvm_function_symbol_name` never adds a
module prefix. `translate_module_with_entry_policy` now records
`{module.name}.{fn}` for a NON-entry module's bare-named functions before any
function is emitted — beside the existing `owned_name_has_local` /
`export_symbol_names` pre-passes — and the selector consults it LAST, after
`main`, `@export("C")`, `@global`, `--no-mangle` and the runtime-owned rules, so
none of those contracts move. Because the `define` and every intra-module call
both resolve through that one selector, the two sides can no longer drift apart.
Entry modules, methods and statics (already owner-qualified, and excluded by the
bare-name test) are untouched; Cranelift and the interpreter do not go through
this emitter.

Ownership note: the fix is in `70.backend`, not `50.mir` — MIR's names and the
call-site registry were both correct; only the LLVM emitter's choice of emitted
symbol was.

### Regression coverage — automated, and it discriminates

`test/01_unit/compiler/backend/llvm_cross_module_symbol_mangling_spec.spl`
(4 cases) runs under the seed interpreter, so unlike run 25's fix this one IS
pinned: with the selector lookup disabled it is **3 of 4 RED**, with it **4/4
PASS**. Neighbours: `llvm_emitter_ssa_violation_guard_spec` 6/6,
`backend_basic_spec` 3/3; `backend_api_spec` (4/5) and
`backend_declaration_name_collision_spec` (2/3) fail identically on pristine
`origin/main` — pre-existing.

### Verdict, verbatim

### Site 13 is FIXED end to end — the witness, not the absence of an error

The lane's own receiver log, verbatim and complete
(`stage3/aarch64-apple-darwin/stage2-receiver.log`):

```
Build complete: 1 compiled, 0 cached, 0 failed
bootstrap_stage2_struct_receiver=PASS
bootstrap_stage2_positional_stage3_route=PASS
```

The route is the exact step that failed to link in runs 24 and 25. Re-run
standalone against the new candidate through the same 5-second reproducer, the
provider object now DEFINES what the consumer references and the program runs:

```
$ nm -gU .../darwin_link_inputs/0-…
0000000000000000 T _compiler.common.module_path_naming.module_logical_name_from_path

$ .../rt27/guard
app.cli.bootstrap_main
compiler.driver.driver
app.cli.main
run_rc=0
```

Three lines, byte-for-byte the fixture's own `# EXPECT stdout`. Before the fix
the same command on the same host ended in
`ld: symbol(s) not found for architecture arm64`.

**Scope of what this proves, stated honestly.** The emitter change was exercised
on small closures only — the 2-module fixture, hello-world, `p2_add`,
`stage2_mir_retention`, the struct-receiver probe. It was NOT exercised on the
886-unit Stage-3 self-compile, which this run never reached. The reasoning that
Stage 3 is unaffected (its `translate_module` sees `is_entry_module=true`, so the
qualification map stays empty and the change is inert there) is sound but
UNMEASURED. "Site 13 fixed end to end" does not mean "Stage 3 proven safe".

### Verdict, verbatim — Stage 2 still NOT admitted, on a NEW blocker

```
  Stage 2: running bootstrap compiler sanity
  Stage 2: proving struct receiver/runtime capability
stage2-sanity-error: frontend-status role=p2_add failure=bounded-bytes
stage2-sanity-error: sanity-receipt role=bootstrap0 failure=status-verification
error: could not publish immutable Stage 2 admission receipt
exit:  4
FAIL — 1 check(s), stage stage2 failed (exit 4) with NO diagnostic text in any of 8 log(s)
```

Read the failure, not the word "failed": runs 24/25 died in the CANDIDATE
(SIGABRT, then a link error); run 27's candidate passed every capability probe
the gate asked of it — all four frontend probes report `raw_status=0` on both the
`SIMPLE_BOOTSTRAP=0` and `=1` passes — and what failed is the gate's own
VERIFICATION of its receipt.

### Site 14, root-caused in the shell, not the compiler — and fixed here

`scripts/check/lib/bootstrap-stage3/sanity.shs:297-298` compared the collector's
`bytes_captured` against `"$(wc -c <"$log")"` as a **string**. BSD/macOS `wc`
right-pads its count even from stdin:

```
$ printf '[%s]\n' "$(wc -c < /etc/hosts)"
[     213]
```

so `[ "653" = "     653" ]` is false for EVERY probe on macOS while the numbers
agree (`bytes_captured=653`, log 653 bytes). GNU `wc` does not pad, which is why
this never fired on Linux, and this is the first macOS run to REACH that line —
24 and 25 died in the candidate first. Fixed by normalising arithmetically
(`$(( $(wc -c <…) ))`); the byte equality is unchanged and still fails closed on
a truncated or substituted log. Filed as
`doc/08_tracking/bug/stage2_sanity_receipt_bounded_bytes_authority_path_2026-09-13.md`.

**A dead theory, recorded so it is not re-derived:** the first draft blamed
`$CANDIDATE_FRONTEND_CAPTURE_PARENT` being a directory fd (`/dev/fd/6`) that
macOS cannot traverse. `sanity.shs:241` hashes that SAME path earlier in the same
loop iteration and passed, so the path resolves fine. The advisor caught this
before it shipped.

Stage 3 and the full CLI were never reached on this run, so there is no Stage-3
artifact, no smoke-check result, no Stage-4 attempt, and nothing was deployed.
Candidate preserved (not deployed):
`.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple`,
139,352,344 bytes, sha256
`4ff156b78b97068ce722d0aef2496b645d60e3e7f27acf471e76dd4781b4982d`.

### Also found: `main` cannot be checked out at all

`df7ac9f6cc2` ("feat(simd): x86 AVX-512 backend, …") replaced every
`.claude/commands/*.md` SYMLINK's target with the linked document's contents
while leaving the tree mode at `120000`:

```
$ git ls-tree ae55a746719 .claude/commands/spipe.md
120000 blob aad5653f…   # 18 bytes: "../skills/spipe.md"
$ git ls-tree df7ac9f6cc2 .claude/commands/spipe.md
120000 blob d94ce75c…   # 153,629 bytes: the full markdown document
```

Git then calls `symlink()` with a 150 KB target and gets `ENAMETOOLONG`, so no
checkout of `main` succeeds — locally (which is why this lane's PR had to be
replanted with `read-tree`/`commit-tree` instead of `git rebase`) or on CI, where
the required `Code Idiom & Structural Ratchet Gates` check dies at checkout for
EVERY open PR. Repair belongs to that lane: restore the 18-byte targets, or keep
the content and set mode `100644`.

### Divergence-delta escape record (required by `.claude/rules/vcs.md`)

`check-test-tree-divergence-delta` PASS over a pre-existing red:
`PASS — 3214 pre-existing offender(s), 0 introduced by this range`. Offender list
saved by the helper to
`/var/folders/94/j3lc49d93bx148gqls5kx5d40000gn/T//test_tree_divergence_preexisting.txt`
(host-local temp; regenerate with the helper). This range's only test file is the
new mangling spec, which has no mirror twin.

Other guards, foreground, `timeout 900`: conflict-markers PASS (9 files),
tree-size PASS (range base 137002 files), no-revert PASS (32 files, 0 reverts),
guard-wiring PASS (1697 guards, 0 NEW unwired). No Rust or C touched, so the
c-runtime / runtime-api / rt-dual gates do not apply to this range.

### Coordination

`doc/08_tracking/bug/stage2_cross_module_call_mangling_asymmetry_undefined_symbol_2026-09-13.md`
was filed independently by the BOOT-12 lane in PR #795, which measured the same
defect on Linux under `ld.lld` — that PR files the record, PR #800 carries the
fix, and the two have no source overlap. PR #793 touches
`60.mir_opt/var_reassign_ssa.spl` only.

## Runs 28-29 — sites 14 and 15 fixed; the lane now dies four steps later, at site 16

Lane both runs: `--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`,
same virgin root, worktree `agent-aee4c61a47998a6a9`. Each run cleared exactly one
blocker and exposed the next, so read them as one sequence.

### Run 28 — site 14 cleared, verbatim

```
  Stage 2: running bootstrap compiler sanity
  Stage 2: proving struct receiver/runtime capability
error: could not publish producer-bound Stage 2 parent receipts
```

**Zero `stage2-sanity-error:` lines** where run 27 had two, and the immutable
admission artefacts were published for the first time on macOS:

```
.../stage3/aarch64-apple-darwin/stage2-admitted/
  -r-------- admission.env  (2647 B)
  -r-x------ simple         (139,352,344 B)
```

Site 14's fix (`$(( ))` around `wc -c`, PR #800) is therefore verified by the
lane, not just by reasoning. What failed is the step AFTER admission: the
producer-bound parent receipts that seed the next run's trust root.

**Site 15, measured:** `publish-stage2-parent-receipts.shs` asserts
`[ "$(field candidate_path)" = "$candidate" ]` under `set -eu` with a bare `[ ]`,
so a mismatch exits 1 with no message. Three of four path fields matched; the
fourth did not — the caller passed the mutable build output
`.../stage2/<triple>/simple` while the receipt records the immutable
`.../stage2-admitted/simple`. The two are byte-identical
(`c85d2aa186e45c8a…`, `cp -p` + sha-verified), so the fix changes which path is
NAMED, not which bytes are bound. The existing producer test cannot catch this:
its fixture always writes `candidate_path=$candidate`, and no test invokes the
caller. Filed:
`doc/08_tracking/bug/stage2_parent_receipts_bound_to_preadmission_path_2026-09-13.md`.

### Run 29 — site 15 cleared, verbatim

```
Stage 2: admitted parent → bootstrap_main.spl
  Stage 2: running bootstrap compiler sanity
  Stage 2: proving struct receiver/runtime capability
error: Stage 2 did not publish its compatibility manifest
```

The parent-receipt error is gone. The new one is **site 16**, and it is the first
in this chain that is NOT a one-line fix:
`bootstrap-from-scratch.sh:3288` is fail-closed on a manifest whose only writer
(`driver_emit_phase2_compatibility_manifest_v1`,
`src/compiler/80.driver/driver_aot_native_output.spl:2051`) is **pure-Simple**,
while this lane's Stage 2 is built by the **Rust seed** (`mode: manual (seed →
bootstrap_main → bootstrap_main)`), and the seed implements the hook nowhere —
`/usr/bin/grep -rn "PHASE2_COMPATIBILITY_MANIFEST" src/compiler_rust/` returns
nothing. The build log carries zero `[M3 ledger]` lines and no manifest exists on
disk. The gate is unsatisfiable on this lane by construction. Two repairs are
possible and both move a contract, so it needs an owner:
`doc/08_tracking/bug/stage2_compatibility_manifest_unwritable_by_rust_seed_2026-09-13.md`.

### Where Stage 2 actually stands now

Built, both capability probes PASS (`bootstrap_stage2_struct_receiver`,
`bootstrap_stage2_positional_stage3_route`), sanity evidence verified, admission
receipt published, parent receipts published. Stage 3, the full CLI and Stage 4
were never reached; **nothing was deployed**. Four blockers were cleared in this
sequence (13 emitter, 14 `wc` padding, 15 caller path) and the fifth is filed.

Chain for whoever picks this up: site 15's parent receipts are exactly the
"parent authority" that
`scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs` requires to mint
the planner admission receipt, which `--resume-stage3-from-admitted` needs via
`SIMPLE_BOOTSTRAP_REASON_RECEIPT` (`bootstrap-from-scratch.sh:634-640`; resume
also forbids `--full-bootstrap`/`--deploy` and permits only `--jobs=1`). So
clearing site 16 should unlock Stage 3, and Stage 4 follows through
`bootstrap-strategy.sh`, which mints the lineage admission locally — no remote
scheduler — with `SIMPLE_BOOTSTRAP_STAGE4_QUARANTINE=1` forcing `deploy=0` so
`bin/release` is never touched.

### Run 30 (2026-09-13) — site 16 repaired; a NEW, earlier Stage-2 link blocker

Lane: `--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, virgin
evidence root, worktree `agent-a48e6e7adea865a52`, tip `6c801a7f309` (carries
PR #843), carrying the site-16 fix below. Cold Rust seed.

**Site 16 is fixed, and the fix is in the tree — but this run did not exercise
it.** Stage 2 never linked, so `stage2_status=1` and the manifest gate at
`bootstrap-from-scratch.sh:3291` (inside `if [ "${stage2_status}" -eq 0 ]`) was
not reached. What run 30 does prove about the fix is narrow and worth stating
exactly: the new library sources cleanly into the script under `set -eu` (the
run reached its own Stage-2 failure path and exited normally), and the gate's
own fixtures pass. The call site itself remains unexercised in a real lane.

Verdict, verbatim:

```
  diagnosis: 2 diagnostic line(s) found. First 5:
    | Build failed: link failed: ld: warning: -ld_classic is deprecated and will be removed in a future release
    | clang++: error: linker command failed with exit code 1 (use -v to see invocation)
PASS — 1 check(s), stage stage2 failed (exit 1) and said why
  warning: stage2 native-build failed (exit 1); Stage 3/full CLI unavailable
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Six undefined symbols at
`logs/aarch64-apple-darwin/stage2-native-build.log:2734-2748` —
`__sffi_enum_discriminant`, `module_surfaces_promote_reason`, `rt_cpu_is_aarch64`,
`rt_cpu_is_riscv64`, `rt_cpu_is_x86_64`, `rt_cpuid` — in three distinct classes
(runtime-bundle composition, a re-exported surface symbol, and a per-module SFFI
helper mangling gap). Run 29 linked cleanly at an earlier tip, so this is a
REGRESSION in the range between them, not a standing condition. Filed as site 17:
`doc/08_tracking/bug/stage2_link_undefined_cpu_probe_and_surface_symbols_2026-09-13.md`.

**Site 16's resolution** (design finding, since the bug record called for an
owner decision): both repairs the record proposed are dead on measurement. The
manifest's writer returns `m2-receipt-<reason>` at
`driver_aot_native_output.spl:415-418` unless the Phase-2 cache carries M2
reverse-reference receipts, which only `reverse_reference_receipt.spl` writes —
`grep -rl 'reverse_reference|current-admitted' src/compiler_rust/` is EMPTY. So
teaching the seed to emit the manifest means porting the whole M2
reuse-admission authority into Rust, and running the pure-Simple writer inside
the Stage-2 candidate against a seed-written cache fails at the same line. It is
also not a macOS problem: `can_full_bootstrap=0` ("Force manual bootstrap") pins
the admitted Rust seed as the Stage-2 producer on EVERY platform unless
`--stage2-parent` supplies an admitted pure-Simple release, so the gate was only
ever satisfiable on that producer. The gate is kept and scoped on a positive
producer fact, with schema checking the old `[ -f ]` never had, and a
`<manifest>.not-published` evidence record on the skip path. Stage 3 still
receives `MANIFEST_READ` and still admits ZERO Phase-2 reuse without a manifest
(verified by reading `phase_compatibility_read_manifest_io_v1`, which returns
`valid=false` on an absent file rather than aborting). Nothing was deployed.

### Run 31 (2026-09-13) — site 17 CLEARED; Stage 2 links; next blocker is K1 composition

Lane: `--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`, worktree
`agent-a887bdd4081fec17c`, tip carrying PR #873 (classes 2 and 3) over a main that
already carried PR #846 (class 1). Cold Rust seed, `Native build jobs: 5`.

**Site 17 is cleared, and this run proves it rather than inferring it.**
`/usr/bin/grep -c "Undefined symbols|__sffi_enum_discriminant|module_surfaces_promote_reason|rt_cpu_is_"`
over `logs/aarch64-apple-darwin/stage2-native-build.log` returns **0**. Run 30's
six undefined symbols are gone and Stage 2 produced a linked candidate binary —
the first time this lane has got past the link since run 29.

Verdict, verbatim:

```
exit:  2
  diagnosis: the PRIMARY log carries no diagnostic text, but a sibling log
             written by another sub-step of this stage does. The stage did
             not fail where the primary log was produced.
  real log:  .../stage3/aarch64-apple-darwin/stage2-sanity.env.frontend-failure.log
  1 diagnostic line(s) found there. First 5:
    | candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
PASS — 1 check(s), stage stage2 failed (exit 2) and said why
  warning: stage2 native-build failed (exit 2); Stage 3/full CLI unavailable
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

The failure has moved **past the link into the candidate's own sanity smoke**, and
the real diagnostic is:

```
PLUG-E-K1-POLICY: bootstrap backend composition admission failed
(selected policy 'llvm-cranelift'; 'unselected' means the fail-closed stub bound
instead of a committed K1 composition)
```

That is **site 18**, already filed by the #846 lane as
`doc/08_tracking/bug/stage2_sanity_positional_route_k1_composition_admission_failed_2026-09-13.md`.
It is a backend-composition admission gate, not a link or a symbol problem, and it
needs an owner the same way site 16 did. Stage 3, the full CLI and Stage 4 were
never reached; **nothing was deployed**.

Separately flagged by a peer lane and NOT what this run hit: a seed `native-build`
regression at origin/main producing `method 'len' not found on type 'i64'` on a
three-line hello world (lane F71). This run's smoke failed on the K1 policy line
instead, so the two are distinct; if a later rerun shows the `len`/`i64`
diagnostic, wait for F71's PR before re-attributing.

Origins for run 30's three symbol classes, with a fix commit each, are recorded in
`doc/08_tracking/bug/stage2_link_undefined_cpu_probe_and_surface_symbols_2026-09-13.md`
rather than repeated here.

## Runs 32-34 (2026-09-13, lane F72) — site 18 root-caused and CLEARED; site 19 exposed

Lane all three runs: `--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`,
worktree `agent-a0e562ca3e5681c38`, cold Rust seed each time.

### Run 32 — died before Stage 2: stale `Cargo.lock` (PR #893)

```
Building Rust seed compiler + runtime library...
error: rust-seed-build failed with exit 101
error: cannot update the lock file .../src/compiler_rust/Cargo.lock because --locked was passed to prevent this
```

`2cc924ff877` (18:49) dropped `"tempfile"` from the `simple-native-all` lock entry
while `native_all/Cargo.toml` still declares it as a dev-dependency, so every
hermetic `cargo build --locked --offline` seed build on every lane failed.
Restored (the one line cargo regenerates offline) as PR #893.

### Run 33 — site 18 reproduced with the diagnostic; verdict verbatim

```
  real log:  .../stage3/aarch64-apple-darwin/stage2-sanity.env.frontend-failure.log
  1 diagnostic line(s) found there. First 5:
    | candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
PASS — 1 check(s), stage stage2 failed (exit 2) and said why
  warning: stage2 native-build failed (exit 2); Stage 3/full CLI unavailable
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Probe log: `PLUG-E-K1-POLICY: bootstrap backend composition admission failed
(selected policy 'llvm-cranelift'; ...)` followed by an EMPTY line where the new
per-sub-check `k1-table:` dump should have been -- the dump itself was a victim
of the same miscompile. Candidate `stage2/aarch64-apple-darwin/simple.rejected`,
139,502,712 B, sha256 `769bed4ef539a9d4…`.

**Root cause, found in seconds with fixtures built by the seed, NOT by rebuilding:**
every enum `match` compiled by the seed's `native-build` (llvm AND cranelift)
took its LAST arm (`q_mixed=30,30,30` vs interpreter `10,20,30`). `df7ac9f6cc2`
(13:33) made typed matches call `rt_enum_check_variant(subject, enum_id, disc)`;
the seed's HIR lowering folds `enum_id` from the BARE type name while
`qualify_enum_runtime_names` later qualifies the constructor's `EnumUnit` name,
so ctor and check never agree (`id=0 -> 10`, `id=hash("Mixed") -> 10`,
`id=<stamped> -> 30`). `BackendKind.to_text()` is a `match self`, so the K1
validator's `name != entry.kind.to_text()` refused the composition. The bug
record's `34b96e29837` suspect is retracted. Corroboration: the same candidate's
`compile --format=smf` dies with `E-AST-SEMANTIC-UNHANDLED: TypeKind`.
Fix (seed, `native_project/mangle.rs`) + 2 Rust tests: PR #898. Fixtures rebuilt
with the fixed seed under both backends equal the interpreter.

### Run 34 — on landed main (`c1329f766a2`): site 18 CLEARED, site 19 exposed

`stage2-sanity.env`: `status=pass frontend_smoke_status=0
frontend_smoke_bootstrap0_raw_status=0 frontend_smoke_bootstrap1_ran=true
frontend_smoke_bootstrap1_raw_status=0`; `hello_world_positional_raw_status=0
probe=complete`; zero `PLUG-E-K1` lines. The positional hello-world builds and
runs on both bootstrap legs for the first time on macOS. Verdict, verbatim:

```
  real log:  .../stage3/aarch64-apple-darwin/stage2-receiver.log
  2 diagnostic line(s) found there. First 5:
    | error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
    | error: in-process native-build: Module surface registry graph promotion failed after phase 2: field composite_names of surface[0] logical=.Users.ormastes.simple..claude.worktrees.agent_a0e562ca3e5681c38.scripts.check.cert.redeploy_gate.fixtures.stage2_module_path_naming canonical=<same> package=.Users.ormastes.simple..claude.worktrees.agent_a0e562ca3e5681c38.scripts.check.cert.redeploy_gate.fixtures (scope sentinel promote=true, surfaces=2)
PASS — 1 check(s), stage stage2 failed (exit 3) and said why
  warning: stage2 native-build failed (exit 3); Stage 3/full CLI unavailable
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

The failure has moved one probe later, into `bootstrap_stage2_positional_stage3_route`
(the candidate compiling the module-path-naming fixture through its in-process
route). That is **site 19**. The two existing records for this message
(`stage2_module_surface_registry_graph_promotion_failed_2026-09-13.md`, FIXED by
`460aa9781cc`/`592041db98a` on Linux BOOT-7; `stage2_sanity_module_surface_registry_promotion_fails_2026-09-13.md`,
CLOSED as already-fixed) do not cover this: the tree carries both fixes and the
field named is `composite_names`. Not investigated here -- unrelated to K1 and
out of this lane's scope; filed as
`doc/08_tracking/bug/stage2_positional_stage3_route_surface_promotion_composite_names_2026-09-13.md`.
Rejected candidate preserved at `stage2-rejected/aarch64-apple-darwin/simple`,
139,504,696 B, sha256 `70f1a6517183d74c1a855f4761235dd2c62d52a63bfa3c36f7c5fb53b83f2703`.
Stage 3, the full CLI and Stage 4 were not reached; **nothing was deployed**.

### Run 35 — on landed main (`60c78b96789`, carries PR #903): site 19 CLEARED, Stage 2 ADMITTED, site 20 exposed

Command identical to run 34's, from worktree `agent-a73a6f3780a2bd75b`:
`sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`.
Native build jobs 5 (host CPUs 10), LLVM 18 at `/opt/homebrew/opt/llvm@18`.
Wall clock ~25 min end to end including a full Rust seed rebuild.

**This is the first macOS run to reach an admitted Stage 2.** Verdict, verbatim:

```
  Stage 2: running bootstrap compiler sanity
  Stage 2: proving struct receiver/runtime capability
PASS — 2 invariant(s) checked (producer identified, skip recorded), producer=rust-seed cannot publish the manifest; Stage 3 reuse disabled; evidence=.../stage3/aarch64-apple-darwin/phase2-compatibility.manifest.not-published
Stage 2 admitted; stopping before Stage 3 as requested.
```

`BOOTSTRAP_RC=0`. Admitted candidate
`<storage>/build/bootstrap/stage2/aarch64-apple-darwin/simple` (byte-identical to
`stage3/aarch64-apple-darwin/stage2-admitted/simple`), 139,504,568 B, sha256
`aed71b284fd897f6dff37ee2cda23056a32b4967c54d99468fea6aa8fc07124a`.
`stage2-sanity.env`: `status=pass ... checks_run=5`. Note this env does NOT carry
run 34's `hello_world_positional_raw_status` / `probe=complete` keys; the
positional Stage-3-route probe is recorded separately in `stage2-receiver.env`,
which reads **`status=pass probe_exit=0`** — that is the probe that failed on run
34 with `field composite_names of surface[0]`, and its fixture log
`stage2-sanity.env.frontend-bootstrap-0.log.stage2-module-path-naming` is present.

Site 19 root cause: NOT a new promotion instance and NOT a seed miscompile — a
regression of `460aa9781cc` reintroduced by `db127a8e8c4` (PR #873). The
repeat-promote post-condition ("a second `rt_transient_heap_promote` answers true
only for a value still owned by the dying scope") holds for a transient heap
STRING only, whose `RT_CORE_STRING_FLAG_TRANSIENT` promote clears
(`runtime_native.c:2474`). Every field in the 24-field loop is an ARRAY: promote
merely zeroes `transient_scope_id` (`:2493`) and `rt_core_transient_classify`
(`:2362`) never reads it, so the repeat promote answers true forever and the guard
was red on the first field of the first surface. Fixed in PR #903 by deleting the
per-field verdict and restoring the guard-free
`module_surface_promote_freeze_names`. `460aa9781cc`'s regression spec had been
RED at 2 of 3 examples on `origin/main` from `db127a8e8c4` until #903; it is now
4 of 4 and additionally pins the array-field loop.

**Stage 3 was NOT reached — new blocker, site 20.** Both routes fail rc=64 with
`bootstrap-policy-error: reason-receipt-required`: the prescribed
`--resume-stage3-from-admitted=<output>`, and a plain continuous
`--full-bootstrap --mode=dynload --jobs=half` run that reuses the admitted Stage 2
and hits the gate within seconds. The planner-admission producer needs a Stage-2
admission + provenance receipt pair that only a non-seed producer may publish —
which is what the Stage 2 verdict above states outright. No receipt was
manufactured. Filed as
`doc/08_tracking/bug/stage3_resume_receipt_chain_unreachable_from_seed_producer_2026-09-13.md`.
Stage 4 is downstream of Stage 3 and was therefore not attempted. **Nothing was
deployed.**

Run-34 repro note for future lanes: run 34's rejected candidate
(`70f1a651…`) was already gone — worktree `agent-a0e562ca3e5681c38` and its
`.simple/storage` had been cleaned — so no cheap native repro of site 19 was
possible. The diagnosis rests on the C runtime source, `460aa9781cc`'s gdb
measurement, and the regression spec. Interpreter-vs-native is not a usable
discriminator for this class at all: the seed's interpreter stubs the
transient-scope externs, so the guard cannot fire there and an interpreter pass
is vacuous.

## Runs 36-38 (2026-09-14, F74 round 3) — Stage 3 reached, then SEGV; nothing deployed

Seed: rebuilt by `--full-bootstrap` (3m50s); `git diff def2a9c30a1..origin/main --
src/compiler_rust` was 6 files +313/-2, so the previous lane's "seed parity" claim
did **not** hold for this range.

| run | tree | stage | outcome |
|---|---|---|---|
| 36 | `def2a9c30a1` | Stage 3 resume, threads=1 | **FAIL** after 91 min — 12x `imported enum \`X\` has no declaration owner` (HIR lowering, `src/app/cli/bootstrap_main.spl`). Fixed on main by #952. |
| 37 | `4f4d0e12832` | Stage 2 run 3 | **FAIL** — receiver probe `NOT_RUN: compiler.common.module_path_naming` |
| 37 | `4f4d0e12832` | Stage 2 run 4 | **ADMITTED**, 4 min warm. sha256 `f7c5c68b96597b11932beef38d5ef3359e7022249375e3fb5b2e9e023ab860ae` |
| 38 | `4f4d0e12832` | Stage 3, threads=5 (coordinator) | **FAIL** in 2 min — `SCV-E-ADMISSION: compile-event-journal-missing` (twice; its own remedy cannot reach the child under `env -i`) |
| 38 | `4f4d0e12832` | Stage 3, threads=1 (direct) | **FAIL** after 23 min — SEGV (signal 11, rc=139) in the HIR phase at unit 2 of 833, `current=compiler.driver.driver` |

**Stage 4 was never attempted. `bin/release/` is untouched. Nothing was deployed
and no artifact sha can be cited for Stage 3 or Stage 4 — there is none.**

Two positive results worth citing:

- **#952 is effective.** On `4f4d0e12832` the build log's count of
  `has no declaration owner` is **0** (was 12 on `def2a9c30a1`), and
  `app.cli.bootstrap_main` lowers successfully. The chain advanced past that
  defect into the SEGV above.
- **#955 is proven end to end.** Run 38's resume set **no** manual
  `SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT` and produced **zero**
  `planner-admission-v2-unbound` refusals — an unassisted resume passed the
  planner-admission gate and reached the build. That is the positive-path proof
  a synthetic receipt cannot give (every failure inside `verify_bound` surfaces
  as the same `unbound` line).

Threads finding: `--threads 1` is a default, **not** a correctness requirement —
`resume-stage3-from-admitted.sh:576-587` documents opt-in parallelism via
`SIMPLE_NATIVE_BUILD_THREADS` (`full` = online CPUs). Changing the *default*
would alter the "byte-for-byte pinned argv" contract and is a design decision,
not wiring. The coordinator route it selects is currently unusable on a cold
checkout — see `doc/08_tracking/bug/stage3_coordinator_route_cold_init_unreachable_under_env_i_2026-09-14.md`.

Logs preserved: `build/f74logs/stage3-run2-native-build.log` (run 36),
`build/f74logs/stage3-run5-native-build.log` (run 38).

## Runs 39-41 (2026-09-14, F75) — the Stage 3 SEGV is a STACK OVERFLOW, and the recursion is named

Runs 39-41 are not chain runs. They are three lldb replays of run 38's own
`stage3-command.transcript`, byte-for-byte except for cache/output/evidence
paths, done because the chain could not advance until the SEGV had a cause.
Each costs ~22 minutes and reproduces deterministically.

**Run 39 — crash class.** `build/f75logs/repro-lldb.log:12077-12085`:

```
Process 12291 stopped
* thread #1, queue = 'com.apple.main-thread',
  stop reason = EXC_BAD_ACCESS (code=2, address=0x16f603ff0)
  frame #0: simple`core::hash::sip::Hasher::write
  ->  0x1008bea38 <+0>:  stp  x26, x25, [sp, #-0x50]!
      sp = 0x000000016f604040
```

A **write** fault one word below `sp`, on the **first instruction of a function
prologue**, on the **main thread** — the stack guard page. This is a stack
overflow. It rules out the seed-codegen miscompile branch (which would fault
`code=1` at a small address) and the `rt_transient_heap_promote` runtime branch
(which would put an `rt_*` symbol at frame #0 as the cause rather than as the
next callee that needed a frame).

**Trap worth recording: `lldb --batch -o run -o 'bt N'` silently drops the
backtrace.** Run 39 printed the stop banner and exited with no frames at all.
The working form is lldb's crash-command list, `-k 'thread backtrace -c N'`,
and `-c` is mandatory — an unbounded `bt` on a stack this deep never returns.

**Run 40 — the recursion.** `build/f75logs/repro-lldb-2.log:12075-12238` shows
an exact four-symbol unit repeating for all 151 captured frames:

```
register_imported_symbol
  -> register_imported_symbol_inner                        (+1772 = module_import_registration.spl:367)
     -> register_materialized_enum_payload_dependencies    (module_reexport_materialization.spl:564)
        -> register_materialized_payload_named_dependency(_inner)   (:485/:491)
           -> register_imported_symbol                     (:537, materialize_enum = true)
```

This is **not** the cycle fixed on 2026-08-17 — that one ran through
`register_imported_type_methods`, whose breaker sits on no edge of this cycle.
And `register_imported_symbol`'s `registered_import_memo` is by its own comment
deliberately **not** a re-entrancy breaker ("A key is recorded only AFTER the
body returns"). The only guard on this cycle is the mark-on-entry in
`register_materialized_enum_payload_dependencies`.

**Run 41 — depth, to choose the fix.** If that mark-on-entry guard works, every
level is a distinct enum identity and depth is bounded by the enums reachable
from `driver.spl` — the tree declares 2,280. 8 MB / 2,280 is ~3.6 KB per
four-frame level, which these multi-KB functions can plausibly use, so
"finite but too deep" and "guard not taking effect" both fit the frames.
Depth ≈ 2,000-2,500 means the walk must be flattened to a worklist; depth far
beyond 2,280 means the Dict memo is not taking effect and the fix is a `[text]`
in-progress breaker, the same shape (and for the same documented
`rt_dict_contains` reason) as `imported_type_methods_in_progress`.
Full analysis, both candidate fixes, and why guessing between them is not
acceptable:
`doc/08_tracking/bug/stage3_hir_enum_payload_closure_stack_overflow_driver_2026-09-14.md`.

**No stack-size lever exists.** `--compile-stack-mib` is passed on the Stage 2
argv and has zero consumers in product code (`grep -rn stack_mib src` is empty;
it appears only in four shell scripts), and the Stage 3 argv omits it entirely.

**Harness fixes landed this round (neither unblocks the SEGV):**

- **#976** — the Stage 3 child runs under `env -i`, so the
  `SIMPLE_SCV_INVENTORY_COLD_INIT=1` remedy that the compiler's own
  `SCV-E-ADMISSION: compile-event-journal-missing` prescribes could never reach
  it; runs 36 and 37 failed identically with the variable exported. It is now an
  explicit, validated, opt-in single-variable pass-through baked into both the
  args digest and the transcript, gated by
  `check-bootstrap-stage3-scv-cold-init-passthrough.shs`. The coordinator
  (threads > 1) route is usable on a cold checkout again.
- **#977** — the Stage 4 twin of #955 was unbound: the same
  `bootstrap_planner_v2_verify` call serves `--resume-stage4-from-admitted`, so
  any lane on a private storage root would have been refused at Stage 4 exactly
  as Stage 3 was. Measured before/after on the real script,
  `planner-admission-v2-unbound` -> `resume-output-root-unresolvable`, i.e. the
  binding block was being skipped entirely. `check-bootstrap-stage3-receipt-autowire.shs`
  widened to 19 checks including a new executing Stage-4 row.
- Filed, not fixed:
  `doc/08_tracking/bug/stage3_declared_fallback_route_read_by_nothing_2026-09-14.md`
  — every Stage 3 receipt records `fallback_route=direct`, and
  `SIMPLE_BOOTSTRAP_STAGE3_FALLBACK_ROUTE` is read by nothing under `src/`.

**Stage 3 remains BLOCKED. Stage 4 was never attempted. `bin/release/` is
untouched, nothing was deployed, and no Stage 3 or Stage 4 artifact sha exists
to cite.**

## Runs 42-45 (2026-09-14, F75) — the HIR breaker, and a misread that must not calcify

### The fix, and the measurement that chose it

Run 42 (`build/f75logs/repro-lldb-4.log`) settled the Stage 3 SEGV. `sp` read at
frames 12/16/20/24 — one full cycle apart each — gives **624 bytes per
four-frame level, uniform**, over a stack region `0x16f604000-0x16fe00000`
(7.98 MB), i.e. **13,415 nested levels** of

```
register_imported_symbol -> register_imported_symbol_inner
  -> register_materialized_enum_payload_dependencies
    -> register_materialized_payload_named_dependency -> (repeat)
```

The cycle was not being broken. Fix (#987, `c56dd5004af`): a `[text]`
in-progress re-entrancy breaker keyed on `(imported_mod_name, dependency)` —
the method's own INPUT tuple, and a linear scan over an append-only array, so
it holds whatever the underlying cause. Spec executed, sabotage -> red -> green.

**The mechanism was over-claimed and is corrected** (#1003): the record first
blamed `rt_dict_contains` under-reporting. F77 could not reproduce that on the
interpreter (6 shapes green), there is a second gate on the cycle at
`module_import_registration.spl:363` keyed on an unstable `local_name`, and the
2,546 ceiling assumed `origin.module_name` is always the declaring module —
never verified. The depth measurement stands; the mechanism is open. Do not
cite that bug as evidence of a Dict defect.

### The misread — and what #1007's record should say

Runs 43-45 were reported as "Stage 3 dies silently with no verdict". **That was
wrong, and the premise of PR #1007's record is wrong with it.** The lane
**execs into `resume-stage3-from-admitted.sh`**, so `pgrep -f
'bootstrap-from-scratch'` misses it and returns 0. The run was alive throughout:
`31736 -> 38398 -> 38401`, worker at 59 min elapsed, **53:48 CPU, 5.0 GB RSS**.
The two follow-up launches that looked like empty runs were the output lock
**working**, and printing so:

```
mkdir: .../bootstrap.lock: File exists
error: bootstrap output is locked: .../bootstrap.lock
```

So #1007's VERDICT-on-exit trap and `check-bootstrap-lane-verdict-line.shs` are
worth keeping on their own merits — a lane that exits without a verdict line
*should* be caught — but **the incident that motivated them was a lane misread
by two sessions, not a harness fault.** The record should say that; leaving it
as written would put a phantom defect in the tracker and credit the guard with
catching something that never happened.

The recipe that would have prevented it is now in `.claude/rules/bootstrap.md`:
resolve `cat <out>.lock/pid`, `ps -p` it, walk `pgrep -P` to the worker, and
judge liveness from CPU/RSS — never from a process-name grep, and never from log
size (lane logs are fully buffered; a 0-byte `stage3-native-build.log` on a live
run means nothing has flushed).

### Two self-inflicted contaminations, recorded so the evidence is not over-read

While run 1 was building, this lane (a) `git checkout`ed the worktree onto the
F78 tip — a native-build reads source from cwd — and (b) launched a second
Stage 2 into the **same output root**, replacing
`stage3/<triple>/stage2-admitted/simple` (18:17) and
`stage3-planner-admission.receipt` (18:19) beneath a run that started 17:24. The
running process keeps its open inode and survived, but its on-disk inputs no
longer describe it.

Consequence, stated rather than glossed: **run 1 is contaminated.** It is
evidence for exactly one thing — its Stage 2 was built from the branch carrying
#987, and where the old crash was deterministic at ~23 min this run passed 59
min with 53 min of CPU, so the breaker got past `compiler.driver.driver`. It is
**not** a deployable artifact (pre-#1001/#1004) and must not be cited as the
chain result.

### Stage 2 twice admitted, first attempt each time

Both Stage 2 lanes this round admitted on the **first** try, with the
receiver-probe `NOT_RUN` flake absent and F76 not yet landed. That is luck, not
a fix — do not read it as the flake being gone.

**Still no deploy.** `bin/release/` is untouched and no Stage 3 or Stage 4
artifact sha is claimed. The deploy gate is three conditions, all recorded
before their results existed: Stage 3 reaching `done=2`; the F77 class probe
(`class Box: n: i64` + a method, `native-build --mode=dynload`) returning rc 0
rather than 139 under the Stage 3 binary; and the F78 spec
`test/01_unit/compiler/option_none_runtime_discriminant_spec.spl` green under
the same binary. Any failure is reported verbatim, and a MIR/Option frame is
explicitly not grounds to revert #987.
