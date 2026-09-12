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
