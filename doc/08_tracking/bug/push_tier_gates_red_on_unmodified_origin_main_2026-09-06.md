# Three push-tier gates are red on an unmodified `origin/main`, so every push is a `--no-verify` push

**Date:** 2026-09-06 · **Status:** RECORDED (measured, not fixed) · **Measured at:** `a12a19eb775`
(worktree checkout of `origin/main`); the reporting session measured the same three at
`4699194f81e`. Host: macOS aarch64. No build was run — every command below is a shell
script or an already-deployed binary.

## Why this is one record

`config/check/must_check_gates.sdn` declares each of these as a `push`-tier row. Two are
`push_blocking: true`. They fail on a **pristine checkout with zero local modifications**,
so the failure is a property of `origin/main`, not of any lane's content. The consequence
is procedural and is the point of this record: a contributor who runs the pre-push hook
cannot push at all, so pushes are being made with `--no-verify`, which nullifies *every*
guard in the chain — including the tree-wipe guards that `.claude/rules/vcs.md` documents
as the only thing that has ever caught a `main` wipe. This is the same class of finding as
`doc/08_tracking/bug/vcs_md_overstated_push_guard_wiring_2026-09-01.md`, and the caveat
block at the top of `.claude/rules/vcs.md` § "Pre-push guards" already admits one such
gate (`push-rules-quick`); this record adds three more.

## Gate 1 — `push-rt-dual-implementation` (blocking): a baseline row for a symbol the gate cannot see

Manifest row (`config/check/must_check_gates.sdn:22`):

```
push-rt-dual-implementation, push, true, tree, "sh scripts/check/check-rt-dual-implementation-ratchet.shs", "no NEW single-lane rt_* symbol and no stale baseline row (rt_* must exist in BOTH the C and Simple lanes)"
```

Verdict, verbatim:

```
selftest: 6 fixture(s) passed
STALE baseline entries (no longer single-lane, or deleted — the baseline
no longer describes the tree, which is how a ratchet stops ratcheting):
  rt_phase_profile_record
FAIL — 2491 symbol(s) checked against 2492 baselined, 0 new, 1 stale
```

**This is the inverse of, not a duplicate of,
`rt_dual_ratchet_red_at_origin_four_unbaselined_symbols_2026-09-06.md`.** That record
reports `4 new, 0 stale` and resolves it by hand-adding four rows to
`scripts/check/rt_dual_implementation_baseline.txt`. One of those four —
`rt_phase_profile_record`, added at `rt_dual_implementation_baseline.txt:2519` as
`rust-only`, with the explanatory note at line 25 — is now reported STALE by the same
gate. The row went from absent-and-failing to present-and-failing without ever being
green.

Mechanism, established by reading the gate: `enumerate_lanes` scans exactly two roots —
`$root/src/runtime` for `*.c` (`check-rt-dual-implementation-ratchet.shs:89-90`) and
`$root/src/compiler_rust/runtime/src` for `*.rs` (`:98-99`), and the `--rev` path
archives exactly those two paths (`:267`). The only definition of the symbol in the tree is

```
src/compiler_rust/native_all/src/mem_snapshot_provider.rs:363:pub unsafe extern "C" fn rt_phase_profile_record(fd: i64, seq: i64, message: *const u8, message_len: i64) -> bool {
```

(re-exported at `src/compiler_rust/native_all/src/lib.rs:20`). `native_all/` is under
neither scan root, so the gate observes the symbol in **zero** lanes, reads that as
"deleted", and reports the baseline row as stale. The hand-edit baselined a symbol the
gate is structurally unable to see, so the row can never clear.

**Not established:** whether `native_all/` is *intended* to be in scope. Two readings are
open and this record does not choose between them — either the scan roots are too narrow
and should include `native_all/`, or `native_all/` is correctly out of scope and the
baseline row should simply be removed. Removing the row is a one-line change that turns
the gate green; adding the scan root would change the checked population from 2491 and has
not been measured. Neither was attempted here.

## Gate 2 — `push-sffi-v2-authority` (blocking): 12 of 46 sub-guards fail

Manifest row (`config/check/must_check_gates.sdn:18`):

```
push-sffi-v2-authority, push, true, tree, "sh scripts/check/check-sffi-v2-authority.shs", "all 46 SFFI v2 source-authority guards pass"
```

Verdict, verbatim (`sh scripts/check/check-sffi-v2-authority.shs`, rc=1):

```
sffi_v2_authority_ok=false
sffi-v2-authority: FAIL — 12 of 46 guard(s) failed
```

The 12, verbatim from the `sffi-v2-authority: FAIL <path>` lines:

```
scripts/audit/bootstrap-probe-args-sffi-authority.shs
scripts/audit/dashboard-remote-collector-sffi-authority.shs
scripts/audit/dashboard-schedule-collector-sffi-authority.shs
scripts/audit/interpreter-eval-ast-sffi-authority.shs
scripts/audit/log-sffi-authority.shs
scripts/audit/mono-cache-sffi-authority.shs
scripts/audit/mono-hot-reload-sffi-authority.shs
scripts/audit/play-session-store-sffi-authority.shs
scripts/audit/portal-server-sffi-authority.shs
scripts/audit/rt-time-contract.shs
scripts/audit/ssh-gcm-sffi-v2-authority.shs
scripts/audit/test-codegen-quick-sffi-authority.shs
```

Three representative failure messages, verbatim:

```
FAIL — @unsafe(reason, capabilities: [ffi]) declaration tag (expected 1, actual 0); rt_get_args call wrapped in unsafe(capabilities: [ffi]) (expected 1, actual 0)
FAIL — 5 assertion(s) checked, interpreter AST SFFI authority: unsafe_tagged_declarations expected 29, got 0
FAIL — 5 assertion(s) checked, quick codegen file-read authority: local_raw_extern_declarations expected 0, got 1; result_lift_import expected 1, got 0; result_lift_call expected 1, got 0; error_arm expected 1, got 0
```

The shape of every one of these is an audit that pins an exact expected count against the
source and now reads a different number — `expected 29, got 0` is not a marginal drift.
Existing SFFI-authority records
(`sffi_v2_authority_group3_silent_stale_count_audits_2026-09-02.md`,
`sffi_v2_authority_group4_silent_audits_2026-09-02.md`,
`sffi_contract_inventory_red_on_origin_main_2026-09-03.md`) describe the same family; none
of them enumerates this set of 12 at this sha, which is why it is recorded here.

**Not established:** the root cause of any individual sub-guard failure. Each was run only
through the aggregator; none was investigated. In particular, whether these are stale
expected-counts (the audit is wrong) or genuine authority regressions (the source is
wrong) is undetermined, and the two demand opposite fixes.

**Direct contradiction to flag.** `rt_dual_ratchet_red_at_origin_four_unbaselined_symbols_2026-09-06.md`
§ "Second gate, same shape" states it "audited every tree-scoped blocking push gate on a
pristine `origin/main` checkout", found the rt-dual ratchet and
`check-runtime-source-list-parity` red, and that "everything else passes".
`push-sffi-v2-authority` is a tree-scoped blocking push gate and does not pass. That
audit's scope claim is wrong, or it was run against a different tree; either way it should
not be relied on as a clean bill of health.

## Gate 3 — `push-dual-run-shadow` (advisory): a pair whose Simple candidate was never written

Manifest row (`config/check/must_check_gates.sdn:23`), `push_blocking: false` — this one
records a verdict on stderr rather than blocking, so it is not part of the `--no-verify`
argument above and is recorded for the underlying defect instead.

Verdict as reported to this session: `FAIL — 40 pair(s) checked, 1 divergent`. The
40-pair population is confirmed independently here —
`/usr/bin/grep -rn --include='*_spec.spl' -E '^# @dual_pair: ' test/` returns exactly 40.

**The premise this session was handed was wrong, and the corrected finding is sharper.**
The report was "`to_lower_ascii` has no Simple twin anywhere under `src/`". In fact the
module exists:

```
src/lib/common/text_ascii.spl   (28 lines)
```

It defines exactly one function, `to_upper_ascii` (`:17`), and its header comment describes
it as the "C-MIG-0035 companion" for `rt_text_to_upper_ascii`. There is no
`to_lower_ascii` in it. But the pair registration names one:

```
test/01_unit/lib/common/spec/dual_run_tranche_c_spec.spl:24:# @dual_pair: to_lower_ascii_vs_rt_text_to_lower_ascii mode=value-legacy ref=rt_text_to_lower_ascii cand=std.common.text_ascii.to_lower_ascii
```

and the same spec imports it at `:33`:

```
use std.common.text_ascii.{to_lower_ascii}
```

So the spec registers a dual-run pair against, and imports, a symbol that does not exist.
`git show 4699194f81e:src/lib/common/text_ascii.spl | grep -c to_lower` returns `0`, and
`git log --oneline -- src/lib/common/text_ascii.spl` shows three commits, all concerning
`to_upper_ascii` — the lower twin was never written and then removed; it was never there.
The tranche C header (`:6-18`) explains the selection method that admitted the pair: the C
symbol is registered in the interpreter's extern dispatch and has no pure-Simple twin, i.e.
the pair was registered as *work to be done* and the Simple side was never landed.

Every other `to_lower_ascii` in the tree is unrelated: a `static fn` inside `Trace32Parser`
(`src/app/debug/remote/protocol/trace32.spl:365` and two `src/lib/**/debug/remote/protocol/trace32.spl`
copies), and re-exports of the *extern* `rt_text_to_lower_ascii`
(`src/lib/common/string_core.spl:531-534` wraps it as `text_to_lower_ascii`, which is a
call to C, not a twin of it).

**Not established, and it matters:** why the gate reports this as `1 divergent` rather than
a load error. An unresolvable import should fail to load, not produce a value mismatch. The
gate was not re-run here — per this session's memory, `simple test` on this macOS host is
load-only, and the deployed seed predates the tip (see
`deployed_seed_predates_tip_verification_cap_2026-09-06.md`). The mechanism by which a
missing symbol becomes a divergence rather than an error is unexplained and should not be
assumed benign; it may indicate the gate's parser treats a failed pair row as a mismatch.

## Adjacent, and NOT a push-tier gate: `check-stage-binaries-runnable`

`.claude/rules/vcs.md` describes this as an advisory guard. It is neither advisory nor
blocking: `grep -rn "stage-binaries-runnable" config/ scripts/check/check-push-must-pass.shs`
returns **nothing**. It has no manifest row and no dispatch case, so it runs on no push at
all. It is recorded here only because its failure mode has changed and the standing record
is now stale.

Verdict, verbatim (`sh scripts/check/check-stage-binaries-runnable.shs`, rc=1):

```
FAIL — 12 invocation(s) executed across 4 binary(ies), 4 crashed/failed/wrong-arch: bootstrap/stage1/simple:native-build(fail,rc=1) bootstrap/stage2/simple:native-build(fail,rc=1) bootstrap/stage3/aarch64-apple-darwin-macho/simple:native-build(fail,rc=1) bootstrap/stage3/simple:native-build(fail,rc=1)  (1 foreign-triple scoped artifact(s) skipped, not counted as passing:bootstrap/stage3/x86_64-unknown-linux-gnu/simple:foreign-triple(elf-x86_64) )
```

**The failure mode is different from the filed one.**
`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md` and the vcs.md bullet
both describe rc=139 SEGV on **both** `compile` and `native-build`. Measured now: `compile`
succeeds on all four (12 invocations, only 4 offenders, all of them `native-build`), and
`native-build` exits rc=1 with a clean diagnostic, not a signal. Reproduced directly
against a three-line hello world:

```
$ ./bootstrap/stage3/aarch64-apple-darwin-macho/simple native-build /tmp/.../h.spl -o /tmp/.../h
error: bootstrap_main cannot emit a seed-wrapper fallback for /tmp/.../h
error: rebuild with the full Simple driver so native-build uses real Simple lowering/codegen
```

That is a deliberate refusal path in `bootstrap_main`, not a crash. The binaries were
replaced between 08-18 and now; the SEGV is gone and a different, self-described defect is
in its place. The 08-18 record should not be closed on the strength of the SEGV being gone,
and this gate is still red.

**Not established:** which commit replaced the stage binaries, and whether the refusal is
correct behaviour for a bootstrap-cli artifact (in which case the gate's expectation is
wrong) or a genuine capability regression. Neither was investigated. Note also that
`.claude/rules/vcs.md`'s claim that repair "needs a bootstrap redeploy" is unchanged, and a
redeploy was forbidden for this session.

## What was NOT done

No fix, no baseline regeneration, no gate edit, and no build of any kind — no bootstrap, no
stage self-compilation, no `cargo`. This record is filing only.
