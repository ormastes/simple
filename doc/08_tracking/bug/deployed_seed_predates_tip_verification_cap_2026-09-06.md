# The only deployed Simple binary predates the tip, so a whole class of gate cannot speak — and the rebuild that would fix it is prohibited

**Date:** 2026-09-06 · **Status:** RECORDED (verification cap, not a code defect) · **Host:** macOS aarch64.
No build was run; this record exists precisely because one could not be.

## The gap

The only locally deployed Simple binary:

```
$ readlink -f bin/simple
/Users/ormastes/simple/src/compiler_rust/target/bootstrap.generations/502da3d0c33802d763006c85e3bb2f2a3f4eb1f9cf3caf20dd9de0addbbcd379-6de58bd16dd0abf4f8ef3af8f878ec155913ef74819cf21014ab757815b0b45d/simple
$ stat -f '%z %Sm' "$(readlink -f bin/simple)"
130402384 Sep  5 20:01:33 2026
```

`src/compiler_rust/target/bootstrap/simple` is the same artifact (same size, same
timestamp). It was built **2026-09-05 20:01:33**. The tip under assessment,
`a12a19eb775` (`origin/main`, merge of PR #398), landed 2026-09-06. Everything merged in
between is invisible to this binary.

## The two symptoms, and why neither is a defect

Both were reported to this session as failures. Both are artifacts of the stale binary,
and this record's purpose is to stop them being re-filed as bugs.

**1. `frontend_offload_switch.spl` fails to parse** with `expected Comma, found Colon` on
an `auto:` label. The construct is present and well-formed at this sha:

```
src/compiler/00.common/structural_contracts/frontend_offload_switch.spl:24:    auto: bool                # true only for "auto"; mode is the evidence-less floor (CpuReference)
```

and is used as a named field at `:47`, `:87` and read at `:109`. The file is a normal
struct declaration. A parser that rejects `auto:` is a parser that predates whatever made
`auto` acceptable in that position.

**2. `posix_spec.spl` fails 3/3 with `unknown extern rt_fd_pread` / `rt_fd_pwrite`.** Both
symbols are implemented at this sha:

```
src/compiler_rust/runtime/src/value/sffi/file_io/descriptor.rs:241:pub unsafe extern "C" fn rt_fd_pread(fd: i32, buffer: *mut u8, len: i64, offset: i64) -> i64 {
src/compiler_rust/runtime/src/security_runtime.rs:101:        | "rt_fd_pread"
```

(`rt_fd_pwrite` is the sibling, documented at `descriptor.rs:266` as sharing the return
convention.) The spec is `test/01_unit/lib/nogc_async_mut/sosix/posix_spec.spl`. The
symbols exist in the source; they are absent from the *binary*, which is what "unknown
extern" reports. Per `.claude/rules/vcs.md`, the `rt_fd_pread`/`rt_fd_pwrite` pair is the
SOSIX lane's recent addition — i.e. it landed after 09-05 20:01:33 by construction.

## The cap, which is the actual finding

The two symptoms are disposable. The structural fact behind them is not: **any gate whose
verdict requires executing a Simple binary cannot render a verdict on the current tip.**
That is not a slow gate or a flaky gate; it is a gate that is silent, and a silent gate is
indistinguishable from a green one to anyone reading a summary.

Concretely, this is why `push-dual-run-shadow` carries `push_blocking: false` in
`config/check/must_check_gates.sdn:23`, with the manifest's own note: "advisory: needs a
runnable `bin/simple`, which not every push host has". The same dependency affects
`check-unbacked-extern-ratchet.shs` and `check-outline-parse-terminates.shs`, which
`.claude/rules/vcs.md` § "Honestly NOT wired" already lists as ERRORing "without a deployed
`bin/simple`, which most push hosts lack". This record adds the case that had not been
stated: a host *with* a deployed binary is not thereby covered, because the binary can be
older than the tree and produce confident, wrong answers rather than an honest ERROR. A
stale binary is worse than a missing one — the missing case fails closed, the stale case
does not.

## Why the cap cannot currently be lifted

Closing it requires a bootstrap rebuild and redeploy. For this session that was
categorically forbidden: an open memory defect OOM-crashed nine concurrent sessions, and no
bootstrap, `scripts/bootstrap/*`, stage1/2/3 self-compilation, or `cargo` build/check was
permitted.

**Not established:** the identity of that memory defect as a filed record. `ls
doc/08_tracking/bug/ | grep -i "oom\|memory"` returns several OOM records
(`bootstrap_stage1_entry_closure_spin_oom_2026-07-17.md`,
`bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`,
`bootstrap_stage4_ast_hir_overlap_memory_2026-07-27.md`,
`bootstrap_low_memory_positional_bridge_circularity_2026-07-26.md`) but none dated
2026-09-05/06, and none was matched to the crash described. The prohibition is therefore
recorded here as an operational constraint reported to this session, **not** as a
cross-reference to a verified record. If the nine-session OOM is real and unfiled, that is
itself a missing record and a blocker on everything above.

## Distinct from the existing stale-seed record

`doc/08_tracking/bug/file_read_nullable_provider_deployed_seed_stale_2026-08-22.md` is the
same *class* and not the same finding. That record is scoped to one provider: the deployed
seed predates an interpreter fix to `rt_file_read_text`'s nil-on-failure contract, so the
`file_read_result` facade "must not yet be cited as cross-lane verification evidence", and
it prescribes re-verifying that one contract after redeploy. It is a symptom record with a
named symptom. This record is about the general cap and about the fact that the remedy is
currently prohibited — which is new, and which is what makes the cap persistent rather than
a scheduling detail.

## What was NOT established

- **No measurement of the gate population.** How many gates in
  `config/check/must_check_gates.sdn` actually depend on executing `bin/simple` was not
  counted; three are named above from existing documentation, not from a survey.
- **The parse failure was not reproduced here**, nor was `posix_spec.spl` run. Both
  symptoms are taken as reported; what is independently verified at `a12a19eb775` is that
  the source constructs and runtime symbols they complain about *exist*, which is the half
  that matters for the "not a defect" conclusion.
- **No claim that the 09-05 binary is the newest obtainable one.** Only the local deploy
  was inspected; whether a fresher artifact exists elsewhere (CI, another host) was not
  checked.
