# `push-no-direct-rt` (BLOCKING push gate) is red on `origin/main` since 2026-09-12

- Status: OPEN (2026-09-12) — observed, not repaired; owner: whoever landed the 262 new sites
- Component: `scripts/check/check-no-direct-rt.shs` ratchet, baseline
  `scripts/check/no_direct_rt_baseline.txt` (6072, tightened 2026-09-07)

## Observation

```
sh scripts/check/check-no-direct-rt.shs --roots src --rev origin/main   # 9e4f1133fe5
FAIL — forbidden direct rt_* count 6334 exceeds baseline 6072 (roots=src, src=6334),
       extern_decls=6613; top offenders: src/compiler/35.semantics/rt_criticalit...
```

At `7352f99898c` (PR #538, the previous base) the same command PASSes at 6072.
The 262 new direct `rt_*` call sites arrived with the 2026-09-12 merges #541
(`work/damage-spec-lane-aware-2`), #542 (`land/jit-symbol-manifest-read`) and
#543 (`land/web-render-chrome-parity`), which landed through PRs — the PR
checks do not run this push-tier gate, so a hooked `git push` of any branch
based on the new `main` is refused regardless of its own content. This is the
third push-tier gate found red on `main` this week (see
`push_gates_red_on_main` in the 2026-09-12 session memory: guard-wiring and
runtime-source-list parity were the other two, unblocked in PR #544).

## Consequence for landing

Branches in this session are based on `7352f99898c` (green) and pushed with
the hook running; the ruleset's strict up-to-date requirement is then satisfied
server-side by `gh pr update-branch`, which does not run local hooks. That is a
workaround, not a fix.

## Fix direction

Either migrate the 262 sites to their typed `std` aliases (the ratchet's
purpose) or, as a reviewed step, raise the baseline WITH the list of offending
files recorded here — never silently. `check-no-direct-rt.shs` prints the top
offenders; `src/compiler/35.semantics/rt_criticalit*` leads the list.

---

## Reconciliation (agent K, 2026-09-12) — the manifest and the hook already agree

Two different ids were being conflated. `push-must-check: TODO no-direct-rt` is
**not** the push gate being skipped:

- It is emitted by `validate_ledger_text` at
  `scripts/check/check-push-must-pass.shs:260`, which prints one `TODO <id>`
  line for every **bootstrap-tier ledger row** whose status is `todo`. All 53
  rows of `doc/08_tracking/check/must_check_db.sdn` are `todo`, so 48 such
  lines print on every push. Reproduced directly:
  `sh scripts/check/check-push-must-pass.shs --self-test` ends
  `push-must-check: PASS — 20 ledger fixtures checked` after emitting
  `TODO interpreter-startup-parity`, `TODO rust-go-benchmark-parity`, …
  The ledger header says so in as many words: "TODO is visible debt, never PASS."
- The push-tier row is `push-no-direct-rt` (different id). It has its
  exact-match dispatch case at `check-push-must-pass.shs:452`, and it RUNS —
  `run_push_gate` at `:470`, blocking, in **delta mode**:
  `--roots src --rev "$_ref" --baseline-rev "${_range%%..*}"`.
  `--baseline-rev` is real (`check-no-direct-rt.shs:106`), so the row is a
  ratchet against the outgoing range's own base, not against the frozen file.

Measured here at `28a96c436b9` (worktree `/home/yoon/dev/simple-wiring`):

```
# as the hook runs it (delta)
sh scripts/check/check-no-direct-rt.shs --roots src --rev HEAD --baseline-rev origin/main
PASS — 16530 file(s) scanned (roots=src, src=6334), forbidden=6334,
       extern_decls=6613 (base origin/main: 6334)

# standalone / bootstrap / release lane (tracked baseline file)
sh scripts/check/check-no-direct-rt.shs --roots src
FAIL — forbidden direct rt_* count 6334 exceeds baseline 6072 (roots=src, src=6334),
       extern_decls=6613; top offenders: src/compiler/35.semantics/rt_criticality_validation.spl:155
       src/compiler/70.backend/backend/llvm_backend.spl:83 src/os/apps/sshd/ssh_session.spl:63 …
```

`scripts/check/no_direct_rt_baseline.txt` still reads **6072** (last touched by
`ba7626d2508`, "tighten no-direct-rt baseline 7776 -> 6072, the measured
reality"). It was **not** silently bumped to 6334 by the 2026-09-12 gate-sync
commit.

### Decision

- `push-no-direct-rt` stays `push_blocking: true`. Delta mode is the honest
  reading: a branch that adds no new direct `rt_*` sites is admitted, and one
  that adds any is refused. No manifest or dispatch change is needed — the two
  surfaces already agree.
- **No re-baseline.** The 262 new sites are real debt. They stay visible as the
  standalone FAIL above and as the bootstrap-tier `no-direct-rt` row, which is
  already `push_blocking: false` in the manifest with ledger status `todo`,
  owner `tooling-team`.
- Evidence attached rather than erased: the full offender dump (1,016 lines) is
  `K_no_direct_rt_offenders.txt` beside this file, produced with
  `sh scripts/check/check-no-direct-rt.shs --roots src --offenders <file>`.

The "Fix direction" above is unchanged and still owned by whoever landed the
262 sites; what changes is that nothing is silently skipped today.

## Still red one day later, and confirmed not lane-caused (BOOT-6, 2026-09-13)

On `work/bootstrap-full-4-2026-09-12` at `4e8e6426a3c` (base `7b93832c115`):

```
FAIL — forbidden direct rt_* count 6328 exceeds baseline 6072 (roots=src, src=6328),
       extern_decls=6646; top offenders: src/compiler/35.semantics/rt_criticality_validation.spl:155
       src/compiler/70.backend/backend/llvm_backend.spl:83 src/os/apps/sshd/ssh_session.spl:63
       src/lib/nogc_sync_mut/io/tcp.spl:62 src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl:59
```

6328 vs the 6334 recorded above — the same top-five offenders, so this is the
same unrepaired debt, not a new one.

**Zero-delta proof for this lane**, using the guard's own call-site regex
(`RT_RE='^[^#]*\brt_[a-z0-9_]*\('`, which by construction ignores comments)
against committed content at both endpoints:

| file | base `7b93832c115` | head `4e8e6426a3c` |
|---|---|---|
| `src/compiler/70.backend/backend/llvm_backend_tools.spl` | 58 | **58** |
| `src/compiler/80.driver/driver_aot_native_output.spl` | 10 | **10** |

Those are the only two `src/` files BOOT-6 touched, and neither moves. The one
added line mentioning `rt_` is a comment, which `^[^#]*` excludes anyway. So the
red is inherited, and BOOT-6 reports this gate as FAIL-with-zero-delta rather
than claiming a pass or regenerating the baseline — regenerating would erase
256 sites of real debt, which is exactly what the ratchet exists to prevent.
