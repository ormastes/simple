# Landing record — shared-tree sync against origin, 2026-08-17

Second sync pass of the day. The previous lane
(`doc/09_report/landing_91_commit_backlog_2026-08-17.md`) pushed from an
**isolated** worktree, so the shared tree at
`/mnt/data/worktrees/simple-main` was never rebased and still reported 94-95
commits ahead. As predicted in that record, almost all of them were already at
origin under rebased shas.

## Range

| item | value |
|---|---|
| origin/main at start (re-derived, not taken from a brief) | `a83396620fde3052ff2a5b20f7b96e1486250de5` |
| shared tree HEAD | `88d1078f3ef8b7f146a87b7f6531df0bdfc22e52` |
| ahead / behind at start | **95 ahead / 362 behind** |
| prepared range (verified, guarded) | `a83396620fde..6f18828fb5ff5da64310d1c9412947d5f34fa037` |
| commits prepared | **2** |
| origin/main after re-fetch at push time | `36a5a0e82912b40ba0afc820c7510001f6d8d6d4` |
| commits actually pushed by this lane | **1** (this record) |

### Outcome correction — the 2 commits were absorbed mid-flight

Origin moved between the guard run and the push (`a83396620fde` ->
`36a5a0e8291`), exactly as expected on this remote. On rebasing onto the new
tip, **both** prepared commits were reported `skipped previously applied` — a
parallel lane landed the same work in the interval. So this lane's push carries
only the landing record.

That was verified **by content**, not by the skip message:

| check at `36a5a0e8291` | result |
|---|---|
| `rt_clear` Dict arm, C runtime (`rt_core_as_dict(receiver)`) | **present (1)** |
| `rt_clear` Dict arm, Rust runtime (`crate::value::dict::rt_dict_clear(receiver)`) | **present (1)** |
| `scripts/check/check-dict-clear-receiver-dispatch.shs` | **PRESENT** |
| all 3 bug records | **PRESENT** |
| blob-identity of `runtime_native.c`, `collections.rs`, the guard `.shs` vs my prepared tip | **all 3 IDENTICAL** |
| `1983ecdbceb` int61 `from_int` range check | **intact (1)** |
| duplicate `fits_inline_int` | **absent (1 definition)** — the superseded commit was correctly not landed by that lane either |

The work is at origin and byte-identical to what was verified here. Nothing was
lost and nothing was rewound; the guard verdicts below were measured against the
prepared range and remain the evidence that this content was safe to land.

All work was done in an isolated `git worktree add --detach`
(`/mnt/data/wt-land-2947111`). The shared working tree was never rebased,
never checked out, and never edited — ~16 lanes hold live uncommitted work in
it. `git config core.bare` on the shared repo was read **immediately after**
the `worktree add` and returned `false`; the known `core.bare=true` corruption
did not occur. The ~392 stale worktrees reported by `git worktree list` were
left untouched.

## The 2 commits prepared (now at origin via a parallel lane)

```
6f18828fb5f docs(bug): native-trailing-default guard is a three-stage red, none of it the trailing-default lane
440da9b271c fix(runtime): receiver-dispatch Dict in rt_clear so Dict.clear() is not inert
```

Files (7 total, `git diff-tree`-confirmed, **4 A / 3 M / 0 D**):

```
A doc/08_tracking/bug/native_trailing_default_param_guard_three_stage_red_2026-08-17.md
A doc/08_tracking/bug/stage3_dict_clear_no_dict_branch_in_rt_clear_2026-08-17.md
A doc/08_tracking/bug/stage3_nil_coalesce_owner_enum_handle_stale_runtime_2026-08-17.md
A scripts/check/check-dict-clear-receiver-dispatch.shs
M src/compiler_rust/runtime/src/value/collections.rs
M src/runtime/runtime_native.c
```

(plus this record and its companion offender list, committed separately.)

The substantive fix adds the missing **Dict arm to `rt_clear`** in both parallel
runtimes. `.clear()` is routed by method NAME with no receiver type, so
`Dict.clear()` landed in `rt_clear`, which dispatched Array and text only — a
dict receiver fell through to `rt_refuse_non_text_receiver` (and, earlier, to a
silent no-op). `SymbolTable.reset_module()` is eight `Dict.clear()` calls plus
two scalar resets, so the dicts cleared nothing while `next_symbol_id = 0` took
effect, leaving stale symbol names pointing at reused ids.

## Drop count

**93 of 95 dropped as already-upstream or superseded. 1 deferred. 2 landed.**

| bucket | n | method |
|---|---|---|
| dropped, exact patch-id equality | 42 | `git cherry origin/main HEAD` reported `42 -` / `53 +`; `git rebase` independently reported **42** `skipped previously applied commit` lines — two mechanisms agreeing on the same number |
| dropped, went empty on apply | 49 | rebase produced an empty pick (`--empty=drop`) |
| dropped, superseded (would not compile) | 1 | `4be6951d019`, see below |
| **deferred** | 1 | `13636027582`, see below |
| **landed** | 2 | above |

### Content-verified drop sample

A subject or a sha proves nothing — a commit was announced as a fix today whose
tree was byte-identical to its parent. Blob-identity checks (`git rev-parse
<rev>:<path>` equality) against origin:

| commit | path | result |
|---|---|---|
| `d03b800c7d6` | `src/lib/nogc_sync_mut/test_runner/test_runner_single.spl` | **IDENTICAL blob** |
| `bcebe89b831` | `src/app/llm_caret/main.spl` | **IDENTICAL blob** |
| `91f2002ec5a` | `src/compiler/20.hir/hir_lowering/module_surface.spl` | **IDENTICAL blob** |

`d03b800c7d6` is worth naming: `.spipe/unstable_test_mode/state.md` at origin
still claims it is **NOT landed** (`make_result_from_output` = 0 at origin).
That claim is now stale — the blob is byte-identical at origin, so the
single-spec classification fix **is** landed.

## The one commit dropped as superseded — caught by ablation, not by any guard

`4be6951d019 fix(runtime): make the Rust test suite compile again` touches only
`src/compiler_rust/runtime/src/value/core.rs`, adding `INLINE_INT_BITS` and
`fits_inline_int`. Origin **already has both** — and additionally wires
`fits_inline_int` into `from_int` (the landed `1983ecdbceb`), which this commit
never did. Rebased on top, the result defined both items **twice in one `impl`
block**:

```
$ git show <tip>:.../core.rs | grep -n 'pub const fn fits_inline_int\|pub const INLINE_INT_BITS'
304:    pub const INLINE_INT_BITS: u32 = 61;
324:    pub const fn fits_inline_int(i: i64) -> bool {
335:    pub const INLINE_INT_BITS: u32 = 61;      <-- duplicate
354:    pub const fn fits_inline_int(i: i64) -> bool {   <-- duplicate
```

git cannot see this: both sides are pure additions at different offsets, so
every text-and-tree guard passes. Proven by **ablation**, rc read from a
variable on the line after each command, never through a pipe:

```
runtime crate, WITHOUT the dropped commit: rc=0   errors=0
runtime crate, WITH    the dropped commit: rc=101 errors=3
  error[E0592]: duplicate definitions with name `INLINE_INT_BITS`
  error[E0592]: duplicate definitions with name `fits_inline_int`
  error: could not compile `simple-runtime` (lib) due to 2 previous errors
```

The ablation edit was reverted; `git status --porcelain` returned 0 modified
paths afterwards. Its stated goal ("make the Rust test suite compile again") is
already met at origin by a strictly stronger change, so dropping it is forward
progress. Note its doc comment also carried a **stale claim** — that `from_int`
"shifts unconditionally and never heap-boxes" — which origin has already
falsified; landing it would have reintroduced a retracted statement.

## Deferral list (1)

**`13636027582 fix(bootstrap): let allowlisted print-only probes reach Stage 3`
— DEFERRED. Owner: the stage-3 admission lane.**

Reason: the conflict lands inside the **stage-3 admission args-hash block**
(`stage2_args=$(bootstrap_stage3_args_sha256 ...)`) of
`scripts/bootstrap/resume-stage3-from-admitted.sh`, and the commit also touches
both files the standing instruction designates as defer-on-conflict
(`scripts/bootstrap/bootstrap-from-scratch.sh`,
`scripts/check/lib/bootstrap-stage3/authority.shs`). A sloppy merge there
silently weakens a provenance gate.

Verified already-landed by content, so the deferral costs nothing real:

- `doc/08_tracking/bug/stage3_env_gated_probes_unreachable_2026-08-17.md` — **PRESENT at origin**
- `scripts/check/check-stage3-diagnostic-env-passthrough.shs` — **PRESENT at origin**
- origin's `authority.shs` carries **6** diagnostic-env-passthrough hits (landed as `f2531d57bdf`)

The only unlanded remnant is the **older** form that hardcodes `--backend
cranelift`. Landing it would have **reversed** origin's transcript-derived
`backend` / `threads` / `compile-stack-mib` / `progress` derivation and dropped
its admission-receipt and preflight-immutability verification — i.e. it would
have been a revert wearing a fix's commit message.

## Conflict resolutions

19 conflicts across 13 commits. **No `-X ours`, no `-X theirs`, no blind
`--skip`.** Both the `-` and `+` sides were read every time. 12 were mechanical:
origin's side was a proven **superset** of the incoming (diff against the
incoming side had zero deleted lines), so origin's content already contained the
commit's contribution. The 7 genuinely divergent ones:

| file | commit | resolution |
|---|---|---|
| `src/app/cli/cli_helpers.spl` | `df0b2ca8747` | Both sides add the **same two** `--unstable` / `--no-unstable` help lines, differing only in prose wrapping. Origin's kept; no intent lost. |
| `scripts/check/check-build-outcome-reason-attribution.shs` | `999a794329e` | Add/add of the same new guard. Origin's differs only by adding a `SIMPLE_BINARY`/`SIMPLE_BIN` override; **both retain `[ -x "$SIMPLE" ] \|\| err`**, so no fail-open was introduced. Origin's kept as the superset. |
| `.spipe/unstable_test_mode/state.md` | `91fa3cce4d4`, `4aad4d47c88` | The incoming 3 lines are **explicitly retracted** by a later origin CORRECTION section ("the attribution is wrong" — stale seed, not a parser defect). Keeping both would reinstate a retracted claim, so origin's supersession was taken. |
| `doc/08_tracking/bug/stage3_export_origins_linear_module_lookup_2026-08-17.md` | `c89ca8acfc6` | Incoming is the **placeholder** table (`see ablation log`, `—`); origin has the filled-in measurement (1012ms -> 794ms, `ORIGIN_COUNT` 72, `ORIGIN_SET_VERDICT: IDENTICAL`). Same finding, later completed. |
| `test/01_unit/.../stage3_hir_lowerer_reuse_contract_spec.spl` | `4e42ce0d32d` | Same interpolation defect fixed two ways. Origin's is the prior lane's landed `810018b7a11` and is **stricter** (full anchor via brace concatenation vs a truncated prefix). |
| `scripts/bootstrap/resume-stage3-from-admitted.sh` | `13636027582` | **DEFERRED** — see above. |

Note on `rerere`: `rerere.enabled=true` is set globally in this repo and
auto-applied cached resolutions from other lanes. Every such resolution was
re-verified here against both index stages rather than trusted; the first one
(`interp_array_param_indexing_2026-07-03.md`) was confirmed to be an
additions-only superset of the incoming side (+364/-0) before being accepted.

## Anti-revert — hunk by hunk on `src/**` and `scripts/**`

The whole pushed range on `src/**` and `scripts/**` is **pure addition**: one new
guard script, plus added Dict branches and comments. The single deleted line in
the range is a reworded doc comment (`/// clear: empty an ARRAY in place` ->
`... an ARRAY or a DICT ...`). No functional deletion anywhere.

Specific items named as must-not-rewind, verified **by content at the pushed
tip**:

| item | check | result |
|---|---|---|
| `1983ecdbceb` int61 `from_int` range check | `grep -c 'if Self::fits_inline_int(i)'` in `core.rs` | **1** (intact) |
| `1983ecdbceb` `from_wide_int` heap boxing | `grep -c 'fn from_wide_int'` | **1** (intact) |
| `1983ecdbceb` transfer / value_ops halves | `git diff` vs origin on `transfer.rs`, `sffi/value_ops.rs` | **0 changed** |
| origin guard work (fail-opens, verdict contracts) | `check-build-outcome-reason-attribution.shs` resolution | fail-closed `[ -x ] \|\| err` retained; **no fail-open reintroduced** |
| `bcebe89b831` 15 revived `env_get` fallbacks | `git grep -c env_get -- src/app/llm_caret` | present across 5 files (main.spl: 6) |
| `aecf222a1ff` / `91f2002ec5a` O(1) export-origin lookup | `module_surface.spl` blob vs origin | **IDENTICAL** — linear scan not restored |
| `f2531d57bdf` stage-3 diagnostic env pass-through | `git diff` vs origin on `bootstrap-from-scratch.sh`, `authority.shs` | **0 changed** (and the one commit that would have touched them is deferred) |

## Anti-wipe — measured against the exact sha pushed

Against `6f18828fb5ff5da64310d1c9412947d5f34fa037`:

| invariant | expected | measured | verdict |
|---|---|---|---|
| `git ls-tree -r --name-only <tip> \| wc -l` | >= ~115,500 | **115,518** | PASS |
| `src/app/interpreter` files | 99 | **99** | PASS |
| `src/` entries | 13..25 | **16** | PASS |
| `src/runtime` files | >= 150 | **222** | PASS |
| `D` lines in range | every one accounted for by name | **0 deletions** | PASS (vacuously, and verified by `--diff-filter=D` returning empty) |

Base tree for comparison was 115,514 files; the range adds 4 files and deletes
none, which reconciles exactly to 115,518.

## Guard verdicts — verbatim

`--no-verify` is user-authorised for the push. rc was read from a variable on
the line **after** each command, never through a pipe.

```
check-no-conflict-tree-push          rc=0  PASS — 2 commit(s) checked in a83396620fde..6f18828fb5ff, 0 conflict trees
check-no-conflict-markers-push       rc=0  PASS — 6 file(s) scanned at 6f18828fb5ff across 2 commit(s) in a83396620fde..6f18828fb5ff, 0 conflict markers
check-tree-size-push                 rc=0  PASS — 2 commit(s) checked in a83396620fde..6f18828fb5ff, each banded against its own first parent, range base 115514 file(s), 0 structural faults
check-runtime-api-regression-push    rc=0  PASS — 2795 symbol(s) checked, 0 removed
check-c-runtime-compiles-push        rc=0  PASS — 106 file(s) compiled, 0 errors (2 skipped for unavailable external dependencies)
check-seed-builds-push               rc=0  PASS — 6 file(s) checked, seed bin + test targets compile cleanly at 6f18828fb5ff (link NOT verified: cargo check does not link)
check-test-tree-divergence --ref     rc=1  FAIL — 875 diverged vs 812 baselined (64 new, 1 fixed-but-still-baselined); 8 mirror-only (6 unallowlisted, 0 stale-allowlist); half-landed: skipped (no --base)
check-test-tree-divergence-delta     rc=0  PASS — 71 pre-existing offender(s), 0 introduced by this range
```

Two extra checks run directly, beyond the guard chain:

```
clang -fsyntax-only src/runtime/runtime_native.c   rc=0  0 errors
cargo check --release --bin simple                 rc=0  0 errors  (1m52s)
```

### What was stepped over, named

**`check-test-tree-divergence` is RED and I stepped over it.** It is a
**pre-existing** red left by other lanes, not caused by this range: the range
touches **0 files under `test/`** (`git diff --name-only <base> <tip> -- test/`
returns nothing). The documented scoped-delta escape was used and returned
`PASS — 71 pre-existing offender(s), 0 introduced by this range`. Per the
escape's own requirement, the pre-existing offender list is **recorded**, not
merely counted, as a committed companion file:
`doc/09_report/test_tree_divergence_preexisting_2026-08-17_shared_tree_sync.txt`
(875 diverged spec pairs). No baseline was regenerated — `--generate-baseline`
was not run.

### Unobtained (never reported as a pass)

- **`check-test-tree-divergence-delta` first attempt: rc=143 — UNVERIFIED.**
  That was my own 2-minute shell limit killing the guard mid-run, not a guard
  verdict. It was re-run with a 540s timeout and only then produced the rc=0
  PASS quoted above. The 143 is recorded here so it cannot later be mistaken
  for a real signal either way.
- **Link step: NOT verified.** `check-seed-builds-push` says so itself —
  `cargo check` runs the full frontend but does not link, so a
  declared-but-never-defined symbol would still pass. `rt_dict_clear` was
  therefore checked by hand: the forward declaration added to
  `runtime_native.c` (`int8_t rt_dict_clear(int64_t dict);`) matches the real
  definition at `src/runtime/runtime_native.c:8184`, and `rt_core_as_dict` is
  declared at `:937`.
- **No test-suite run.** `bin/simple test` was not run for this range. Nothing
  here claims spec-level green.
- **Nothing was rebuilt or redeployed.** `bin/simple` and `bin/release/**` were
  untouched; the worktree got a symlink to the already-deployed binary only.
  `/mnt/data/worktrees/simple-boot-snap` was never touched (bootstrap cycle 6
  is live there).

## Binary identity

Observed directly, per the standing warning that the symlink target gets
replaced mid-session and that no number from a brief should be trusted:

```
$ readlink -f bin/simple
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
$ stat -c '%s %y'
59537240 bytes   mtime 2026-08-17 12:58:51 +0000
$ bin/simple --version
WARNING: this Rust-built Simple binary is a bootstrap seed only; ...
```

**This is a different binary from the one the bug records in this very range
cite** (they record 59,536,728 bytes, mtime 2026-08-16 22:59:37). It changed
again during the session. No verdict in this record depends on the Simple
binary: the two compile checks used `clang` and `cargo` directly, and the
structural guards read committed content via `git ls-tree` / `git cat-file`.

## Push

`git push --no-verify` (never `--force`). Verified by `git ls-remote origin
main`, not by an exit code — a clean exit has lied on this remote, and a pipe
produced a false push success earlier today.

Origin moved once mid-flight (`a83396620fde` -> `36a5a0e8291`) and was handled
by re-fetch + rebase + retry, never by forcing. The final push carries this
record only, for the reason given in the outcome correction above.

## Standing conclusion for the next sync lane

The shared tree reporting a large "ahead" count is **not** a backlog. Two
independent passes today (91 commits -> 13 landed; 95 commits -> 2 prepared, 0
uniquely landed) both found ~85-98% of it already at origin under rebased shas,
because lanes push from isolated worktrees and never rebase the shared tree.
The useful work of a sync pass is therefore **verification**, not volume — and
the two findings that justified this pass were both invisible to the guard
chain:

1. A rebase can synthesise a **duplicate definition** from two pure-addition
   sides and break the crate (`4be6951d019`, E0592). Only compiling catches it.
   Run `cargo check` on the rebased tip, every time.
2. An old commit can carry an **outdated form** of a provenance gate that would
   silently revert a hardened one (`13636027582`, hardcoded `--backend
   cranelift`). Read both sides before believing a "fix" subject.
