# Stale-merge line-loss audit — the exposure is ~950 product lines, not 6,236

- **Date:** 2026-09-06
- **Subject:** the eight merges flagged at the end of
  `doc/08_tracking/bug/stale_merge_bcc52735edb_rewound_seven_files_2026-09-06.md`
  ("8 merges match. 6,236 lines they dropped are still absent from `origin/main`")
- **Baseline tip for every measurement:** `origin/main` after this audit's own
  first repair landed (`0dc18e8edfc`), so every number below is a **residual**,
  not a pre-repair figure.
- **Repaired and landed here:** `0dc18e8edfc` — 14 files, 4 PRs, behaviourally verified.

## Headline

The alarming estimate corrects **downward by about 6.5x**.

| stage | product lines still absent |
|---|---|
| prior estimate (all paths, `sort -u` heuristic) | **6,236** |
| ... restricted to product paths (`src/ scripts/ config/`) | 1,928 |
| ... + require the line to be absent at the merge result too | 1,928 |
| ... + require it absent from the **entire tip tree**, not just the same file | 1,555 |
| ... after this audit's repair (`0dc18e8edfc`) | **949** |
| ... of which hand-adjudicated **SUPERSEDED**, i.e. never a loss | 35 |
| **genuine, unrepaired product exposure** | **~914 lines / ~95 files** |

Two facts do most of the correction, and neither is a quibble:

1. **The 6,236 is dominated by one merge whose losses are not product code.**
   `0547effe615` alone accounted for 3,900 of it. Its real footprint is
   ~14,000 lines across ~978 files — but **0 of them are product code after
   tree-scoping**. They are `test/**` and `doc/06_spec/**`, and `doc/06_spec` is
   generated from sspec (CLAUDE.md: "generated from sspec, mirrors test/ paths").
   The merge is `pr/sspec-maintain-80`, a bulk spec-regeneration PR, merged
   against a base 1,691 commits stale.
2. **The signature is file-scoped; content that MOVED counts as lost.** This
   produced a false positive worth 238 lines on its own — see
   `mem_snapshot.rs` below. Fixing it required indexing every normalized
   non-blank line in the tip's tracked tree (5,967,240 unique lines) and
   requiring a "lost" line to be absent from all of it.

**But the corrected number is not reassuring where it lands.** The residual is
almost entirely one merge, `a7fd32f9475`, and what it did is worse in kind than
the raw count suggests: it reverted **85 product files across ~19 already-landed
PRs** in a single resolution. That is not drift, it is a wholesale rewind.

## Method

Four filters, each one strictly narrowing the previous. Re-runnable; scripts
described precisely enough to reconstruct.

For merge `M` with parents `P1` (the topic side, `M^1`) and `P2` (the
origin/main side, `M^2`) and base `B = git merge-base P1 P2`, a line counts as
**genuinely lost** only when all four hold:

- **(a)** it is a `+` line of `git diff -U0 B P2 -- <f>` — main-side content
  gained since the base (whitespace-runs collapsed, blanks dropped);
- **(b)** it is absent from `git show M:<f>` — **the merge really dropped it.**
  Without this, lines the merge KEPT and a later commit deliberately removed are
  counted as merge damage. This filter alone took `cb986e09bdb` from 84 lines to
  1, and `66e58d62da8` from 365 to 52;
- **(c)** it is absent from `git show origin/main:<f>` — nothing restored it in place;
- **(d)** it is absent from **every tracked file at the tip** — it was not merely
  relocated to another path.

Parent orientation was verified per merge rather than assumed (`git rev-list
--count B..P1` vs `B..P2` plus each tip's subject): `^2` is the origin/main side
in all eight.

**Filter (d) is necessary but not sufficient, and (c)/(d) both still over-report.**
Two residual failure modes survive all four filters and can only be caught by
hand:

- **Semantic supersession.** `runtime_simd_dispatch.c`'s 31 "lost" lines are
  hand-written `rt_simd_add_f32x4` &c. The tip generates the same symbols from a
  `RT_SIMD_F32X4_BINOP` macro (`src/runtime/runtime_simd_dispatch.c:2332`). The
  *text* is genuinely gone tree-wide; the *function* is not. SUPERSEDED.
- **Reflow.** Confirmed by the prior record and re-confirmed here; a word-level
  diff (`git diff --word-diff=porcelain --ignore-all-space`) isolates it. Only 4
  of `a7fd32f9475`'s 115 product files were purely cosmetic, so reflow is a small
  term for this incident — unlike `bcc52735edb`, where it was 2 of 6.

### The classifier that made 85 files adjudicable without 85 hand-diffs

```
CLEAN_REVERT : merge took P1 wholesale for f  AND  P1 never changed f vs base
               AND  no non-merge commit touched f in M..origin/main
```

When all three hold, the merge result for `f` is *the merge base version*: the
topic side had no changes to contribute, so "take ours" discarded everything main
had landed, and nothing since has had an opinion. There is no resolution to
second-guess. For `a7fd32f9475`: **85 of 115 product files are CLEAN_REVERT**
(1,600 raw lines), 29 are TOUCHED_SINCE (need judgment), 1 is a real two-sided edit.

Aggregating `git log --no-merges B..P2 -- <f>` over the 85 names the PRs the
merge undid: **#249, #262, #265, #270, #271, #272, #274, #277, #284, #285, #286,
#287, #295, #296, #298, #302, #304, #305, #306.**

## Corrected per-merge table

Product paths only (`src/ scripts/ config/`), all four filters applied, measured
against `origin/main` at `0dc18e8edfc`.

| merge | date | prior est. | raw (file-scoped) | **tree-scoped** | verdict |
|---|---|---|---|---|---|
| `a7fd32f9475` | 09-02 | 2178 / 114f | 1830 / 115f | **894 / 92f** | **GENUINE.** Residual after this audit repaired 606 raw lines. Wholesale revert of ~19 PRs. |
| `0547effe615` | 08-27 | 3900 / 1f | 2 / 1f | **0** | **NOT PRODUCT.** ~14k lines, all `test/**` + generated `doc/06_spec/**`. |
| `198737a06e9` | 09-06 | 57 / 2f | 52 / 2f | **50 / 2f** | GENUINE, **same loss as the row below** (`.shs`→`.sh`); count once. |
| `66e58d62da8` | 09-02 | 57 / 2f | 52 / 2f | **50 / 2f** | Duplicate of the above — one 51-line loss in `bootstrap-stage3-provenance-verifier`, propagated. |
| `d150a169f26` | 08-31 | 35 / 1f | 35 / 1f | 31 / 1f | **SUPERSEDED** — macro-generated at tip. Not a loss. |
| `df31df530e7` | 09-06 | 4 / 1f | 4 / 1f | **4 / 1f** | Unadjudicated (Metal font backend). |
| `dfb069ade84` | 09-05 | 4 / 1f | 4 / 1f | 4 / 1f | **SUPERSEDED** — confirmed false positive in the prior record (#369 comment). |
| `cb986e09bdb` | 09-04 | 1 / 1f | 1 / 1f | **1 / 1f** | Unadjudicated. Note: 83 of its raw 84 lines were killed by filter (b). |

**Deduped genuine product exposure: 894 + 50 + 4 + 1 = 949 lines**, of which
~914 is `a7fd32f9475` and the provenance verifier.

## Widened detection (task 2)

The origination signature — "content P2 gained since the base that the merge
lacks" — structurally cannot see a merge that *propagates* a rewind it inherited.
`bcc52735edb`, the one confirmed incident, does not appear in it.

**Signature W ("invented resolution").** A merge legitimately differs from each
parent — it combines them. What is never legitimate is a file whose merge-result
blob matches **neither** parent:

```sh
for M in $(git rev-list --merges origin/main~400..origin/main); do
  git diff --name-only "$M^1" "$M" | sort > /tmp/w1
  git diff --name-only "$M^2" "$M" | sort > /tmp/w2
  comm -12 /tmp/w1 /tmp/w2 | grep -E '^(src|scripts|config)/' | grep -v /vendor/
done
```

Then, per hit file, count lines **either** parent had that the merge result lacks
and that are absent tree-wide at the tip (the same filter (d) index).

**Yield: 56 merges (vs the origination signature's 8), 1,942 product lines across
168 file-instances, over 223 merges scanned.** It finds `bcc52735edb` with
exactly the 7 files the incident record names — the validation that it catches
propagated rewinds. Roughly **1,377 lines in 48 merges are additional** to the
original eight.

Largest new hits: `5faf2103589` (270L / 35f, "merge: bring origin/main into
work/session-cleanup-2026-09-05"), `8f32c082271` (133L / 5f), `f30d6f5caf6`
(101L / 5f), `8c4ab84ceed` (55L / 7f).

**Calibrate it before acting on it.** Two measurements bound its precision:

- On `bcc52735edb`, an incident already triaged to completion, it still reports
  22 residual lines across 5 files — content the prior record adjudicated as
  deliberately superseded. So a nonzero residual is normal even for a fully
  repaired file.
- Its most-repeated single hit, `config/check/must_check_gates.sdn` at 74 lines
  in **three** separate merges, is a false positive at the semantic level:
  **zero gate rows were lost** (76 rows at the discarded parent, 110 at the tip,
  every one of the 76 still present). The 74 lines are amended row *text*.

Signature W is the right net — no false negatives of the propagated class — but
its output is a worklist, not a defect count.

## What was repaired

### `0dc18e8edfc` — the SFFI-authority sources and guards (#284, #285, #286, #287)

14 files, every one CLEAN_REVERT, restored byte-identical from `a7fd32f9475^2`
(the exact origin/main content the merge was handed and discarded).

Nine guards, **run** after the restore:

```
log-sffi-authority.shs                   PASS — 10 assertion(s) checked
mono-cache-sffi-authority.shs            PASS — 10 assertion(s) checked
mono-hot-reload-sffi-authority.shs       PASS —  9 assertion(s) checked
play-session-store-sffi-authority.shs    PASS —  4 assertion(s) checked
portal-server-sffi-authority.shs         PASS —  6 assertion(s) checked
dashboard-remote-collector-...           PASS —  4 assertion(s) checked
dashboard-schedule-collector-...         PASS —  4 assertion(s) checked
ssh-gcm-sffi-v2-authority.shs            PASS — 17 assertion(s) checked
rt-time-contract.shs                     PASS — 48 assertion(s) checked
```

Before the restore **five of the nine FAILED**, and `log-sffi-authority.shs`
exited 1 printing *nothing at all* — the silent-guard failure mode #286 exists to
eliminate ("deliberately `set -u` WITHOUT `set -e` — `grep -c` exits 1 on zero
matches, and under `-e` that killed this guard silently").

The proof this is a loss and not a supersession is an **incoherence between guard
and source at the tip**: `src/lib/nogc_sync_mut/log.spl` already carried #286's
owned `env_get` facade (0 raw `rt_env_get` externs, 2 `@unsafe`), while its guard
still asserted the pre-#286 shape (3 externs, 3 `@unsafe`, `rt_env_get` present).
The merge split the pair apart. The five `.spl` sources are restored with their
guards for the same reason — restoring one alone just moves the failure.

Provider check (guards are text ratchets; they do not prove the callee exists):
every `extern fn rt_*` declared by the five restored sources resolves at the tip
— `rt_ssh_aes256_gcm_decrypt_packet_v2`, `rt_tls13_aes256_gcm_{encrypt,decrypt}`,
`rt_file_read_text`. No unbacked extern introduced.

Gate verdicts, run from a clean detached checkout of the landed sha, range
`5292b9ab66f..0dc18e8edfc`:

```
check-tree-size-push: PASS — 1 commit(s) checked ... range base 134516 file(s), 0 structural faults
check-no-conflict-markers-push: PASS — 14 file(s) scanned ..., 0 conflict markers
check-no-conflict-tree-push: PASS — 1 commit(s), 1 unique tree(s) checked, 0 conflict trees
check-runtime-api-regression-push: PASS — 2994 symbol(s) checked, 0 removed
check-rt-dual-implementation-ratchet: PASS — 2491 symbol(s) checked against 2491 baselined, 0 new, 0 stale
check-runtime-source-list-parity: PASS — 135 file(s) checked, 0 drift (seed=28 simple=35 rust=25 in-no-list=84)
```

## What was deliberately LEFT, and why

### `mem_snapshot.rs` / PR #271 — attempted, reverted, left. **Still a genuine loss.**

The single largest file `a7fd32f9475` reverted (238 lines). It was restored, then
**backed out before landing**, and the reason is the most useful thing in this
report.

`5e09b3ef2fd` (#271) *deleted* `src/compiler_rust/native_all/src/mem_snapshot_provider.rs`
and moved its canonical body into `simple-runtime::mem_snapshot`. The merge
reverted that, so the tip has the file back — 438 lines the discarded parent did
not have. Restoring `mem_snapshot.rs` alone made
`check-rt-dual-implementation-ratchet.shs` go
`FAIL — 2490 symbol(s) checked against 2491 baselined, 0 new, 1 stale
(rt_phase_profile_record)`.

Do **not** read that as "main superseded #271". The baseline's own commentary,
written today, says the opposite:

> `rt_phase_profile_record` -- NOT a repair. PR #271 moved it out of
> `src/compiler_rust/runtime/src` into `src/compiler_rust/native_all/`, a
> directory this guard does not scan, so its Rust lane still exists...
> The symbol is GENUINELY DUAL

Main believes #271 is in effect. It is not. That commentary is reasoning about a
reverted tree, and the ratchet row and the filed scope-hole bug
(`rt_dual_ratchet_scan_scope_omits_native_all_2026-09-06.md`) both rest on it.

What is measurably true at the tip today:

- Two `#[no_mangle]` definitions of `rt_mem_snapshot_open` / `_record` exist —
  `src/compiler_rust/runtime/src/mem_snapshot.rs:23,140` and
  `src/compiler_rust/native_all/src/mem_snapshot_provider.rs:225,271`.
- The `simple-runtime` copy contains **0** occurrences of `run_id`; the
  `native_all` copy contains **7**. That is exactly the semantic divergence #271
  described ("the simple-runtime copy omitted the `run_id=` field that both C
  copies and the native-all copy emit"). The seed links `simple-runtime`
  *without* `native_all`.
- The **link** half of #271, however, does **not** reproduce:
  `cargo test -p simple-native-all --no-run` at the tip **succeeds**
  (`Finished test profile ... in 7m 38s`, exit 0).

So: the divergence is live, the link failure is not, and the correct repair
(re-apply #271: restore `mem_snapshot.rs`, delete `mem_snapshot_provider.rs`,
restore the `native_all/src/lib.rs` re-export, and remove the now-stale ratchet
row) is a four-file change that lands on top of another lane's same-day
reasoning. **That belongs to the runtime lane, with the divergence measured
behaviourally, not to this audit.** Restoring the file alone would leave the
ratchet red; restoring it wholesale would silently contradict a documented
decision. Left, and filed here.

### Left with CLEAN_REVERT evidence, needing their owning lane

| cluster | files | lines | why left |
|---|---|---|---|
| compiler HIR/MIR lowering (#265, #272, #295, #298, #306) | ~25 under `src/compiler/20.hir`, `50.mir`, `80.driver` | ~120 | No Stage-3 run is available on this host. Restoring lowering code that cannot be exercised is precisely how the original rewind happened; the prior record left the same class for the same reason. |
| nvfs mount-seal (#262) | `check-simpleos-nvfs-server-roundtrip-ovmf.shs` + 6 sources incl. `mount_table.spl` (147L) | ~330 | Its gate is an x86_64 OVMF boot; this host is aarch64, so the repair cannot be verified where it is made. |
| `mem_snapshot.rs` (#271) | 1 (+3 for a correct repair) | 238 | Above. |
| `bootstrap-stage3-provenance-verifier` | 1 | 51 | Counted once across `66e58d62da8`/`198737a06e9`. Landed in the codex/stage3 lane, which is actively rebasing; belongs to that lane. |
| `check-cpu-simd-render-scale-contract.shs` + `backend_measurement_software_export.spl` (#302), `check-native-option-bool-eq-vs-literal.shs` (#304) | 3 | 93 | **Attempted, then backed out.** Restored from `a7fd32f9475^2` and run: neither guard *discriminates* on this host. `check-cpu-simd-render-scale-contract.shs` reports `cpu_simd_render_scale_contract_status=fail / reason=4k_run_failed_exit_127` **byte-identically before and after** the restore (it needs a runnable 4K render binary); `check-native-option-bool-eq-vs-literal.shs` prints **nothing at all** and exits 0 in both states — itself the silent-guard failure mode, and unchanged by the restore. With no signal that distinguishes the restored state from the current one, landing it would be an unverified change to a guard. Backed out. Needs a host that can run the 4K lane. |

### Left as NOT A LOSS (do not restore — restoring these is a clobber in the other direction)

- **`d150a169f26` / `runtime_simd_dispatch.c`, 31 lines.** Tip generates the
  symbols via `RT_SIMD_F32X4_BINOP`. The tip version *also* carries a later MSVC
  `!defined(_MSC_VER)` fix the discarded parent lacks — main moved forward here,
  in both directions.
- **`dfb069ade84` / `bootstrap_globals.spl`, 4 lines.** Already adjudicated a
  false positive by the prior record; re-confirmed.
- **`config/check/must_check_gates.sdn`, 74 lines × 3 merges** (widened scan).
  Zero gate rows lost; 76 → 110.
- **`0547effe615`'s ~14,000 lines.** `test/**` and generated `doc/06_spec/**`
  from a bulk sspec-maintenance PR. Regenerating specs is the sspec tool's job,
  and the duplicate test trees (`test/unit` vs `test/01_unit`) are under
  divergence-baseline control, so some of it is deliberate de-dup. **Not
  adjudicated file-by-file** — 978 files exceeds what this session could defend,
  and its product exposure is 0.

## Prevention

The prior record's item stands and is now better specified: make **signature W**,
not the origination signature, the push-tier gate. W catches both classes
(originated and propagated), needs only two `git diff --name-only` and a `comm`
per merge in the outgoing range, and found 56 merges where the current prose rule
found none. Give it an `--expect-invented <n>` escape for genuine conflict
resolutions, on the model of `check-tree-size-push.shs`'s `--expect-files`.

Second, cheaper item, aimed at the actual mechanism here: **a merge that resolves
a file by taking its own side when its own side never touched that file since the
base is never a resolution — it is a discard.** That is the CLEAN_REVERT
predicate above, it is three `git diff --quiet` calls per file, and on
`a7fd32f9475` it would have fired on 85 files at push time.
