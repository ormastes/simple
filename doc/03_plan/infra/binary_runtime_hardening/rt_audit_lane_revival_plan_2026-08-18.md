# rt-audit lane — revival plan (2026-08-18)

Reconstruction of a dead session (shared `simple-main` tree, scratchpad
`3669360f-…`) that was running two threads of work: the runtime exported-API /
C-migration audit, and an `amqp_utils` duplicate-symbol investigation.
Base: detached at `origin/main` `ca7c33ecf75`. **Every claim below was
re-verified against that tree — none is trusted from the scratchpad.**

## 1. What the dead session had established

### 1a. C-migration audit (C-MIG series)
Differential-evidence migrations of owned C/Rust runtime primitives to
pure-Simple equivalents, each with KAT + edge table + 100-vector bulk loop,
C retained as oracle. Its own bug drafts (`bug_base.md` → `bug_phase1.md` →
`bug_full.md`, three snapshots of one growing table) claim `done` through
**C-MIG-0042**.

### 1b. Dispatch-dead sweep
1458 owned `rt_*` C definitions vs 1901 registered in `interpreter_extern/*.rs`
→ 710 unregistered, of which **23 DEAD** deletion candidates, none deleted.

### 1c. `rt_cli_get_args()` nil-safety analysis (`FINAL_REPORT.txt`)
50 files / ~66 call sites. 8 files (12 sites) already nil-guard; **42 files use
the result directly with no nil guard**, while `runtime_native.c:5218` really
can return nil on OOM. Verdict was SAFE-FOR-TABLE with a documented semantic
change (nil → `[]`). **Never acted on.**

### 1d. amqp duplicate-symbol investigation
`collisions.txt` empty; `dup_probe_results.txt` 20/20 stable runs.

## 2. Verified against current origin/main

| Claim | Verdict at `ca7c33ecf75` |
|---|---|
| amqp dedup landed | **TRUE.** `src/lib/common/amqp_utils.spl` (744 lines) is the owner; `gc_async_mut`/`nogc_async_mut`/`nogc_sync_mut` are byte-identical 5-line `pub use std.common.amqp_utils*` delegators. Zero intra-file duplicate decls in all four. **This thread is DONE.** |
| `dispatch_dead_c_audit_2026-08-18.md` landed | **TRUE**, present. |
| `c_migration_inventory.sdn` current | **FALSE.** Highest id present is **C-MIG-0020**. |
| `c_replaceable_bug_list.md` current | **FALSE.** Highest id **C-MIG-0020** (0019 absent from the id set). |
| C-MIG-0021…0042 lib code landed | **FALSE.** `numeric_round.spl`, `text_ascii.spl`, `path_pure.spl`, `math/cbrt.spl`, `dict_contains_pure.spl`, `array_repeat_pure.spl` are all **MISSING**. Only `src/lib/common/encoding/byte_char.spl` (C-MIG-0028) survives. |

### The load-bearing finding: ~35 C-MIG commits exist but are not in main
`git log --all --not HEAD --grep=C-MIG-00` lists commits `fbed4bada30`
(C-MIG-0001) … `cd0fc78fc68` (C-MIG-0042) — including several duplicate pairs
from failed replays (`86a911da573`/`ac707c9f8af`, `60f3188fdd3`/`b047acd9096`,
`f9cb9e53b1b`/`6c52280166e`). `git merge-base --is-ancestor 86a911da573 HEAD`
→ **NO**. What actually landed instead is `c4fa74c1b16`
*"chore(salvage): 16 net-new files from commits that could not be
cherry-picked"* — 1815 insertions, mostly `*_crosslang_spec.spl` test files
plus `byte_char.spl` and three bug docs.

**So: the specs were salvaged, the implementations they test were not.** Those
salvaged crosslang specs reference `std.common.numeric_round`,
`std.common.path_pure`, `std.common.text_ascii` etc. — modules that do not
exist at main. The tree is presumed RED on those specs; this is the first thing
to measure.

### Cross-lane finding (independently re-verified, still live)
`src/compiler/20.hir/hir_types.spl` `SymbolTable.define`: `exact_symbols[name]`
is guarded (`if not self.exact_symbols.has(name)`) so **types are first-wins**,
while `scope_syms[name] = raw_id` immediately below is **unguarded, so
functions are last-wins** — the two tables disagree on a duplicate and nothing
is diagnosed. Confirmed real victim, still present:
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl`
defines `decl_tbl_last_valid_transition_index` at **:2169 and :2450** and
`decl_tbl_get_last_valid_transition` at **:2182 and :2458**; the second
(weaker) pair wins. This is the same root cause the amqp work was chasing —
amqp itself is clean, so the defect class outlived the investigation.

## 3. What was NOT finished
1. C-MIG-0021…0042 implementations are not in main (salvage was partial).
2. The salvaged crosslang specs are orphaned — untested against main.
3. Inventory SDN and bug list are 22 ids stale.
4. `rt_cli_get_args()` nil-guard rewrite: analysed, zero files changed.
5. The 23 DEAD `rt_*` symbols: identified, none deleted, follow-up check unrun.
6. `SymbolTable.define` last-wins/first-wins split: undiagnosed, unfiled.

## 4. Plan (ordered by evidence value, laziest first)

**P0 — measure the orphan damage.** Run the 8 salvaged `*_crosslang_spec.spl`
files from `c4fa74c1b16` against main. Detached `nohup setsid`, never `timeout`
(earlyoom kills `simple`). Output is the ground truth for P1's size.

**P1 — file the reality gap as a bug doc.** One record under
`doc/08_tracking/bug/`: salvage landed specs without implementations, naming
the 6 missing modules, the 35 unlanded commits, and the P0 results. This is
higher value than re-doing any migration — right now the tracking docs claim
work that is not in the tree.

**P2 — file the `SymbolTable.define` duplicate-symbol defect** with the
browser_engine reproducer above. Concrete, verified, unfiled, and it is a
silent-wrong-code bug, not a tracking bug.

**P3 — recover, don't redo.** The unlanded commits are reachable objects.
Attempt `git cherry-pick` of the C-MIG-0031/0032/0033/0034 chain (all four land
in one `numeric_round.spl`) as the cheapest test of whether recovery beats
rewriting. If cherry-pick fails the way it failed before, record *why* — that
reason is the actual blocker and nobody has written it down.

**P4 — reconcile inventory/bug-list** to whatever is genuinely in the tree
after P3. Not before: syncing docs to unlanded work is how this state arose.

**P5 (deferred).** `rt_cli_get_args()` class (a) rewrite — 8 files, zero
semantic change; and the 23 DEAD-symbol follow-up checks. Both are safe but
neither is blocking, and neither has a failing test behind it today.

## 5. Constraints
Work only in `/mnt/data/worktrees/lane-rt-audit`. Commit locally; **do not
push**. Never wrap runs in `timeout`; detach with `nohup setsid`.
