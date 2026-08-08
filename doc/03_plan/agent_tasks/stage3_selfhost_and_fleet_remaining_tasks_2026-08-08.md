# Stage-3 self-host + fleet remaining tasks

**Slug:** `stage3_selfhost_and_fleet_2026-08-08`
**Written:** 2026-08-08
**Audience:** a single agent per task, working alone, with no memory of this
session. Every task below states its own preconditions, what was already
verified (don't re-derive), and the specific traps that already produced
wrong answers today.
**Model guidance:** tasks marked `TIER: routine` are mechanical/well-scoped
and safe for a smaller model. Tasks marked `TIER: judgement` need a decision
that cannot be mechanised — the task says what the decision is.

---

## 0. READ THIS FIRST — traps that already burned lanes today

**T1. Verify blobs before measuring, every round.**
`git hash-object <file>` vs `git rev-parse origin/main:<path>`. An automated
`chore: sync ...` process periodically snapshots the shared working copy and
has silently reverted lanes' files to pre-fix blobs at least five times
today (two lanes hit it twice each) — once reverting a doc to a 197-line
stale version while origin held 538 lines. Work from `origin/main` blobs in
a scratch dir or isolated `git archive` extraction, not the shared WC.

**T2. `git checkout -- <path>` can restore the EMPTY blob `e69de29`.**
Happened once today when a lane tried to revert a sabotage marker via that
command after a failed `git fetch` left `FETCH_HEAD` unresolvable. Verify the
resulting blob sha, don't trust the command.

**T3. `bin/simple` IS the Rust seed** (confirmed by matching md5 against a
fresh `cargo build` of the seed, multiple times today) **until it is
redeployed.** A redeploy happened once today at 07:45:57 — always check
`ls -l --time-style=+%H:%M:%S bin/release/x86_64-unknown-linux-gnu/simple`
and `md5sum` against a fresh seed build before trusting any claim that a
`.spl`-side fix or Rust-seed fix is "live". `.spl` fixes ARE live without
redeploy (the deployed binary loads `.spl` from the working tree); Rust-seed
fixes are NOT.

**T4. `bin/simple run` resolves `use std.…` relative to the SCRIPT'S
directory, not cwd.** A probe run from `/tmp` or a stale scratchpad can
silently read an old bundled `src/lib` snapshot and be immune to a
deliberate syntax error. Always prove edit-visibility with a sabotage marker
**during** any A/B measurement, not just once beforehand — a probe that
proved visibility once, then measured later without re-checking, produced a
wrong conclusion that was cited as authoritative four times before being
caught.

**T5. The `list`/`list<i64>` element-read corruption is real, but SCOPED.**
Fires only for parameters of functions called **across a module boundary**
under the seed's JIT. A `list`-spelled parameter on a function in the same
file as its caller reads correctly. `list<i64>` is fully typed and breaks
identically to bare `list` — only `[T]` is safe for a cross-module
parameter. This is a seed-JIT defect (pure-Simple native codegen is clean on
every spelling), but operationally live because `bin/simple` is the seed.

**T6. `env_get` has THREE contract shapes** — guarded (`-> text`, returns
`""` for unset), unguarded passthrough (returns **nil**, and a text method
call on that **silently aborts the enclosing function with no diagnostic**),
and honest `text?`. Resolve the actual `use` line to the real definition;
never pattern-match `env_get(...) ??` — that produced both a false "15 real
defects" (13 turned out already-guarded) and a false "36 dead fallbacks" (14
were already dead-safe).

**T7. Spec harness: trust the `SPEC FILE VERDICT` line, always read
`dropped=`.** `dropped>0` means the file ran only part of itself and was
still scored as if complete — a real, now-fixed, greenwash. A tail
`describe(...)` as the last statement of `fn main():` makes the whole file's
exit code a **constant 1** (Simple returns a function's tail expression, and
for `main` that becomes the process exit status) — exit-status gating is
vacuous in BOTH directions for that shape; only the verdict line is
trustworthy. Prefer `--no-session-daemon` — a stale daemon produced 6
spurious failures today on an identical binary.

**T8. `grep` here is a WRAPPED ugrep honouring `.gitignore`.** Use
`/usr/bin/grep` for any load-bearing count. Test trees are DUPLICATED
(`test/unit` + `test/01_unit` + `.spipe_matchers_*`) — deduplicate before
quoting a figure. `src/compiler/{mir,driver,hir,backend}` are SYMLINKS; real
dirs are numbered (`10.frontend/`, `20.hir/`, `30.types/`, `35.semantics/`,
`50.mir/`, `55.borrow/`, `70.backend/`, `80.driver/`). Git pathspecs on the
symlinked names FAIL SILENTLY.

**T9. Beware counting string literals as real imports/calls.** Specs assert
on quoted source (`expect(x.contains("use std.foo")).to_equal(true)`), which
inflates a naive grep. This produced a false "92 unresolved imports" report
today against a cluster that actually resolved fine.

**T10. Almost every number quoted without independent re-derivation was
wrong today**, in both directions: 42/29 survivors → really 6; 1,385
mismatched functions → really 31; 15 broken `env_get` sites → really 2; 10
dead `??` fallbacks → really 2 real defects; 122 orphaned specs → really 352
→ really 162 (three re-derivations, each fixing bugs in its predecessor's
resolver). **Re-derive any inherited count with your own injection-tested
oracle before acting on it.**

**T11. Disk is tight.** Check `df -h /` before any large build. It swung
from 175G free to 76G free in about an hour today from one orphaned
`git worktree`'s Rust `target/` dir (31G, safe to delete — build caches are
always regenerable, never source or work product — but check
`ps aux | grep cargo` for a live writer first). ENOSPC has wiped `main`
twice before at this fill level. Do NOT run `git prune`/`git gc --prune` —
multiple lanes' uncommitted work is anchored as unreachable loose blobs in
the object store.

**T12. `native-build` writing an artifact INSIDE the repo can be silently
eaten by a parallel sweeper before the rename completes** — "reported
success but produced no fresh output binary" with the deployed binary's
mtime unchanged. Write build output outside the repo tree.

**T13. `native-build` exiting 0 while producing NOTHING is a known trap** —
silence with rc=0 is a failure signal here, not a pass. Conversely,
native-build is SLOW, not broken: budget >300s for a simple build, >1200s
for a full Stage-3 run; two lanes killed valid builds under load (peak
observed load 92) and had to retract "did not complete" claims.

**T14. Landing: PLUMBING protocol only** (`git hash-object -w` → scratch
index `read-tree`/`update-index --cacheinfo` → `write-tree` →
`commit-tree -p origin/main` → `git push origin $SHA:refs/heads/main`).
Never `jj commit`, never `git add -A`. Pin blob SHAs as literals in any
retry loop and assert the tree's blob matches before pushing. `git push |
tail -2` returns TAIL's exit status and has falsely reported success —
check the real unpiped exit code, then verify with
`git merge-base --is-ancestor <sha> origin/main` **and** a content grep.
Origin has been taking 100+ commits/4h from concurrent sessions; expect to
lose non-fast-forward races and rebuild on the fresh tip each retry (one
lane needed 25 attempts). All three guards
(`check-no-conflict-tree-push.shs`, `check-no-conflict-markers-push.shs`,
`check-tree-size-push.shs`) must PASS with non-vacuous counts on an explicit
`origin/main..<sha>` range — `ERROR — nothing was checked` (exit 2) is NOT a
pass. If they all report that error, check
`git config --get core.worktree` — a stray value pointing at a `/tmp`
worktree silently disables all three guards repo-wide (found and partially
cleared today; re-check it hasn't reappeared).

---

## 1. Stage-3 self-host — the critical path — TIER: judgement

**Do not restart the investigation.** Read, in order:
- `doc/08_tracking/bug/stage3_vacuous_binary_is_enum_discriminant_garbage_not_a_link_failure_2026-08-08.md`
- `doc/08_tracking/bug/native_mir_lowering_unresolved_to_u8_and_join_2026-08-08.md`
- the landed correction narrowing the enum-dispatch hypothesis (search commit
  history for `stage3` + `census` + `d61d02cc0885`/`a99e87c3beb`/`20471cba7f9`)

**What is settled, do not re-litigate:**
- `unresolved type: ByteOrder` — FIXED, sabotage-proven (revert → 16 errors
  return; fix → 0).
- The output binary IS linked (the 1.16 MB compiled object's `__simple_main`
  is byte-identical to what ships) — the earlier "unlinked object" framing
  is REFUTED. The object itself is vacuous: 0 `store`, 0 arithmetic, across
  5,767 functions.
- **The enum-dispatch hypothesis is REFUTED** — 5 independent builds (seed
  interpreter, seed native/LLVM, seed native/cranelift, `stage2-simple`
  native/LLVM, `stage2-simple` under the exact Stage-3 env), each running a
  25-variant enum probe shaped like `HirTypeKind`, all resolved 12/12
  correctly. The earlier `d=-1`/wildcard-fallthrough reproducer does NOT
  reproduce against the binary it names.
- **The real confound**: `cycle.sh` sets `SIMPLE_NATIVE_BUILD_RUST=1` for
  Stage 2 but not Stage 3 — that variable is a PIPELINE SELECTOR. Stage 2 has
  always run the Rust pipeline; Stage 3 is the ONLY run that has ever
  exercised the pure-Simple pipeline at compiler scale, and it has never
  produced non-vacuous output. Every "Stage 2 passes / Stage 3 doesn't"
  comparison to date compared two different compilers.
- **Native MIR lowering family** (`error: unresolved method call: <name>`,
  the literal string `_mir_error_is_fatal` keys on): FIXED —
  10 numeric-conversion methods, `join`, `contains` on array receivers.
  ALREADY WORKED without a fix — `substring`, `split`, `replace`, `unwrap`.
  STILL OPEN — `slice`, `merge`, `index_of` (one-arg form only; a separate,
  already-safe two-arg `index_of(needle, start)` overload exists and must
  not be touched/confused with this).
  **This family is NOT the Stage-3 root cause** — `substring` (the single
  most frequent name in the 3,629-substitution census, 261 hits) and
  `unwrap` (217 hits) lower fine on typed receivers. The 538 names behind
  the 3,629 substitutions are AT LEAST TWO MECHANISMS sharing one error
  string: a handful of genuinely-missing arms (`merge`, `slice`), and a
  majority that fail only because **Stage-3's flat HIR erases receiver
  types**. Adding more method arms cannot fix the majority group.

**What is NOT settled — this is the actual next step:**
A scale-vs-construct bisect starting at `src/compiler/10.frontend/core/`,
independently implicated by (a) the file that timed out during census
measurement and (b) the largest surviving `.text` section in the vacuous
binary's own census. The judgement call: does Stage-3's HIR need to start
carrying receiver types through to MIR lowering (a real architecture
change), or is there a narrower scale-triggered defect (e.g. an
arena/allocator limit, a recursion depth, a cache eviction) that only
manifests at full-compiler size? Do not assume either — build the
bisection and let it answer.

**Also open, filed not fixed, same file family:**
Two producers of the residual `[infer-arm]` HIR-type-inference crash are
tracked at `doc/08_tracking/bug/native_build_self_hosted_mir_infer_type_crash_2026-07-30.md`
— producer 1 (`function_lowering.spl`) fixed and measured effective;
producer 2 (`lower_hir_expr`'s Binary path) still blocks. Check whether the
scale-vs-construct bisect and this crash share a cause before treating them
as independent.

**Success criterion for the whole thread**: a Stage-3 build whose output
binary, when run, computes correct values on a real workload — not just
exits 0. Prove it with a positive capability probe (sabotage a
`src/compiler/**` source with an observable behavior change, rebuild,
confirm the change appears in the OUTPUT BINARY's behavior, revert). Size
and banner both lie; `--entry` delegates to the Rust runtime and has already
produced one false self-host claim.

**Once a genuine binary exists**: do NOT overwrite
`bin/release/x86_64-unknown-linux-gnu/simple` without explicit confirmation
— ~10 concurrent sessions depend on it. Build to a versioned path first.

---

## 2. `elf_parser.spl` relocation-merge defect — TIER: routine, ready to dispatch as-is

**File**: `doc/08_tracking/bug/elf_parser_relocations_merged_without_target_section_2026-08-08.md`
**Location**: `src/compiler/70.backend/linker/elf_parser.spl`, the loop
around line ~375-383.

**Already verified this session — do not re-derive:**
- The loop merges every `SHT_RELA` section into ONE flat list;
  `ElfRelocation` (struct at line 64: `r_offset`, `r_info`, `r_addend`) has
  no target-section field, so attribution is lost by construction. The
  comment above the loop even says "first RELA section" while the code
  merges ALL of them — comment and code disagree.
- **No-consumer claim verified**: the only real `ElfObject` consumer
  repo-wide is `src/compiler/70.backend/linker/sym_resolver.spl`, and it
  reads symbols, never `.relocations` (0 hits). Latent, safe to fix without
  breaking a live caller.
- **`sh_addr` is NOT a bug** — it deliberately stores the file offset (see
  the in-file comment at line ~338: "We store sh_off in the sh_addr field
  since ElfSectionHeader has no sh_offset field. All callers in elf_parser
  use sh_addr as the file offset"). Do not "fix" this; it is a documented
  convention. (I nearly filed this as a false critical finding myself —
  verify before trusting a plausible-looking line.)

**The fix**: widen `ElfRelocation` with a `section_idx: i64` field, populate
it from the RELA section being parsed in each loop iteration. Consider
consolidating with the shared-helper pattern from the sibling fix
(`16456ea9b55`, `src/compiler/80.driver/smf_elf_parser.spl`'s
`_find_text_section_indices()`), which exists specifically so two consumers
of the same data can't drift apart again — that sibling fix, tested the
same way, found the OLD unfixed code returned **0 bytes of code** against a
real `cc -ffunction-sections` object (an empty placeholder `.text` won the
first-match) — test THIS fix the same way: `cc -c -ffunction-sections
-fdata-sections` on a small multi-function C file, verified against
`readelf -S`/`readelf -r`, not a synthetic fixture.

RED→GREEN control, matching the sibling's rigor
(`6 passed, 1 failed` → `7/7`).

---

## 3. Organic-drift return-type mismatches (~9 sites) — TIER: routine

**File**: `doc/08_tracking/bug/return_type_result_mismatch_class_audit_2026-08-08.md`
(landed `310ee089c55`).

The originally-quoted "1,385 functions" figure is not reproducible anywhere
in the tree. An injection-tested classifier found **31 genuine sites** in
`src/`. **22 of 31 are owned by the impl-to-free-fn refactor-damage family**
(closed today, 5 of its 6 known survivors fixed — see
`doc/08_tracking/bug/impl_to_free_fn_refactor_family_still_incomplete_2026-08-08.md`)
— do not touch those without checking whether that family is still open.
**The remaining ~9 are unrelated organic drift** — build your own
injection-tested classifier before acting (this count has moved by 40x
once already), then for each site determine whether the DECLARATION is
wrong (usual case) or the BODY is wrong, check call sites, and fix with a
RED→GREEN control per site.

---

## 4. `asm """…"""` placeholder-binding defect — TIER: judgement, NOT YET SCOPED

Known only from a prior-session memory reference
(`reference_asm_block_operand_placeholders_never_bind`); NOT investigated or
re-verified this session. Before writing a fix task: reproduce it fresh
against current `origin/main`, confirm it still reproduces (many defects
this session turned out already-fixed or mis-scoped), and determine which
of the three implementations (seed/pure-Simple/runtime-C) is actually
affected. This is compiler-internals work (parser/lowering substitution
semantics) — expect it to need the same rigor as the MIR-lowering work in
§1, not a mechanical fix.

---

## 5. Facade-shadowing sweep — mostly done, one item to re-check — TIER: routine

Of the 21 stdlib facades with a same-named tier sibling: `format_utils`,
`platform`, `process_monitor`, `resource_tracker`, `text`, `string_core` are
wildcard-safe by construction; `math`, `pe_coff_header` are self-contained,
not re-export facades; `compute` is a deliberate namespace anchor;
`io_runtime` was fixed (`b62ab7772e7`); `option` was already fixed
elsewhere (`4a59910ef47`); `crypto` and `math_repr` are innocent (verified
live with fabricated-symbol negative controls); `log` was fixed today
(chain: `_ensure_initialized()`'s unguarded `env_get` fault fixed, then the
9 re-exports added, then a circular-import `val`-binding bug the re-export
itself exposed was fixed) — landed `7f2c7ae8ff1`, `86b61ace566`,
`157dc560b16`.

**`string`/`hash` facades were blocked** on the `@noalloc` decorator defect
(fixed today, `25a838b2a83`/`1993b437300`) requiring a seed redeploy, which
**did happen today at 07:45:57**. **Re-check whether `string`/`hash` are now
genuinely unblocked** (probe `use std.nogc_async_mut_noalloc.hash.{...}` /
`.string.mod.{bm_str_len}` under `bin/simple test` against the CURRENT
deployed binary's md5/mtime) and land the re-exports if so. `hash.spl`'s
in-source header should already state the unblock condition — verify it
against reality before trusting it, since it was written before the
redeploy happened.

---

## 6. Module-count-limit fix — landed but not live — TIER: routine (verification only)

Landed `e4b5b0dac8e` (`DEFAULT_MODULE_LIMIT` 800→4000 in the Rust seed, plus
a legible non-verdict-shaped abort banner) — root cause was a real ceiling
being legitimately approached (0 duplicate loads measured), NOT a leak.
**Requires a seed redeploy to take effect** — check whether the 07:45:57
redeploy included it (compare commit timestamps/ancestry) and re-verify
with `SIMPLE_LOADER_TRACE=1 bin/simple test <a spec with a large graph>`
against the current deployed binary.

Also filed, not fixed: 95% of one client's 787-module graph (746 modules,
including all 537 of `src/compiler/**`) comes from a single
`--spl-doctest`-only import in `test_runner_client.spl:9`, costing 22.4s of
startup on every invocation regardless of whether doctest mode is used.
Needs routing `--spl-doctest` through `test_should_use_light_daemon_client`
(Rust, `driver/src/main.rs:235`) since `test_runner_single.spl` doesn't
implement the flag today — landing the `.spl` half alone would silently
drop `--spl-doctest`.

---

## 7. Live 3-day-old sabotage marker — TIER: judgement (needs Rust AST knowledge)

`src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:315`,
present at `origin/main` since 2026-08-05:
```
// SABOTAGE-TEMP: reverted to prove the FP guard goes RED. RESTORE.
```
A lane deliberately removed the `extern fn`/`extern class` name-collection
match arm (documented in the surrounding comment, lines ~309-314: extern
declarations should contribute their name to `locally_defined_names` so a
`[use-warning]` oracle doesn't wrongly flag a providing module as not
providing) to prove a false-positive guard fires — and never restored it.
I confirmed this is real and dated but deliberately did not guess-fix it
myself (wrong Rust `Node` enum variant name risked a bad edit to the seed's
module loader). Needs: find the correct `Node::Extern*`-shaped variant in
this codebase's AST, restore the arm, verify against the FP guard it was
testing (it should still go RED with the arm removed and GREEN restored).

---

## 8. Named-constructor Nil defect in pure-Simple — TIER: judgement, blocked on §1

`lower_struct_construct` (`50.mir/_MirLoweringExpr/switch_operators_calls.spl:3038`)
shares the seed's now-fixed named-constructor defect (an unknown field name
is accepted, never validated, the intended slot silently reads as the
constant 3 — `lower_nil_expr`'s `ConstInt { value: 3 }`, "Nil is tagged
value 3"). Seed half fixed (`277ce674d22`). Pure-Simple half is OBSERVED,
not fixed — deliberately, because there is no build oracle to verify a fix
without risking converting a visible crash into an undiagnosable silent
miscompile. **Blocked on §1** (a working Stage-3 build provides the oracle).

---

## 9. `gc_analysis/mod.spl` — filed, not touched — TIER: judgement

Different, pre-existing corruption class from the rest of `gc_analysis/`
(which was otherwise fixed today — see
`doc/08_tracking/bug/gc_analysis_desugar_dropped_method_bodies_2026-08-02.md`
and the `barriers.spl` fix). `mod.spl` has TAB-named args, an `_1` closure
placeholder, and empty `GcSafetyReport` methods. **Do NOT delete
`gc_analysis/`** — it has real, currently-exercised test importers
(`gc_safety_spec.spl`, `gc_roots_barriers_spec.spl`); an earlier "zero
importers, safe to delete" claim was checked and found FALSE.

Related, same file family: the parenthesized-field-call resolution gap
(`(self.field)(args)` failing where `self.field(args)` works) was FIXED at
the compiler level today (seed only, `interpreter_call/mod.rs`,
`call_value_as_callable`) — landed `c571dbd6f4e`. If touching `mod.spl`,
this class of failure should no longer apply; if it still does, that is new
information worth its own bug doc.

---

## 10. Orphaned spec basenames — deliberately left, no action needed — TIER: n/a

`doc/08_tracking/bug/landed_specs_import_modules_absent_from_origin_main_2026-08-08.md`.
Latest re-derived count: 162 flagged paths / 85 unique basenames (moved
122→352→162 across three re-derivations, each fixing real bugs in its
predecessor's resolver — re-derive again if you touch this, don't trust
162). `git log --diff-filter=D` returns EMPTY for all 85 basenames — none of
this was ever landed and later deleted, consistent with planned/red-phase
work (same pattern as the pre-existing `parser.treesitter*` precedent). The
considered verdict was "leave all 85, delete nothing, land nothing" — WC
evidence is too thin to distinguish "abandoned" from "someone's in-flight
work" per-basename. A grandfathered guard is viable at this count but was
deliberately NOT landed, since freezing an un-individually-triaged number
is worse than no guard.

---

## 11. Disk headroom — one large safe win still available — TIER: routine

Currently ~105G free at 98% full (reclaimed 31G today from one orphaned
`git worktree`'s unreferenced Rust `target/` dir — confirmed no live
process before deleting). A teammate session earlier measured **~320GB
reclaimable in Docker images/containers** on this machine
(`docker system df`) — not yet acted on. Before running `docker system
prune`: re-measure (the number may have changed), confirm `docker ps` shows
no build mid-flight, and this is unambiguously safe (Docker image cache is
regenerable, same category as a Rust `target/` dir). This is the single
largest remaining safety margin against another ENOSPC wipe of `main`.

There are 60+ `git worktree` entries registered against this repo across
`/home/ormastes/dev/`, `/home/ormastes/`, and `/tmp/` — most carry named
branches (`codex/*`) suggesting active work from concurrent sessions/tools,
not just this fleet. Do NOT bulk-clean these without per-worktree liveness
checks (`ps` for an owning process) — only `target/`-style build caches
inside them are unambiguously safe.

---

## 12. Session capacity note

This session hit the **200-subagent cumulative spawn cap**
(`CLAUDE_CODE_MAX_SUBAGENTS_PER_SESSION`) — it does not free up as lanes
complete; it is a lifetime-of-session total. Continuing this work in
parallel requires a NEW session with that variable raised in the
environment before launch.
