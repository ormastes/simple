# Plan: Aerospace-Grade Hardening — `critical` + `flight-core-v1` + `aero-a`/`space-a`

**Date:** 2026-08-07
**Research:** [`doc/01_research/language/assurance/aerospace_grade_hardening_research_2026-08-07.md`](../../../01_research/language/assurance/aerospace_grade_hardening_research_2026-08-07.md)
**Sibling campaign:** [`doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md`](../resource/resource_parallel_agent_plan_2026-08-06.md)
(shares the stage-3 gate; its `emit_move`/allocation work is the substrate for PR 6 here)

Work packages are sized for a mid-tier agent (Sonnet; Haiku for the mechanical
ones) in a single session. Agents MUST NOT touch files outside their WP —
parallel sessions share the working copy (`.claude/rules/vcs.md`). Commit + push
per WP.

---

## #0 — Read this before picking a WP: the reachability gate

Two independent facts cap what any code change here can deliver **today**:

1. **`bin/simple` is the Rust seed** and stage-3 self-host is blocked
   ([[reference_borrow_check_runs_only_in_aot_pipeline]],
   `doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md` §0).
   A new pass under `src/compiler/**` outside `90.tools/lint` produces **zero**
   user-facing enforcement until that lands.
2. **The deployed lint binary predates its own source.** Proven 2026-08-07: the
   binary at `bin/release/x86_64-unknown-linux-gnu/simple` contains the string
   `MEXH001` but **not** `MEXH006`, which sits at
   `src/compiler/90.tools/lint/_LintMain/lint_checks.spl:65`. A `.spl` lint edit
   therefore does **not** take effect under `bin/simple lint` until redeploy.

**Consequence for method, not just for scope:** *sabotage is not a valid oracle
for lint work in this tree.* A verification agent inserted a `println` marker
into `check_required_comment_source` — a function proven wired — and the marker
did not appear, while its diagnostic still fired from the binary. Any lane below
that "proves" a lint check is wired by sabotage has proved nothing. Use a
positive call graph from `main_and_help.spl:322` down, plus a live behavioural
run on a probe file.

Every WP below carries a **Reach** column stating which binary enforces it and
whether that binary reaches users today. This is per-lane, not a global
disclaimer — the rule registry, docs and SDN schema reach users immediately;
compiler passes do not.

---

## Verified premises (2026-08-07)

Every row was checked against the tree. **`file:line` or it is not a premise.**
Rows marked ✗/◐ are corrections to the originating proposal — the plan below is
built on the corrected version, not the proposed one.

| # | Proposal claim | Verdict | Evidence |
|---|---|---|---|
| 1 | `critical` canonical; `mission-critical`/`mission_critical` deprecated aliases | ✓ | enum `_LintMain/config_and_model.spl:51-55`; parser `:83-101`; aliases `:95,:98,:100-101`; ladder `doc/02_requirements/language/mission_critical_profile.md:146-156` |
| 2 | Profile+alias table duplicated in 5 places | ◐ | 5 copies, but the 5th is the **interpreter** (`10.frontend/core/interpreter/eval_decls.spl:284`, Deny-half only), **not** test-runner config. Others: lint `config_and_model.spl:83-101`, driver `80.driver/driver_safety_severity.spl:43-57`, run `src/app/io/_CliCommands/handler_commands.spl:96-109`, test-runner args `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:28-41` |
| 2b | Severity table duplicated 5× | ✗ | Three *different* mappings share the names: lint→levels dict (`:217-241`), driver→`SafetyPassSeverity` (`:43-57`), interpreter→bool (`:284`). Not a duplication; a divergence |
| 2c | SDN scanner duplicated | ✓ (new) | **3 copies**: `config_and_model.spl:335-352`, `handler_commands.spl:114-131`, `test_runner_config.spl:48-71` |
| 2d | Driver comments cite layering/interpreter contamination | ✓ | `driver_safety_severity.spl:4-22`; echoed `handler_commands.spl:90-95`, `test_runner_args.spl:15-27`, `eval_decls.spl:275-282` |
| 3 | `ProjectContext.load_from_sdn()` parses then discards | ✓ | `80.driver/project.spl:81-90` — comment literally reads "For now, return defaults (field mapping can be added later)". Also `set_active_profile` (`:133`) has **zero callers**; `active_profile` (`:56`) is never set |
| 4 | run/test scan TOML-ish `[lints] profile =` vs documented `lints:` | ✓ **and worse** | Scanners `handler_commands.spl:114-131`, `test_runner_config.spl:48-71`, `config_and_model.spl:347`. Documented convention is indent/colon (`doc/06_spec/system/compiler/modules/tooling/formatting_lints.md:345,:438`). **All three scanners are dead**: no `simple.sdn` in the repo has a `lints` key and there is no repo-root manifest, so every scanner always returns `""`. Project-level profile pinning does not work at all |
| 5 | `mission_critical_profile.md` stale re: run/test plumbing | ✓ | Doc `:120-121` says "NO profile plumbing exists today… NOT IMPLEMENTED"; contradicted by `handler_commands.spl:177` and `test_runner_config.spl:188`, both `SIMPLE_SAFETY_PROFILE` sets |
| 5b | `SIMPLE_SAFETY_PROFILE` authoritative in-process? | ✗ | Process-global env var, never typed state. Driver **re-reads** per call (`driver_safety_severity.spl:62-63`); interpreter **latches once** at `eval_init` (`eval_decls.spl:297`) and cannot see later changes; test runner uses it as subprocess serialization only |
| 6 | noalloc root claims no-heap yet exports allocators | ✓ | Claim `src/lib/nogc_async_mut_noalloc/__init__.spl:1-5,:29-33` ("alloc_allowed: false"); exports `:76` (Bump/FreeList/FixedBlock/MultiPool), `:77` `heap_init`, `:152` `SharedHeap`, `:190` `mimalloc_alloc`/`mimalloc_free` |
| 7 | `@noalloc` checker rejects direct/transitive/family allocation | ◐ | Checker `35.semantics/noalloc_checker.spl`; kinds `:23-27`. **Not a compile gate** — sole non-self caller is `90.tools/verify/noalloc_manifest_scan.spl:172`, driven only by `scripts/audit/noalloc_manifest_scan.spl:12`, referenced by nothing in `scripts/check/` or `.github/`. DirectAlloc is 5 hard-coded string tags (`:116-126`); the audit detects only 2 of them |
| 7b | — | ✗ **circular hole** | `35.semantics/gc_boundary_check.spl:96` hard-codes `nogc_async_mut_noalloc → allocates: false`, matched by **prefix** (`:140`). So `…noalloc.mimalloc` and `…noalloc.memory` classify as non-allocating: a `@noalloc` fn calling `mimalloc_alloc` can never trip FamilyImport. Premises 6 and 7 contradict each other in-tree |
| 7c | Stale comment | — | `effect_verifier.spl:365-367` says the noalloc checker has "ZERO production call sites" — now stale, though "not a gate" still holds |
| 8 | noalloc scheduler is a cooperative scaffold | ✓ **worse** | `nogc_async_mut_noalloc/async/scheduler.spl`: `run_one_tick` (`:138-161`) poll body is the literal `0` (`:158`); `any_completed` initialised false (`:144`) and never assigned → always returns false; `run_until_complete` spins to the 10000 cap (`:171`). `TaskSlot` (`:37-42`) has **no** deadline/period/WCET/budget/release-time field |
| 8b | No WCET integration | ✓ | `wcet` appears in **zero** `.spl` files repo-wide |
| 9 | Docs say interleaving tests don't prove fairness | ✓ | `doc/07_guide/app/spipe/mission_critical_robust_sw.md:15-16` (hedge is "a single", narrower than "representative") |
| 10 | Enum: interpreter hard error | ◐ | Observed (`exit 1`) but **unconditionally**, with and without `SIMPLE_SAFETY_PROFILE=critical`, and via a path that delegates to the Rust seed. Pure-Simple source is warn+nil (`eval.spl:779-786`), abort default-off (`eval_tables.spl:875`), promoted under critical (`eval_decls.spl:294-298`) — **unverified by execution** |
| 10b | Enum: compiled/JIT nonfatal diagnostic | ◐ | Emit `50.mir/_MirLoweringExpr/switch_operators_calls.spl:2445` → `ctx.add_warning` (`driver_pipeline_lowering.spl:137-141`) — non-fatal as claimed, but the live JIT run printed **nothing** and returned nil-sentinel at exit 0. Weaker than claimed |
| 10c | Enum: wildcard on closed enum = warning | ◐ | In lint it is **inert, not warning**: `wildcard_match = "allow"` (`config_and_model.spl:164`), no lint code maps to it (`:605-630`). Interpreter side warn-only, no abort variant (`eval_tables.spl:978`) |
| 10d | No sound pre-execution check | ✓ | Self-documented as unsound: `switch_operators_calls.spl:2447-2462`, `eval_tables.spl:865-869` |
| 11 | Enum-exhaustiveness checker dead/unwired | ✓ | `35.semantics/lint/match_exhaustiveness.spl:101`; appears nowhere in `src/` outside its definition + re-export (`lint/__init__.spl:127`); in neither dispatch list. Behavioural: probe emitted the *text* `non_exhaustive_match` EasyFix (`fix/rules/registry.spl:90`), **not** `MEXH001`. `Linter.new()` registers MEXH001-006 descriptors (`lint_checks.spl:53-66`) nothing emits |
| 11b | …*because* of an ambiguous global enum-name registry | ✗ **conflated** | Two registries. The checker's own is `{text:[text]}` built per-call from `decl_indices` — **module-local** (`match_exhaustiveness.spl:112-120`), ambiguous via `matching_enums[0]` (`:581`). The genuinely **global** bare-name registry is `enum_reg_names`/`enum_reg_variants` (`eval_tables.spl:633-636`), first-wins, collision warning at `:665`. The causal link between the two is **UNSUPPORTED** — no commit or doc ties the unwiring to the registry |
| 12 | `required_comment` semantic checker not invoked by production lint | ✓ (call graph + behaviour; **not** sabotage) | Semantic `35.semantics/lint/required_comment.spl:86` has zero callers outside `lint/__init__.spl:57`. Entry `main_and_help.spl:322,330` → `cli_lint_commands.spl:46,177` → `entry_and_fixes.spl:342` → `:401`. Two flat dispatch lists, no name-keyed table: `lint_checks.spl:199-289`, `entry_and_fixes.spl:35-164` (exactly six AST checks) |
| 12b | — | ✗ **new: it is duplicated, not absent** | Production runs an independent **text reimplementation**: `lint_checks.spl:501` → `:545`, weak-rationale predicate `:505` (empty, `<10` chars, or `todo\|fix\|later\|unknown\|because\|n/a\|na`), emitting REQC001-004. Probe confirmed `warning[REQC001]` |
| 13 | Stub checker exempts `_noop_`, ignores empty bodies, stops on any `pass` | ✓ with qualifiers | `35.semantics/lint/stub_impl.spl`: `_noop_` `:160-162` (uses `starts_with`, so `helper_noop_x` is **not** exempt); empty `:164-166`; pass-marker stop `:182-184` (+`:420-425,:437-438,:443-444,:455-462`). Qualifier: the stop gates **STUB001/002 only** — STUB003 emits first at `:170-180`, and on the production path AST-STUB003 is filtered out (`entry_and_fixes.spl:124-126`) while a **separate text STUB003** fires from `lint_checks.spl:495-499`. Defect: the STUB001 hint at `:205` recommends `pass_todo`, which self-triggers STUB003 at `:171` |
| 14 | Unresolved identifier → global surviving to native link | ◐ **mechanism wrong** | Survival is real: `_MirToLlvm/core_codegen.spl:315-325` auto-emits `declare i64 @{name}`; freestanding is worse — `llvm_native_link.spl:2541` fabricates ~4023 weak NIL-returning stubs so the link **never fails**. But HIR **hard-errors** on unresolved identifiers (`hir_lowering/expressions.spl:398`); the leniency lives in **import admission** (`module_loader_core.spl:409-433`; W0407 warning-only at `use_resolution.spl:83-89`). No lenient-identifier flag exists. Naming trap: `unresolved_symbol_flags_for_unix_linker` (`_LinkerWrapper/native_linking.spl:110-118`) returns `--allow-multiple-definition` — *duplicate*-symbol tolerance, unrelated |
| 14b | Censuses exist | ✓ | `undeclared_imported_symbols_census.md:50` (1,226/766/380), `use_list_names_never_checked_2026-08-04.md:192` (636 @ 14.6%), `extern_backlog_enumeration.tsv` (2,377 rows), `jit_runtime_symbol_manifest_audit_2026-07-28.md:93`, `stage4_campaign_summary_2026-07-27.md:211` |
| 15 | Skip API surface | ✓ | `src/lib/nogc_sync_mut/spec.spl`: `skip:216`, `skip_it:201`, `pending:211`, `skip_context:249`, 9 platform helpers `:309-451`; decorators `decorators.spl:16,199,236,254,272` |
| 15b | Reason validation | ✗ **absent everywhere** | `skip("t","")` accepted by every API. Platform helpers take **no reason parameter at all** (auto-generated `:313`). The one construct resembling validation is a **fallback substitution**: `decorators.spl:220-223` (dup `:76-79`) silently substitutes `"Condition not met"` — flagged as the likely false positive for re-verifiers |
| 16 | Unified `SimpleArtifactManifest` as single policy surface | ◐ | Type `src/os/kernel/loader/artifact_manifest.spl:168`, fields `:170-186` (target, abi features, services, capabilities, `ManifestResourceLimits:133`, native/smf libs, content hashes, signature). **Zero production callers** — only consumer is `test/01_unit/os/kernel/loader/artifact_manifest_spec.spl`; its header `:39-40` concedes reading it off disk is "a later increment". Signature/hash fields exist, **no verification code**. **No design doc** — the "no second manifest" rule lives in the module header `:15-25` + `doc/01_research/domain/simpleos_production_host_master_plan.md:101-102,:137-141` |
| 17 | Two SMF writers; the older one returns an empty image | ✓ | Production `80.driver/smf_writer.spl` (interface hashes `:73,:75-87`; launch metadata `:50`, section 15 `:375-381`). Older `70.backend/linker/smf_writer.spl:273-276`: `pass_todo(...)` then `# Placeholder: callers receive an empty byte list, NOT a real .smf image.` `Ok([])` |
| 18 | Cert roadmap names aero-a/space-a; MC/DC, traceability, differential, sanitizers, WCET, semantic preservation, corpus all blocked/partial | ✓ | `doc/03_plan/cert/cert_roadmap.md:19` (aero-a/auto-d/space-a **blocked**, blocker "stage4 wall (miscompilation) → then MC/DC codegen instrumentation"); traceability `:27` PARTIAL (175/620, 445 orphan-down, 244 orphan-up); MC/DC `:29` PARTIAL; test rigor `:30` **FAIL**; formal `:32` PARTIAL; tool qualification `:33` BLOCKED; deferred C1 `:78` blocked, C3 `:80` queued, C4 `:81` queued, C6 WCET `:83` **not-scheduled**, C7 `:84` queued |
| 19 | SimpleOS loader could enforce minimum assurance | ✗ **refuted** | `src/os/kernel/loader/fs_exec_spawn.spl` + `fs_exec_resolve.spl` + `elf_loader.spl` enforce **no** signature, hash, ceiling or assurance concept. `cap_exec_gate.spl:24` exists but its header `:11-14` says it "never denies today" — every production call site passes `caller = 0`, hitting the sentinel bypass `:30-31`. Only real check is ELF magic/class/`e_machine` (`elf_loader.spl:137-190`) |
| 20 | `simple inspect` exists | ✗ | Zero occurrences of `inspect` in `src/app/cli/dispatch/table.spl`. `bin/simple inspect` prints `error: file not found: inspect` + usage banner and exits **rc=0** — a fail-open worth filing on its own |

**Not verified, by decision:** every external standards citation (ECSS revision
dates, JSF's 206/233 split, SPARK Silver, Ravenscar restrictions, TACLeBench,
capDL, CompCert, ARCHIE, the cFS/RISC-V study). Network fetch is blocked here and
a wrong revision date does not change the plan the way a wrong repo fact does.
They are recorded "as-cited, unverified" in the research doc §2. **Re-verify
against controlled documents before any of this becomes certification evidence.**

---

## What the verification changed about the plan

Four structural consequences the original proposal did not anticipate:

1. **PR 1 is bigger and more urgent than "de-duplication".** Project-level
   profile pinning is not merely duplicated — it is **entirely non-functional**
   (premise 4). `load_from_sdn` discards, `set_active_profile` has no callers,
   and all three SDN scanners always return `""`. There is no "migration from
   the legacy TOML form" to preserve, because nothing uses either form. That
   *simplifies* PR 1: implement the canonical `lints:`/`profile:` form only, and
   delete the TOML scanners rather than keeping them for compatibility.

2. **The enemy is reimplementation, not absence.** Premise 12b is the pattern:
   the semantic `required_comment` checker is unwired *and* a parallel text
   version is live with its own weaker predicate. Same shape at premise 13
   (AST-STUB003 filtered, text-STUB003 live) and premise 11 (MEXH001-006
   registered but a text EasyFix actually fires). **Wiring the semantic checker
   without deleting the text twin produces double diagnostics, not better
   coverage** — see [[reference_deleting_a_reimplementation_reroutes_not_dedupes]].
   Every wiring WP below must state which twin dies.

3. **The `@noalloc` story has a hole that must close before allocation classes
   are worth building.** Premise 7b: the family manifest asserts the noalloc
   family never allocates, and prefix matching extends that assertion to the
   allocator submodules the family itself exports. Building a five-class
   allocation lattice on top of a manifest that says `mimalloc_alloc` does not
   allocate is building on a false premise. Fix 7b **first**, in PR 3.

4. **Binary/loader enforcement is greenfield, not an extension.** Premises 16
   and 19: the manifest has no production callers and the loader checks nothing.
   The proposal's PR 9 ("extend the manifest, add link/load enforcement") is
   really "make the manifest load-bearing for the first time". Re-scoped below
   and moved behind the reachability gate, since the SimpleOS ring-3 spawn path
   is itself blocked ([[reference_simpleos_vmm_pml4_reads_zero_blocks_ring3_spawn]]).

---

## Shared contracts — frozen before any parallel work

WP-0 freezes four schemas. No later WP invents an alternate representation of
the same facts. This is the single serial dependency in the plan.

| Schema | Owner | Consumers |
|---|---|---|
| `FlightRuleV1` | WP-0 | every enforcement WP, docgen, release gate |
| `ResolvedAssurancePolicyV1` | WP-0 | lint, check, build, run, test, verify, package, loader |
| `CriticalSymbolSummaryV1` | WP-0 | closure, resource, contracts, traceability |
| `AssuranceStampV1` | WP-0 | object note, artifact manifest, linker, loader, inspector |

---

## Work packages

**Reach legend** — 🟢 reaches users on merge · 🟡 reaches users only after a lint
redeploy (premise #0.2) · 🔴 blocked behind stage-3 self-host or the SimpleOS
ring-3 gate; lands as tested-but-dormant code.

### Wave 0 — foundation (serial; blocks everything)

| WP | Task | Files | Model | Reach | Accept |
|---|---|---|---|---|---|
| **WP-0** | Freeze the four schemas above; create `src/compiler/00.common/assurance/flight_rules.spl` with `FlightRuleV1` + the initial `FLT-*` registry | new `00.common/assurance/**` | Sonnet | 🟢 (data + docgen) | Registry compiles; docgen emits the standards crosswalk + severity table from it; **no** hand-maintained severity table remains outside it |
| **WP-1** | Standards crosswalk `doc/04_architecture/language/assurance/standards_crosswalk_2026-08-07.md`: every `FLT-*` rule ↦ source, rationale, phase, analyzer, waiver policy, `critical`/`aero-a`/`space-a` level | doc only | Haiku | 🟢 | Every rule row has all seven fields; citations carry the "as-cited, unverified" marker; dormant/intrinsic/enforcement-gap status explicit |
| **WP-2** | Baseline census: current violations per `FLT-*`, read-only, reproducible | new scanner under `90.tools/verify/` + `doc/09_report/` | Sonnet | 🟢 | Zero source-behaviour changes; two runs give identical counts; report states its own coverage fraction (do **not** repeat the audit-script mistake of premise 7 — state what it cannot see) |

### Wave 1 — make the profile real (the biggest single win; depends on WP-0)

| WP | Task | Files | Model | Reach | Accept |
|---|---|---|---|---|---|
| **WP-3** | One canonical policy resolver in `00.common`; `ResolvedAssurancePolicyV1` threaded through the driver as **typed state**. `SIMPLE_SAFETY_PROFILE` demoted to subprocess serialization only | new `00.common/assurance/policy.spl`; edits to `driver_safety_severity.spl`, `handler_commands.spl`, `test_runner_args.spl`, `eval_decls.spl` | Sonnet | 🟡 | lint/check/build/run/test resolve an **identical** policy hash; CLI may raise, never lower a pinned `robust`/`critical`; deprecated aliases warn once; the interpreter's latch-at-init (premise 5b) is replaced by the passed policy |
| **WP-4** | Implement real SDN → `ProjectContext` mapping for the canonical `lints:`/`profile:` form; **delete** all three dead TOML scanners; wire `set_active_profile` | `80.driver/project.spl:81-90,:133`; `config_and_model.spl:335-352`; `handler_commands.spl:114-131`; `test_runner_config.spl:48-71` | Sonnet | 🟡 | A repo-root `simple.sdn` with `lints:\n  profile: critical` actually pins the profile — proved by a spec that fails when the key is removed. No TOML scanner remains |
| **WP-5** | Correct the stale normative text | `doc/02_requirements/language/mission_critical_profile.md:120-121`; add REQ-MC-013…022 | Haiku | 🟢 | REQ-MC-012 status reflects premise 5/5b; each new REQ names its enforcement phase (compile / integration / release) |

### WP-3.5 — discharge the 🟡 tier's reachability debt (blocks all of Wave 2)

Every 🟡 acceptance criterion below is **unobservable without this WP.** Per
premise #0.2, `bin/simple lint` runs a binary older than its source, so "REQC001
now fires from the semantic checker" cannot be checked by running lint against
an edited tree. The Reach column names that constraint; nothing else discharges
it.

| Task | Model | Accept |
|---|---|---|
| Own the lint-binary redeploy: a documented, repeatable build+deploy of `bin/release/<triple>/simple` from current `90.tools/lint` source, plus a **staleness probe** any later WP can run first | Sonnet | The probe fails on today's binary (which has `MEXH001` but not `MEXH006`, `lint_checks.spl:65`) and passes after redeploy. Note the `.mcp.json` launch-path skew and the `cp .new` + `mv` dance for "Text file busy" (`.claude/rules/code-style.md`) |

Every 🟡 WP's acceptance is amended to read: *run the WP-3.5 staleness probe
first; a WP that cannot prove it ran against fresh binary reports its result as
unverified, not as pass.*

### Wave 2 — close the semantic gaps (parallel; each states which twin dies)

| WP | Task | Files | Model | Reach | Accept |
|---|---|---|---|---|---|
| **WP-6** | Type-resolved `ResolvedMatchCoverage` in HIR, keyed by `scrutinee_type_id` + `enum_symbol_id` + variant **ids**. MIR lowering refuses to lower an unapproved incomplete critical match | new `20.hir` + `35.semantics` modules; `switch_operators_calls.spl:2445` | Sonnet | 🔴 | Missing variant and wildcard-on-closed-enum fail under `critical` in interpreter **and** compiled paths (premise 10b: JIT currently prints nothing). **Twin that dies:** the text EasyFix `non_exhaustive_match` (`fix/rules/registry.spl:90`) once MEXH001 fires |
| **WP-7** | Wire the semantic `required_comment` checker; **delete** the text reimplementation | `entry_and_fixes.spl:35-164`; delete `lint_checks.spl:501,:505,:545` | Sonnet | 🟡 | REQC001-004 still fire, from the semantic checker; predicate is the semantic one, not the `<10`-chars heuristic; **no double diagnostics** (assert exactly one REQC001 on the probe) |
| **WP-8** | Stub checker: remove the empty-body skip and the `starts_with("_noop_")` exemption; require a typed NoOp contract instead. Fix the STUB001-hint→STUB003 self-trigger (`stub_impl.spl:205` vs `:171`) | `stub_impl.spl:160-166,:182-184,:205`; `entry_and_fixes.spl:124-126` | Sonnet | 🟡 | Empty concrete body is an error under `critical`; `helper_noop_x` and `_noop_x` treated identically (by contract, not name); STUB003 has exactly one live source |
| **WP-9** | Skip governance: `skip_ref(id)` resolving into SDN tracking (category/reason/owner/requirement/alternative-evidence/venue/expiry/issue). Reject `skip_it`, bare `pending`, free-text-only, weak, expired, ownerless under `critical` | `src/lib/nogc_sync_mut/spec.spl:201-451`; `decorators.spl:16-272` | Sonnet | 🟡 | Every skip API validates its reason; the `"Condition not met"` silent substitution (`decorators.spl:220-223`, dup `:76-79`) is **removed**, not reused; platform helpers gain a required reason or a venue-coverage proof |
| **WP-10** | Import-admission closure: make `module_loader_core.spl:409-433` fail-closed under `critical`; promote W0407 (`use_resolution.spl:83-89`) from warning to error. Forbid the freestanding weak-stub fabrication (`llvm_native_link.spl:2541`) in a flight closure | as listed | Sonnet | 🔴 | Unresolved import is an error under `critical`; the ~4023 fabricated NIL stubs are absent from a flight link; census counts (premise 14b) drop measurably |

### Wave 3 — resource and control-flow boundedness (depends on WP-0; WP-11 first)

| WP | Task | Files | Model | Reach | Accept |
|---|---|---|---|---|---|
| **WP-11** | **Close the circular hole first.** Split the noalloc family manifest so `…noalloc.mimalloc` / `.memory` are not covered by the family's `allocates: false`; replace prefix matching with exact/explicit submodule rows | `gc_boundary_check.spl:94-106,:140` | Sonnet | 🔴 | A `@noalloc` fn calling `mimalloc_alloc` is **rejected** — spec proves it was accepted before and rejected after |
| **WP-12a** | **The `@noalloc` apparatus is vacuous end-to-end — fix that before the lattice.** Two independent reasons, both measured 2026-08-07 while landing WP-11: (a) `90.tools/verify/noalloc_manifest_scan.spl:159`, the ONLY real driver of `check_all_noalloc_fns`, registers every scanned fn with `family_module: ""` and never registers callees at all, so `FamilyImport` is **structurally unreachable through it regardless of a correct manifest** — the audit printed identical output before and after WP-11's fix; (b) **zero functions in the tree carry `@noalloc`**, so there is nothing for it to check even if it worked | `noalloc_manifest_scan.spl:159`; annotation rollout | Sonnet | 🔴 | The audit driver derives `family_module` per callee and the WP-11 regression case is reachable THROUGH the driver, not only through a direct unit call. Report the count of `@noalloc`-annotated fns before and after — if it is still 0, the WP is not done |
| **WP-12** | Allocation classes `none`/`init_only`/`bounded_pool`/`unbounded`/`unknown` over the existing checker; startup **seal**; steady-state gate | `noalloc_checker.spl:23-27,:116-126`; new lifecycle lib | Sonnet | 🔴 | Every critical symbol carries a class; `unbounded`/`unknown` reject; DirectAlloc no longer 5 hard-coded strings. **Needs WP-12a first** — a lattice over a driver that cannot observe callees classifies nothing. Also: the manifest's `allocates` boolean cannot today express "bounded static-region sub-allocation" (`baremetal.allocator`, `mimalloc` — no malloc/mmap/brk, caller-supplied `(base,size)`) as distinct from heap allocation; both collapse to `true`. Making that distinction expressible is this WP's core job |
| **WP-13** | Clean the noalloc facade: allocator exports move out of the default surface or the no-heap claim is corrected | `nogc_async_mut_noalloc/__init__.spl:1-5,:29-33,:76,:77,:152,:190` | Sonnet | 🟢 (lib) | Root export surface and the `alloc_allowed: false` claim agree — whichever direction is chosen, they stop contradicting |
| **WP-14** | Loop bounds (ranges, fixed collections, refinement types, constants), recursion SCC, stack frames, queue/task capacity — report-only first | new CFG/MIR analysis modules | Sonnet | 🔴 | No `unknown` termination result in the flight closure; report names the dominant call path, not just the total |
| **WP-15** | Object-level allocator-symbol scan of the steady-state closure | `70.backend` + `90.tools/verify` | Sonnet | 🔴 | Forbidden allocator symbol in a sealed build fails the link |

### Wave 4 — evidence and binary seal (mostly 🔴; sequence last)

| WP | Task | Reach | Note |
|---|---|---|---|
| **WP-16** | AoRTE obligations (init, globals, overflow, div, shift, cast, bounds) with per-SymbolId proved/checked/assumed status | 🔴 | Feeds `doc/03_plan/cert/` formal lane |
| **WP-17** | Ravenscar subset over existing task APIs + a **real** `run_one_tick` (premise 8) | 🔴 | The scheduler must schedule before any timing claim; this is a prerequisite, not a nicety |
| **WP-18** | Target timing model + WCET adapter + response-time report; import TACLeBench as an independent corpus | 🔴 | `wcet` currently appears in zero `.spl` files; cert roadmap C6 is **not-scheduled** |
| **WP-19** | Make `SimpleArtifactManifest` load-bearing: first production caller, real signature/hash **verification** (fields exist, code does not) | 🔴 | Greenfield, not an extension |
| **WP-20** | `AssuranceObjectNoteV1` + linker compatibility validation | 🔴 | Requires the production SMF writer; the `70.backend` writer returning `Ok([])` must be excluded from sealed builds or completed |
| **WP-21** | Loader `minimum_assurance` enforcement; un-stub `exec_cap_check` (every caller passes `caller = 0`) | 🔴 | Also gated by the VMM PML4 ring-3 blocker |
| **WP-22** | `simple inspect --assurance` subcommand | 🟢 | Also fixes the standalone fail-open: `bin/simple inspect` currently exits **rc=0** on an unknown subcommand |
| **WP-23** | Test-vacuity + mutation checks for critical requirements | 🟡 | Highest-leverage evidence WP given the repo's false-green history |

---

## Merge order

WP-0 → WP-1/WP-2 (parallel) → **WP-3 + WP-4 + WP-5** (the profile actually
working is the gate for every enforcement WP) → **WP-3.5** (without it no 🟡
result is observable) → Wave 2 in parallel → **WP-11 before any other Wave-3
WP** → WP-12…15 → Wave 4.

**WP-22 can jump the queue** — it is 🟢, small, and closes a live fail-open.

---

## Cross-cutting rules for every agent

- **Never claim a check is wired based on sabotage** (premise #0.2). Positive
  call graph from `main_and_help.spl:322` + a live behavioural run on a probe.
- **Never accept an absence-grep as proof.** Grep for *callers of the symbol*.
  This plan's premises 11, 12, 16, 19 were all absence-shaped and three of them
  changed verdict under a positive call graph.
- **Every wiring WP names the twin that dies.** Wiring without deleting the
  reimplementation yields double diagnostics.
- **A correct spec that fails stays RED** with a `doc/08_tracking/bug/` record
  (`.claude/rules/testing.md`). Do not soften it.
- **Update the LLM wiki in the same commit** —
  `doc/00_llm_process/{feature,layer}_expert/*/skill.md`
  (`.claude/rules/vcs.md`). This is unconditional.
- Do not touch files outside your WP; commit and push per WP.

---

## Execution log

| WP | Commit | Outcome |
|---|---|---|
| WP-11 | `ed493da4c99` | **Landed.** Exact-or-dot-boundary matching replaces `starts_with`; `…noalloc.mimalloc` + `…noalloc.baremetal.allocator` marked allocating, `…noalloc.memory` deliberately NOT (WP-13 proved `SharedHeap.allocate()` returns a logical `BinaryRef`, never an address — marking it would be a false positive as damaging as the false negative). Regression through the real checker: before `4 total, 2 passed, 2 failed` → after `4 total, 4 passed, 0 failed`. Also fixed the `pure → gc_async_mut` alias gap and documented the dead `async` row |
| WP-13 | `977a401a05c` | **Landed**, comment-only. Consumer audit found 0 facade callers for `mimalloc_*`/`SharedHeap` and 3 submodule-path callers for the allocator classes; `allocator.spl`/`mimalloc.spl` sub-allocate inside a caller-supplied region with no malloc/mmap/brk/libc. So the exports are legitimate and the *claim text* was wrong — corrected the header, kept the API |
| WP-22 | `21154033918` | **Landed, but the filed premise was wrong.** `bin/simple inspect` exits **rc=1**, not rc=0 — measured across 7 token shapes; `main.rs:1674` has read `return 1` since introduction. Real (smaller) fix: the fall-through returned a flat `1`, indistinguishable from a genuine file-execution failure; now returns `2` for usage errors. Function-level RED→GREEN proven; **process-boundary verification impossible today** — no self-hosted binary is deployed |
| REQ-MC-023 | `82fd43ad4df` | **Landed.** `W-MC-RES-001 unwrapped_foreign_resource`: allow in moderate/strict/robust, warn in `critical`, deny at v2 — same two-phase pattern as REQ-MC-002/011. Marked SPECIFIED-NOT-IMPLEMENTED with all three blockers named. Skipped REQ-MC-013…022 (reserved by WP-5). No `doc/06_spec` entry written: that tree is generated from `test/**` and no sspec source exists yet, so writing one would fabricate evidence of a test that does not run |
| Foreign-resource migration | `c038cd1e6df` | **Blocked, correctly.** The tier→strategy hypothesis was **refuted**: strategy is selected by per-resource `@sffi` metadata + use-site sigil (`R`/`*R`/`@R`), NOT by defining tier — tier only constrains legality. Census: 85 release-families. Migration cannot proceed because `resource`/`@sffi` parsing does not exist (WP-A). Pilot spec left RED with a bug record rather than hand-rolling wrappers that would reproduce the boilerplate `resource` exists to delete |
| WP-B | `6b2be03f435` | **Landed.** `@T`/`-T` ownership sigils (`*T` already parsed). Ownership-kind recorded at flat-bridge time, not parse time — WP-C's resource registry isn't populated yet when the raw parser sees a sigil. `@R` gated on `thread_safe:` metadata. 6/6, sabotage-verified. **Recovery note:** this WP's fully-verified, unlanded work (4 files + spec) was silently wiped from the working copy mid-session by a concurrent jj snapshot/reconcile operation; recovered via `git log --all -- <path>` against jj's own periodic snapshot commits — see [[reference_shared_wc_uncommitted_work_wiped_recover_via_jj_snapshot_commits]]. First recovery pass missed `core/types.spl`, caught only because the re-run spec failed 5/6 instead of reproducing 6/6 |
| WP-2 | `c2eeaa43db6` | **Landed.** Baseline census scanner, `90.tools/verify/flight_rule_census_scan.spl` — read-only, does not invoke the stale lint binary. Per rule reports exactly `intrinsic`/`checked`/`uncheckable`, never a silent omission. **Real number: 2 of 32 rules are `checked` today** (FLT-IMP-001/002); the rest are intrinsic or stated enforcement gaps. 6/6, sabotage-verified. Also recovered from the same wipe as WP-B |
| WP-6 | `10a94ada1d3` | **Landed on the second attempt.** `ResolvedMatchCoverage` id-keyed by scrutinee_type_id+enum_symbol_id+variant ids (`20.hir/match_coverage.spl`); MIR lowering emits a hard error under `critical` for an incomplete match with no wildcard, scoped to arms carrying an explicit `EnumName.Variant` qualifier. 11/11, sabotage-verified. **The first push (`35886a28c04`) silently dropped the `switch_operators_calls.spl` hunks** — that file was wiped from the WC between the pre-commit lint pass and the commit build; `git cat-file -e origin/main:<path>` caught it (the marker grep came back 0). Recovered the hunks from a jj snapshot commit, but that snapshot PREDATED WP-E's own already-landed edit to the same file — merged by hand onto `origin/main`'s current content rather than overwriting, which would have reverted WP-E. Re-verified both WP-6's spec (11/11) and WP-E's own spec (5/5, unaffected) before the second push |
| WP-8 | `b19b8bedbcf` | **Landed.** NoOp exemption changed from name-matching (`starts_with("_noop_")`) to a structural contract: exempt only if the body is exactly one `pass_do_nothing("reason")` call, non-empty reason required. `_noop_x`/`helper_noop_x` proven identical under the new contract. STUB001's hint no longer recommends `pass_todo` (which is itself a STUB003 placeholder — the self-trigger this WP was tasked with fixing); recommends the exempt contract shape instead. Empty body now hard-errors under `critical`. 60/60, sabotage-verified. Caught and recovered its own mid-task WC clobber |
| WP-9 | `36137a043d8` | **Landed.** Fabricated placeholder skip reasons (`"Condition matched"`/`"Condition not met"`) removed from `decorators.spl` — a skip with no real reason is rejected under `critical`, not silently faked. New `skip_governance.spl`: SDN-tracked `SkipRecord` (category/reason/owner/requirement/alternative_evidence/venue/expiry/issue), validators reject skip_it/bare-pending/free-text/weak/expired/ownerless under `critical`. 23/23 + 4/4, sabotage-verified. **Filed two real bugs**: the Rust seed's `bin/simple test` hardcodes a BDD dispatch intercept on functions named `pending`/`skip_it`/`skip` that bypasses the `.spl` body entirely (governance on those three names is unreachable via the seed's test runner — proved via a differently-named `skip_via_ref` instead); a pre-existing lint crash (stmt-arena OOB) on `decorators.spl`, reproduced identically against unmodified HEAD |
| WP-10 | `722ca2a06bb` | **Landed.** `module_loader_core.spl`'s lenient already-registered-name fallback now hard-fails under `critical`; W0407 promoted `WARNING`→`ERROR` under `critical`; `llvm_native_link.spl`'s fabricated-stub exemption now also disables under a flight closure (`SIMPLE_NO_STUB_FALLBACK=1` OR strictness ≥ `critical`), reusing the pre-existing strict-link mechanism rather than inventing a new flag. Fabricated-stub COUNT is unchanged by design — this alters *classification* (which stubs get refused vs. exempted), not the emission itself. Sabotage-verified both source pieces. **`llvm_native_link.spl`'s lint could not be verified by the agent** (sustained SIGTERM under load, reported honestly rather than hidden) — I lint-checked it myself afterward: 8 pre-existing errors (`primitive_api`, `COLL006`), confirmed identical against the pre-WP-10 baseline blob, none introduced |
| WP-14 | `7ccd4efc144` | **Landed.** Loop-bound census (`90.tools/verify/termination_census_scan.spl`): range/fixed-collection loops classify `bounded`; everything else `unknown`, always naming the function — never a silent omission. Recursion SCC detection as a separate category. Report-only, no enforcement. 6/6, sabotage-verified |
| WP-15 | `97c293d3cc7` | **Landed.** Object-level allocator-symbol scan (`90.tools/verify/allocator_symbol_scan.spl`), exact-match only (learned from WP-11's substring-match defect, not repeated here) against a real `nm -u` read of `src/runtime/runtime.o`. "Sealed build" reuses WP-10's `flight_closure` predicate rather than inventing new terminology. Enforcement wiring into `llvm_native_link.spl` deliberately deferred — WP-10 had an in-flight edit to that exact file at the time, and landing on top of it risked exactly the WP-6 hunk-loss incident; documented as a stated one-line-per-call-site gap, not silent |
| WP-H | `51e08eb7ead` | **Landed.** `sffi_gen/resource_wrapper_gen.spl`: acquire→static factory with invalid-sentinel check returning `T?`, methods borrow, release→one-shot consuming `close()`. Targets the CURRENT opaque-handle pattern deliberately, not `resource R` syntax — confirmed unreachable from production source before designing the emitter's output shape. Golden-file spec against the `rt_file_*` family, 5/5, sabotage-verified |
| WP-I | `fb8f796903f` | **Landed.** Root cause: WP-E's drop *timing* comes entirely from the shared `MirLowering` pass (used by every backend), so the interpreter needed zero timing logic — the actual gap was one level down, `MirInterpreter.execute_instruction` had no arm for `MirInstKind.Drop` and fell through to `UnsupportedOperation`. Fix: a no-op `Drop` arm (no backend wires a real release extern yet — that's downstream of WP-H). 3/3 interpreter-mode, sabotage-verified; WP-E's own spec re-verified unaffected in both modes (5/5 each). Detected and recovered its own mid-task WC wipe before landing |
| WP-3.5 | (pending push) | **Probe delivered, redeploy blocked (correctly, not faked).** `scripts/check/check-lint-binary-staleness.shs`: grep-only, fails on today's binary (`MEXH006`/`W-MC-RES-001` both missing), passes on a `--selftest` synthetic fresh fixture. Root cause found while building the probe: the deployed binary isn't merely stale, it's the **Rust seed** (`--version` prints the seed banner) — `MEXH001` lives in `src/compiler_rust/compiler/src/lint/types.rs` too, so no pure-Simple-only redeploy can ever surface `MEXH006`/`W-MC-RES-001` without a genuine Stage-3 self-host. That self-host is separately, actively blocked: a same-day `--full-bootstrap --deploy` run reached Stage 3 and SIGSEGV'd during `phase=monomorphize`/MIR lowering (exit 139, ~394s, 10.7GB peak RSS) — see `t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`. Not re-attempted here (prior sessions already spent hours confirming this exact wall today; re-running reproduces the same SIGSEGV, doesn't fix it). Process doc: `doc/07_guide/compiler/lint_binary_redeploy_process.md`. **Every 🟡 WP downstream must run this probe first and, until the Stage-3 SIGSEGV is fixed, report lint-based results as unverified, not pass** |
| WP-5 | `de437daea00` | **Landed, corrected before landing.** REQ-MC-013 (canonical policy resolver, WP-3) and REQ-MC-014 (SDN profile pinning, WP-4) documented; REQ-MC-015…022 explicitly reserved and left unallocated rather than padded. The agent's own report cited a test file (`project_lints_profile_pin_spec.spl`) that does not exist anywhere in the repo — caught by `git cat-file -e` before landing and corrected to the real files (`run_sdn_lints_profile_spec.spl`, `lint_profile_spec.spl`). Landed by me after its push attempts were defeated by shared-WC lock contention |
| W-MC-RES-001 | `df82283d449` | **Landed (implemented, DORMANT).** `src/compiler/35.semantics/lint/unwrapped_foreign_resource.spl`, reuses `resource_families.acquire_verbs()`, wired through lint's existing single levels-projection (not a 5th severity table) — allow default, warn `critical`. Text-level, intraprocedural, single-assignment heuristic, ceiling documented in-module. 17/17. **I landed this one myself after the agent's first-try-clean report went unverified** — its own sabotage proof was missing, so I ran it: stubbing `_ufr_is_acquire_name` → `17 total, 10 passed, 7 failed`, reverted → `17/17`, oracle confirmed live. Push also hit a genuine race (another session landed between fetch and push, `non-fast-forward`) — succeeded on retry-after-refetch, the normal case the plumbing procedure exists for |
| WP-D residual | `45c0f068163` | **Landed.** The 1 RED spec was a real catalog gap: `load` was missing from `acquire_verbs()`, so `rt_image_load` classified as a plain method and left the family acquire-less. Engine now `17 total, 17 passed, 0 failed`, sabotage-proven both directions |
| Lint parser `describe`-fn crash | `3695df74c59` | **Landed (by me, not the agent).** `try_parse_bare_ident_string_call` consumed only the string argument, so the pure-Simple parse path rejected `describe "...", fn():` — a form the seed accepts — and lint skipped that file's AST checks. Fix adds a comma-arg loop. Defect 2 (silent skip) did **not** exist: the lint path already reports PARSE001 with a distinct exit code 3. **Process note:** the agent reported commit `606bae83998`, which is a *different session's* commit; none of its three files were on `origin/main` and the work sat uncommitted in the shared WC. Its tree-size check "passed" because it measured someone else's healthy tree. Verify landings by file (`git cat-file -e origin/main:<path>` + marker grep), never by hash |
| PoolLinkedList indexed-field receiver | `797918c8987` | **Library bug fixed (level b); language limitation stays OPEN.** `self.nodes[idx].field = v` fails whenever the indexed receiver is itself a field access. Probes in both live `.spl` `eval_assign_expr` sites never fired and the message text has exactly one emitting site — `src/compiler_rust/compiler/src/interpreter/node_exec.rs:916`, whose assignment `Case 2` only handles `array_expr` as a bare `Expr::Identifier`. No editable `.spl` fix site exists, so `PoolLinkedList` was restructured to parallel primitive arrays (same pattern as `FixedMap`, `57f7f44849f`) and `ListNode` deleted. Sabotage: `5 total, 2 passed, 3 failed` → reverted `5 total, 5 passed, 0 failed`. The type's old spec was text-scan-only, which is why this shipped broken |
| WP-3 | `4817dd06f0f` | **Landed.** Canonical policy resolver in `policy.spl`/`policy_names.spl` replaces the 4 live severity tables (lint dict / driver enum / interpreter bool / SDN reader) with one resolution path across 5 call sites. `24/24` + `2/2`; falsifiability proven by sabotaging the canonical alias table → `19 passed, 5 failed`, exactly the five sites, confirming each calls the real resolver rather than a stale copy. Local WC was 194 commits stale; diffed both directions against 3 files WP-4 had since touched, confirmed non-overlapping edit regions, reset+reapplied rather than clobber — anti-clobber protocol applied correctly (`.claude/rules/vcs.md`) |
| WP-D | `57da6077b69` | **Landed** (Haiku). Fail-closed convention inference (`infer_family_conventions` + verb classifiers) in `35.semantics/resource_families.spl`. 16/17 specs; the 1 failure is a real engine gap, filed separately (`resource_family_infer_rt_image_fails_2026-08-07.md`), not swept under. Census ratio ("how many of the 85 families infer cleanly") is **not measurable from Appendix A** — it lists only a representative sample, not all 85 family names; correctly reported as unmeasurable rather than estimated after an unmeasured "~80-85/85" guess was rejected and sent back |
| WP-12a input (collections) | `57f7f44849f` | **Landed — real fix, not comment-only.** `FixedArray`/`FixedStack` now reserve full capacity in `new()` and write by index (no per-`push()` growth); `FixedMap` refactored from per-op `FixedMapEntry` allocation to parallel primitive arrays, matching `FixedSet`/`RingBuffer`'s already-correct pattern. Regression: `FixedArray`/`FixedStack` `items.len()` 0/3/0 → 8/8/8 (`4/4` pass); `FixedMap` `3/3` pass. Zero production consumers for `FixedArray`/`FixedStack`/`FixedMap`/`FixedSet` (test-only); `RingBuffer`'s one consumer (`src/os/realtime/scheduler.spl`) was already correct and untouched. Stays RED only where genuinely blocked: true inline/static storage needs `[T; N]` sized-array support, which parses but discards its size (`parser.spl:781-798`) — that gap is the WP-12 lattice's remaining dependency. Surfaced a second, more severe defect mid-investigation: `PoolLinkedList.push_back`/`push_front`/`pop_front`/`pop_back`/`remove_at` fail at runtime (`semantic: invalid assignment: complex indexed field receiver is not supported`), filed separately, never caught by its own spec (text-scan only) |

**Method note earned the hard way:** the WP-22 premise came from a verification
agent's report that was never independently measured before being filed as a bug.
An agent-reported measurement is a hypothesis until re-measured — the same
standard this plan applies to absence-greps applies to reported numbers.

## Defects surfaced by this audit — where each is tracked

Newly filed (2026-08-07):

- `doc/08_tracking/bug/noalloc_family_manifest_prefix_match_exempts_its_own_allocators_2026-08-07.md`
  — premise 7b, the circular hole. Blocks WP-12.
- `doc/08_tracking/bug/cli_unknown_subcommand_exits_zero_fail_open_2026-08-07.md`
  — `bin/simple <unknown>` exits **rc=0**. Paired with WP-22.
- `doc/08_tracking/bug/noalloc_collections_backed_by_growable_heap_array_2026-08-07.md`
  — `nogc_async_mut_noalloc/collections/*` claimed "no heap allocation" but
  are backed by a real heap `[T]` array. FIXED for `FixedArray`/`FixedStack`/
  `FixedMap` (reserve-once / parallel-array patterns, `57f7f44849f`); `FixedSet`/
  `RingBuffer` were already correct. Stays RED only for true inline/static
  storage, which needs a language feature that does not exist (`[T; N]` is
  parsed but its size is discarded, `parser.spl:781-798`). WP-12 input.
- `doc/08_tracking/bug/pool_linked_list_push_fails_complex_indexed_field_receiver_2026-08-07.md`
  — `PoolLinkedList.push_back`/`push_front`/`pop_front`/`pop_back`/`remove_at`
  fail at runtime with `semantic: invalid assignment: complex indexed field
  receiver is not supported`. Found mid-investigation of the bug above; its own
  spec never caught this because it's text-scan-only.

Already tracked elsewhere — pointers, not new records:

- `70.backend/linker/smf_writer.spl:273-276` returns `Ok([])` (empty `.smf`
  image) → `doc/08_tracking/bug/smf_reader_bridge_silent_nil.md`, named by the
  `pass_todo` itself.
- `exec_cap_check` (`cap_exec_gate.spl:24`) never denies; every production call
  site passes the `caller = 0` sentinel (`:30-31`) →
  `doc/08_tracking/bug/execve_spec_blocked_by_dead_ipc_cap_gate_and_missing_rt_copy_user_byte_2026-08-06.md`.

Carried inside a WP rather than filed standalone (fix and regression live
together):

- `stub_impl.spl:205` recommends `pass_todo`, which self-triggers STUB003 at
  `:171` → WP-8.
