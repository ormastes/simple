# Plan: Script-Mode / Lint-Tier Axis and the Future "Reliable Mode"

## Summary

This plan introduces a **second strictness axis** for Simple — the *script-mode / lint-tier* axis (`moderate < lib < reliable`) — and lays out an honest, phased path to the top rung, "reliable mode." The axis is **code-strictness**, orthogonal to the existing **stdlib memory/runtime tiers** (`nogc_sync_mut`, etc.); the two must never be conflated.

"Reliable mode" is defined as a **ladder**, not a monolithic guarantee:

- **rung 1** = the current lint level (R1: lint at compile *and* link, configurable take-or-config severity),
- **rung 2** = a local/internal-primitive-use check, surfaced as a **WARNING** with verified auto-fix (R2/R3),
- **rung 3** = a formal-verification **COVERAGE** meta-check — *does each feature-level public class / main-class-of-file HAVE a discharged proof* (R4), distinct from running proofs.

This is exactly the "strict lint + `@deny(non_exhaustive_match)` + bounded Lean coverage" realization that `doc/07_guide/language/simple_language_comparison.md:31` prescribed when it rejected the unprovable "High-robustness mode." It supersedes that rejected idea by being **configurable and context-dialed**, not asserted as a blanket property.

Two pieces are genuinely large/risky and are presented as such with their blockers intact: **R1's link-half** (no link-time lint exists; SMF carries no type signatures) and **R4** (the only Simple→Lean path is interpreter-only behind the M12 ceiling; the pure-Simple `LeanBackend` is a stub).

---

## Two Axes (do not conflate)

Simple now has **two independent classification axes**. A module/build target picks one value on each, and they **compose freely**.

| | **Axis A — Stdlib Memory/Runtime Tiers** (existing) | **Axis B — Script-Mode / Lint-Tier** (NEW, this plan) |
|---|---|---|
| What it controls | Memory model, allocation, async/GC capability | Code-quality strictness: which lints fire, at what severity, and whether proof-coverage is gated |
| Values | `common`, `nogc_sync_mut`, `nogc_async_mut`, `gc_async_mut`, `nogc_async_mut_noalloc` | `moderate`, `lib`, `reliable` |
| Source of truth | `.claude/rules/structure.md:10-14`, `CLAUDE.md` (src/lib block); default tier = `nogc_async_mut` | New: `simple.sdn [lints] profile=`, CLI flag, `@profile()` header attr; default = `moderate` |
| Selects by | directory under `src/lib/` | build target / file manifest |

**Orthogonality (the one sentence that prevents conflation):** any strictness tier composes with any memory tier — e.g. a `nogc_async_mut_noalloc` baremetal module can be built under `reliable`. "reliable" is **not** a memory tier; it never changes the runtime/allocation model.

Today neither axis is in `doc/glossary.md`; this plan adds both (Axis A as a mirror of `structure.md`, Axis B as the new canonical definition) so the disambiguation has a home.

---

## Script-Mode / Lint-Tier Ladder

**Assumption (stated, not deferred to the user):** `moderate` = relaxed/casual scripting strictness; `lib` = library-code strictness; `reliable` = strictest = current lint level **+** local-primitive-use check **+** formal-verification coverage.

| Tier | Audience | Lint behavior | Primitive-use check (R2) | Proof-coverage (R4) | Rungs |
|---|---|---|---|---|---|
| **moderate** | scripts, prototypes, examples | advisory only; most `deny` defaults downgraded to `warn`/`allow` | off | off | — |
| **lib** | library / reusable code | full current lint at error severity + minimal-public-surface / export-boundary checks (`wide_public` W0404, `star_export`) | off (or warn, opt-in) | off | rung 1 |
| **reliable** | safety-relevant units | rung 1 lint **+** rung 2 **+** rung 3 | **WARNING** + verified auto-fix | **coverage gate**: each feature-level public class & each main-class-of-file HAS a discharged proof | 1 + 2 + 3 |

**Rung → requirement spine (the doc's backbone):**
- **rung 1** = current lint level, available at compile **and** link → **R1**
- **rung 2** = local/internal-primitive-use WARNING + verified autofix → **R2** (CLI) + **R3** (LSP wiring)
- **rung 3** = formal-verification COVERAGE meta-check → **R4**

Every rung is overridable through `[lints]` / `@allow`/`@deny` — strictness is *dialed*, never hard-coded.

---

## Relationship to the rejected "High-robustness mode"

`doc/07_guide/language/simple_language_comparison.md:31` lists **"High-robustness mode | Not proven | Replace with strict lint or `@deny(non_exhaustive_match)` wording."** Line 13 of the same doc says "Replace 'high-robustness mode' with deny-level match-exhaustiveness lint configuration." The phrase never named a shipped feature — `simple_language.md` only ever used aspirational "Rust-like robustness" language (lines 22/24).

**"reliable mode" IS that prescribed fix, made concrete.** The difference:

- **Rejected idea:** a single opaque "mode" asserting robustness as a blanket guarantee — unprovable, hence rejected.
- **reliable mode:** a **configurable lint tier** = (a) the existing strict lint level incl. `@deny(non_exhaustive_match)` (the doc's own recommendation), (b) a local-primitive-use warning with verified autofix, (c) a proof-**coverage** meta-check that asks only "does this unit have a discharged proof?" — *not* "is this code formally proven correct by magic." Each ingredient already half-exists in the repo; each is overridable. It promises **process** (lint + proof-coverage), not an unfalsifiable property.

A forward-pointer addendum should be added next to line 31: *"Superseded by: reliable strictness tier (glossary.md#strictness-tiers)."* The dated verdict snapshot (2026-06-07) is left intact.

---

## R1 — Lint during compile AND link, with take-or-config mode

**Current state.** Lint is *not* a compile phase. The driver reaches it only by shelling out: `rt_process_run(simple_bin, ["lint", path])` at `src/compiler/80.driver/driver_public_compile.spl:117`. The standalone CLI engine (`src/compiler/90.tools/lint/_LintMain/config_and_model.spl`) has the config substrate R1 wants — `enum LintLevel{Allow,Warn,Deny}`, `LintConfig` parsing `simple.sdn [lints]` via `find_project_sdn`, per-name `get_level/set_level`, `@allow/@warn/@deny` header attrs (`apply_file_attributes`), `apply_config_level`/`should_keep_lint_result`, and `--deny-all/--warn-all` (`lint/_LintMain/entry_and_fixes.spl`). But the IDE/LSP/build path (`src/app/cli/query_lint.spl` `_emit_source_lint_diagnostics`) calls the `35.semantics/lint/*` checks **directly with no `LintConfig`**. **Two engines, one config that reaches only one of them.** Link-time lint does **not exist**: `link.spl`/`mold.spl` emit only `parse_linker_diagnostics()` over external linker stderr; `SymbolGraph` (`symbol_analysis.spl`) and `SymResolution` (`sym_resolver.spl`) are defined and re-exported but have **no construction site** in the live `Linker.link` path.

**Gap.** (1) No profile/tier abstraction — only `--deny-all/--warn-all`. (2) `map_lint_code_to_config_name` returns `""` (unconfigurable) for ~15 code families (W001, ST001, S001, CC001, CLOS001, RET001, BOOL001, SAFE001, W040x) — a profile selector cannot govern them. (3) Compile-half is a subprocess, not a phase; link-half is greenfield. (4) Cross-module primitive-escape lint is blocked: `SmfSymbol` (`obj_taker.spl:39`) + coarse `SymbolType` carry **no param/return signatures**; `ObjTakeResult.Code.ty: TypeInfo?` is `nil` at every site.

**Steps.**

| # | Step | Effort | Risk |
|---|---|---|---|
| 1 | Add `profile` field + `profile_default_levels(profile)` to `LintConfig` (`lint/_LintMain/config_and_model.spl`); resolve from CLI flag / `[lints] profile=` / `@profile()`, same precedence as existing overrides | M | Only honored on CLI path until step 3 lands — document the limitation |
| 2 | Fill `map_lint_code_to_config_name` for the ~15 unmapped families with stable config names + default levels | M | Each needs a name matching future `@allow/@deny` ergonomics |
| 3 | Reconcile the two surfaces: route `query_lint.spl _emit_source_lint_diagnostics` through `LintConfig` (load `find_project_sdn` + `apply_file_attributes`, then `should_keep_lint_result`/`apply_config_level` per diagnostic). Promote `LintConfig` to a shared leaf module both compile & link consume | L | `35.semantics` checks emit heterogeneous Warning structs w/o code-mapping; needs a uniform code→config adapter per pass |
| 4 | Compile-half: make lint a real in-process phase in `80.driver` after semantics (reuse already-parsed AST; avoid double-parse) instead of the `:117` subprocess; generalize `lint_cache.spl` (today hardcoded to `RequiredCommentWarning`) to all passes | L | In-process lint adds compile latency |
| 5 | Link-half substrate: construct `SymbolGraph` + `SymResolution` from the resolved object/SMF set in `mold.spl` (reachability/dead-symbol + defined/undefined) | L | Reachability needs correct entry-point seeding; perf on large images |
| 6 | Link-half pass: new link-time lint over the linked symbol graph (dead-public-symbol, unresolved-as-lint, whole-program exported surface), severity via shared `LintConfig`, output via `MoldDiagnostic` shape | L | Distinguishing link-only findings from per-module duplicates; false positives on intentionally-exported `.lsm` archive symbols |
| 7 | Cross-module primitive-escape: add a type-signature metadata channel to SMF (extend `SmfSymbol`/`SmfSymbolRaw` or a new NOTE-SDN section) so primitive_api can run on the linked public surface | XL | On-disk format change + writer/reader + Rust SFFI raw struct; back-compat for existing `.smf`/`.lsm`. This is the L-vs-XL discriminator for link-side primitive lint |

**Risk & blockers.** The link-half is the genuinely large piece. `SymbolGraph`/`SymResolution` are dormant (grep-verified: no call site in `mold.spl`) — wiring them is real work, not a toggle. Precise cross-module primitive lint is **impossible** until step 7's signature channel exists. The compile-half is a bolt-on subprocess today, so R1 has gaps on **both** ends.

---

## R2 — reliable = current lint level: internal-primitive use as a WARNING + verified auto-fix

**✅ DONE (public-API surface) 2026-06-16.** The deny/warn split (step 1) and the LSP-path WARNING
(step 5) are resolved without any arena rewrite or bootstrap. `primitive_api` now surfaces on the
LSP/build path (`src/app/cli/query_lint.spl` → `_emit_primitive_api_text`), tier-gated and
severity-routed by the P0 profile (`reliable`/`lib` → deny/sev1, `moderate` → warn/sev2, no profile
→ silent), reusing `param_tag`'s text signature parsers (no parser/arena → dodges both the
interpreter `parse_module` crash and the bootstrap closure-bloat). Verified end-to-end through
`query.spl check … --format json` (pure-math exemption + `text`-exclusion confirmed). See
[[r2_primitive_check_draft]]. **Remaining:** step 3 (extend pub-only → **internal** fns under
reliable) — needs the canonical compiled-path lint changed + a bootstrap; tracked, not blocking.

**Current state (historical, pre-fix).** Two parallel primitive lints exist. The **text-scanning** rule `src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl` (`check_primitive_api`) scans `pub fn/pub me/pub static fn`, flags bare numerics `{i64,i32,…,f32}` in public params/returns, exempts pure-math (`_all_same_primitive`), and emits an **`EasyFix` with `FixConfidence.Uncertain` whose `new_text == the original line` (a no-op placeholder)**. The **AST twin** `src/compiler/35.semantics/lint/primitive_api.spl` is higher fidelity (fields + all visibility + `@allow`) but is **exported and never invoked** in the live pipeline. `primitive_classification.spl` (convertible/blocked/intentional/exempt + 12-entry `DomainWrapperCatalog`) is pure data, wired to neither.

**Severity contradiction (concrete code fact):** `build_default_levels()` sets `levels["primitive_api"]="deny"` (`main_part1.spl:62`), but the `Lint` is constructed `LintLevel.Warn` (`main_part2.spl:227`). Effective severity depends on path. R2 wants WARN.

**Gap.** No "internal/local" primitive concept distinct from public-API surface (checks key off `pub`/visibility). No real autofix (the rewrite is a no-op). No "apply after user verifies" gate — the live `lint_entry_run_fix` (`src/app/cli/lint_entry.spl`) has only `--dry-run` (preview, never writes) vs Safe-apply; `--fix-all` applies `Uncertain` fixes but simultaneously **disables all confidence verification**. The y/n/a/q `InteractiveFix.prompt_fixes` lives only in the **unused** `fix/main.spl async main()`.

**Steps.**

| # | Step | Effort | Risk |
|---|---|---|---|
| 1 | Reconcile the deny/warn contradiction: source emission severity from `get_level(tier)` so `primitive_api` = `allow`(moderate)/`warn`(lib, opt-in)/`warn`(reliable). Removes the `:62` vs `:227` split | M | Changing default could flip many files to warnings — gate elevation behind `reliable` |
| 2 | reliable-tier primitive check via the higher-fidelity path. **BLOCKER (verified 2026-06-16): NOT a wire-up.** `35.semantics/lint/primitive_api.spl` `check_module_items([Node])` / `check_function(FunctionDef)` operate on a typed-Node AST; the query/build lint pipeline only builds the arena AST (`module_get_decls() -> [i64]`, consumed by `check_argument_count([i64])` et al.). No `i64`→`Node` adapter exists. Choose: (a) rewrite the primitive check against the arena `[i64]` AST like `argument_count`, or (b) build an arena→typed-Node bridge. | L–XL | Two incompatible AST representations; pick rewrite-vs-bridge first |
| 3 | Extend to **internal** bare-primitive usage (new code, default `warn` even in reliable), reusing `primitive_classification.spl` categories | L | Distinguishing internal vs public usage needs visibility/scope info the text path lacks — likely AST-backed |
| 4 | Real autofix-after-verify: replace the no-op `EasyFix` with a wrapper-introducing rewrite driven by `DomainWrapperCatalog`; keep `FixConfidence.Uncertain` and require an explicit `--apply-verified` confirm before `FixApplicator.apply_to_disk` writes. **Decouple "apply Uncertain" from "disable all verification"** (today both are `--fix-all`); port `InteractiveFix.prompt_fixes` into the live `lint_entry_run_fix` | L | Text-only wrapper rewrite is fragile — may need AST-backed edit |
| 5 | Emit primitive-use as a Warning-severity **Diagnostic** (not just `EasyFix` data) on the diagnostics channel, linked to its `EasyFix` via a stable code, so the WARNING that R2 mandates actually exists for both CLI and LSP | M | Diagnostics volume — gate behind reliable tier |

**Risk & blockers.** The deny-vs-warn ambiguity must be resolved before R2 is cleanly satisfiable. The high-fidelity AST lint is dead in the live pipeline — making it the reliable check requires standing up a semantics-lint invocation that does not exist.

**R2 arena-rewrite recipe (de-risked 2026-06-16 — exact API surface).** Implement option (a)
as a new arena lint mirroring `35.semantics/lint/argument_count.spl`:
- Inputs from `compiler.core.ast`: iterate `module_get_decls() -> [i64]`; `decl_tag[idx]`
  (`== DECL_FN`), `decl_name[idx]`, `decl_get_param_names(idx)`, **`decl_get_param_types(idx) -> [i64]`**,
  **`decl_get_ret_type(idx) -> i64`**.
- Resolve a type i64 to a name with **`type_tag_name(t)`** (`compiler.core.types`); named/custom
  types via `named_type_name`. **OPEN ITEM (confirm first):** whether `decl_get_param_types`
  returns type *tags* (then `type_tag_name` resolves directly) or type-node indices (needs a
  node→tag step). The arena module does NOT load in an isolated `bin/simple run /tmp/...` probe
  (`compiler.core.ast` arena vars fail to resolve), so confirm this **inside** the pipeline.
- Flag a param/ret type whose name ∈ {i8,i16,i32,i64,u8,u16,u32,u64,f32,f64,bool}; reuse the
  pure-math exemption idea (all params + ret the same primitive) and `@allow(primitive_api)`.
- Wire into `query_lint._run_ast_lint_passes` exactly like `check_argument_count`, emit code
  `primitive_api`. **Gate** emission on an active tier (add `_LINT_TIER_ACTIVE`, set in
  `_load_lint_config_for`) so there's zero default noise; severity then governed by the R1-step-3
  override map (moderate→suppress, lib/reliable→deny).
- **Verify** end-to-end via `_collect_lint_diagnostics_json("@lint_profile(reliable)\n\nfn f(x: i64)->i64:\n  x\n")`
  → expect a `primitive_api` diagnostic at severity 1; without the tier → none (gated). The
  isolated arena probe cannot be used (module-load limit above) — verify through this pipeline entry.

---

## R3 — LSP check autofix properly wired (diagnostic → code action → apply edit)

**Current state.** The chain is wired but **broken by a JSON schema mismatch**. `lsp_handle_code_action` (`src/lib/nogc_sync_mut/lsp/lsp_handlers.spl:674`) shells to the CLI `code-actions` subcommand → `query_code_actions` (`src/app/cli/query_navigation.spl:87`), which **does** build real edits but emits the standard nested `edit.changes.<file>[{range,newText}]` shape. The LSP response builder `_parse_code_action` (`lsp_handlers.spl:698`) only reconstructs from **flat keys** `editLine/editCol/editEndLine/editEndCol/newText` — **emitted by nothing** (grep: those keys appear only in `lsp_handlers.spl`). Result: the action carries **no edit** and applies nothing. Separately, `query_api.spl code_actions()` (line 480) always returns `edits:[]` and is **dead** relative to the live LSP server. The fix source is `compiler.tools.fix.collect_fixes_from_source`, **unlinked** to the `Lint.easy_fix` field.

**Gap.** CodeAction→TextEdit hop is broken; two fix generators (`tools.fix` EasyFix vs lint `easy_fix`) are not unified; there is **no end-to-end LSP code-action spec** — which is why the mismatch shipped.

**Steps.**

| # | Step | Effort | Risk |
|---|---|---|---|
| 1 | Pick one canonical CodeAction→JSON shape and pin it: preferably rewrite `_parse_code_action` to consume the standard `edit.changes`/`documentChanges` the CLI already emits; extract a single shared serializer used by both CLI and LSP | M | Two emitters drift again — mitigate with the shared serializer |
| 2 | Add an end-to-end LSP spec: known fixable lint → `textDocument/codeAction` → assert non-empty workspace edit with correct range + newText (the missing regression guard) | S | Needs LSP harness — reuse existing lsp spec scaffolding |
| 3 | Unify the autofix source so code actions derive from lint results (`Lint.easy_fix`), not the separate `tools.fix` generator; dedup overlapping fixes | M | Two generators may conflict — need dedup |
| 4 | Make `query_api.spl code_actions()` either populate real edits or be removed/redirected, leaving one source of truth | S | Low — confirm no caller depends on empty-edit behavior |

**Risk & blockers.** "R3 properly wired" is **unverifiable** until step 1 (schema) and step 2 (harness) both land.

---

## R4 — Formal-verification COVERAGE meta-check

**This is a proof-COVERAGE meta-check** — *does each feature-level public class and each main-class-of-file HAVE a discharged proof obligation* — **not** push-button proving of user code. That distinction is load-bearing and the doc must not blur it.

**Current state.** Two disjoint Lean systems exist; only one is real. (1) **Stub/dead:** the pure-Simple `LeanBackend` (`src/compiler/70.backend/backend/lean_backend.spl` + `lean_mir_translate.spl`) — `write_to_file` returns `Ok(())` **without writing**, `export_module` returns `proof_obligations: []`, `translate_mir_body` falls back to `"sorry"`. Unwired to any CLI flag. (2) **Real:** the Rust driver `gen_lean.rs` + `verify.rs` (`simple gen-lean {generate,compare,write,verify}`, `simple verify {status,check,…}`). `write/generate` runs **15 hand-curated `verification/regenerate/*.spl` modules through the INTERPRETER** (`RunningType::Interpreter`) to emit fixed `.lean` files; `verify` shells to `lean` and fails on any `sorry`/`axiom`/unproven goal. What's actually proven: **hand-authored theorems about the compiler's own algorithms** (`pattern_exhaustiveness.lean`, `module_resolution.lean`, `visibility.lean` — 0 `sorry`) + ~20 generated projects under `src/verification/`. **None verify arbitrary user classes.** The inventory is a **hardcoded Rust list** (`supported_regeneration_modules` in `gen_lean.rs`).

**Gap.** No per-class/per-file proof metadata of any kind (no `@proven`/contract attrs, no symbol→theorem mapping). No notion of "feature-level public class" or "main-class-of-file" in the compiler — it cannot enumerate the units that would need a proof. `check_completeness` is a regeneration-**drift** check, not a coverage check. The `lean` binary is optional (`cmd_status` reports "Not found" gracefully).

**Steps (coverage ledger FIRST — never full proofs first).**

| # | Step | Effort | Risk |
|---|---|---|---|
| 1 | **Coverage LEDGER** (minimal honest start): a declarative `doc/08_tracking/verification/proof_ledger.sdn` mapping each public/feature-level class & main-class-of-file → `{lean_project, theorem(s), status}`. **Seed from the existing hardcoded `supported_regeneration_modules` list** so it is real and non-empty day one; have `gen_lean.rs` read it instead of the hardcoded list | M | Low (additive) — one-time class-vs-file granularity convention decision |
| 2 | Source annotation so the compiler can KNOW a unit claims a proof: `@proven(project:"…", theorem:"…")` on classes/fns, parsed + surfaced in symbol metadata, **inert to codegen (lint-only)** so the seed is unaffected | L | New attribute kind — must not break seed |
| 3 | "feature-level public class / main-of-file" classifier (the enumerator R4 needs; does not exist today) | M | Reliable public/main classification is non-trivial |
| 4 | **Coverage meta-check as a LINT pass** (not a prover): enumerate units via step 3, look up each in ledger/annotation, emit a WARNING (reliable tier) when a unit lacks a discharged proof. New `verify coverage` subcommand alongside `cmd_check`. Achievable **without** touching M12-blocked codegen | M | Depends on step 3 classifier |
| 5 | Wire "DISCHARGED" truth: reuse the working `LeanRunner`/`gen-lean verify` result (success ∧ goals==0 ∧ no sorry/axiom) → ledger status, so coverage reflects actual `lean` outcomes. reliable gate = annotation present ∧ referenced theorem checks clean | M | Depends on `lean` installed — define warn-vs-fail policy when `LEAN_BIN` missing |
| 6 | **Explicitly DO NOT** auto-translate user classes to Lean this phase. Document that reliable formal verification = COVERAGE of human-written proofs, because the `LeanBackend` MIR translator is a stub and the only Simple→Lean bridge is interpreter-only (M12 ceiling) | S | Low — scope/doc; prevents over-promising |

**Risk & blockers (stated plainly).** The **M12 ceiling is real and hard**: the only working Simple→Lean path runs `.spl` regen modules through the *interpreter*; `run/jit/aot/native` use the Rust frontend and never emit Lean — so a trustworthy auto-generated proof of compiled user code is **not feasible in the planning horizon**. The pure-Simple `LeanBackend` is **vapor** (no-op write, empty obligations, `sorry` fallback) — must not be a basis for R4. `lean` is an **optional external toolchain** — the reliable gate must degrade gracefully or block CI by explicit policy. No public/main-class classifier exists yet. R4 is therefore a multi-step coverage program, **not** one bullet.

---

## Phased Rollout

**P0 — Config + profile selector (foundation).** R1 steps 1–2 (profile field, fill `map_lint_code_to_config_name`); glossary + comparison-doc supersession notes; ladder/assumption documented. *Outcome:* the axis exists and is configurable on the CLI path. *Gate:* no behavior change beyond `moderate` default.

**P1 — Primitive WARNING + autofix-after-verify + LSP wiring.** R1 step 3 (two-engine reconciliation — prerequisite that makes profiles meaningful in LSP/build); R2 steps 1–2,4–5 (reconcile severity, AST lint, verified autofix, Warning diagnostic); R3 steps 1–4 (schema fix, spec, unify fix source). *Outcome:* `lib`/`reliable` rung 1+2 usable in editor and CLI.

**P2 — Link-time lint.** R1 steps 4–6 (compile phase, SymbolGraph/SymResolution wiring, link-time lint pass). R1 step 7 (SMF signature channel, XL) and R2 step 3 (internal-primitive AST) ride here or slip to P2.5. *Outcome:* R1 "compile AND link" satisfied at module + whole-program scope.

**P3 — Formal-verification coverage.** R4 steps 1→6 in order (ledger → annotation → classifier → coverage lint → discharged-status wiring → scope doc). *Outcome:* `reliable` rung 3 gate (coverage, not auto-proof).

Ordering rationale: R1 step 3 (engine unification) and the unmapped-code fill block everything downstream; the heavy/risky work (link SMF, Lean coverage) is deliberately last.

---

## Open questions

- Proof-coverage **unit granularity**: per public class vs per file (main-class-of-file) — the ledger needs one convention.
- Policy when **`LEAN_BIN` is absent** under `reliable`: warn-and-pass vs hard-fail CI.
- **Tier auto-selection** for mixed app/lib trees: manifest-driven, directory-driven, or explicit-only (default `moderate`).
- **Ordering** of the two-engine unification (CLI `LintConfig` vs LSP `35.semantics` direct calls) relative to the profile selector — profiles are inert in the editor until this lands.
- Whether `lib` tier turns the internal-primitive check on as `warn` by default or leaves it opt-in.
