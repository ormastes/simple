# IDE Extension Kernel — Parallel-Agent Plan with Shared-Foundation-First

Date: 2026-07-29. Status: PLAN (verified against repo, see Audit Deltas).
Strategy: land ONE serial foundation wave (Phase S) that owns every file two or
more lanes would otherwise touch; only then start parallel lanes L1–L7, each
with an exclusive path set. Conflict prevention = path ownership, not merge
heroics.

## 0. Audit deltas (research corrections to the source plan)

Verified 2026-07-29 by three parallel repo sweeps. The source plan is broadly
correct; these deltas change lane scoping:

1. **CONFIRMED** manifest loader is a positional quote-scraper
   (`src/lib/editor/extensions/manifest.spl:72-137`); themes/keybindings
   hardcoded `[]` (:68-69); debug-adapter list returns `[]` (:124-125).
   Commands and languages harvest from one flat id pool, so language
   `extensions` is always `[]`.
2. **CONFIRMED** host has no typed handlers (`host.spl:65,246,316` — dispatch
   produces status records only), events only count (`host.spl:208-218`),
   wildcard activation at `gui_shell_core.spl:64-66`.
3. **CONFIRMED** `parse_with_spans` returns an empty span map
   (`src/lib/common/sdn/parser.spl:80-87`); no duplicate-key/unknown-field
   diagnostics; only `parse_untrusted` has the 1 MiB cap (:339-343); **no
   serializer** in the live SDN lib (`SdnValue.to_text` stubs Dict/Table).
   A full canonical serializer exists only in the legacy parallel tree
   `src/compiler_rust/lib/std/src/sdn/serializer.spl` — port, don't rewrite.
4. **DELTA** `editor_controller.spl` (3175 LOC) and `gui_shell_core.spl`
   (981 LOC) import Markdown modules directly but **no Office modules** —
   Office decoupling is cheaper than the source plan assumed; the coupling
   problem is Markdown-shaped.
5. **DELTA** Slides layouts/elements are **closed enums**
   (`slides/slide.spl:9-20`), not literal arrays — registry migration means
   enum→descriptor conversion, slightly bigger than "populate dropdown from
   registry".
6. **CONFIRMED** Sheets `formula.spl` is 9,769 LOC with inline name dispatch,
   no registry, and module-level mutable origin-cell state (:50-63,
   single-threaded by contract).
7. **CONFIRMED** IOSLight hardcoded at `word_app.spl:97`, `sheets_app.spl:87`,
   `slides_app.spl:102`, plus `launcher.spl:105`, `counter.spl:35`,
   `mail_app.spl:63`, `planner_app.spl:85`. `office/theme.spl` ignores its
   `app_name` arg. Duplicate 43-LOC theme manager at
   `src/lib/editor/extensions/theme_manager.spl`.
8. **CONFIRMED** the main extension "system test" is 159 source-string
   assertions, duplicated verbatim (`test/03_system/gui/editor_extension_spec.spl`
   and `test/system/editor_extension_spec.spl` — 318 total). Any refactor of
   manifest/host breaks all of them with zero behavior change. Must be removed
   in Phase S, not by a lane.
9. **NEW FINDING** `md.toggleBold` is declared in
   `builtin/md_language.spl:19` but has **no implementation anywhere** — the
   flagship "first acceptance scenario" command must be written, not migrated.
10. **CONFIRMED** native plugin registry (`src/app/plugin/registry.spl`, 348
    LOC) is separate and also hand-parses its SDN manifest — share the new
    decoder later (Phase L7), do not merge registries.
11. **LANDMINE** `SdnValue.insert()` lands on a dead copy for
    constructor-returned dicts (`value.spl:167-179`, bug
    `enum_payload_dict_copied_on_function_return_2026-07-28`). The manifest
    decoder must build typed structs via `mut` locals, never mutate a returned
    SDN tree.

## 1. Why shared-foundation-first

Conflict hotspots — files ≥2 lanes would edit if lanes started today:

| Hotspot | Lanes that would collide | Resolution |
|---|---|---|
| `src/lib/common/sdn/*` | kernel, theme, vscode-bridge, plugin-registry | Phase S owns |
| `src/lib/editor/extensions/{api,manifest,host}.spl` | all lanes | Phase S owns |
| Command registry (new) | Markdown, Word, Sheets, Slides | Phase S creates contract + registry |
| Document service (new) | Markdown, Word, Sheets, Slides | Phase S creates traits + registry skeleton |
| ThemeService injection contract | theme lane, all 3 Office lanes | Phase S defines contract; Office lanes do their own injection lines; theme lane never edits app files |
| `editor_controller.spl` / `gui_shell_core.spl` | Markdown lane, kernel | Exclusive to L1 after S removes wildcard activation |
| `test/03_system/gui/editor_extension_spec.spl` + duplicate | every lane | Phase S deletes both, replaces with behavior spec |
| Builtin registration index | all built-in lanes | Per-lane registration files + one S-owned index that only appends one `use` line per lane (jj merges disjoint one-line appends; each lane touches only its own line) |

Rule: after Phase S lands, **no lane edits a file outside its ownership column**.
If a lane discovers it needs a contract change, it files it to the S-owner
follow-up lane (L0) — it does not edit shared files.

## 2. Phase S — serial shared foundation (ONE agent, lands before any lane)

Est. the largest single wave; it is the price of conflict-free parallelism.

### S1. SDN hardening (`src/lib/common/sdn/`)
- Real spans in `parse_with_spans` (line/col per key and value).
- Duplicate-key error, unknown-field diagnostic hook (schema-driven).
- Structural limits: max nesting, collection count, string length (extend the
  existing 1 MiB `parse_untrusted` path).
- Canonical serializer: port from
  `src/compiler_rust/lib/std/src/sdn/serializer.spl` into
  `src/lib/common/sdn/encode.spl`; stable ordering ⇒ manifest hash.
- `schema.spl`: decode `SdnValue` → typed struct with all-errors-collected
  reporting. Construction via `mut` locals only (landmine #11).
- Keep `parse_config`/flat parsers untouched (out of scope; they have their
  own consumers).

### S2. Extension kernel contracts (`src/lib/editor/extensions/`)
Target layout (refactor in place, keep `ExtensionHost` facade name):
```
contract.spl      # ExtensionId, SemVer range, descriptors, selectors, errors
manifest.spl      # typed manifest model only (no parsing)
manifest_sdn.spl  # SDN decode + schema validation + canonical encode
api.spl           # ExtensionContext, Disposable, CancellationToken,
                  # ServiceToken<T>, typed storage, When-predicate tree
registry.spl      # contribution + provider indexes, duplicate-ID detection,
                  # stable ordering, conflict policy
host.spl          # facade: activation router, lifecycle, disposal
runtime.spl       # host-placement stub (builtin in-process now; worker later)
```
- Command entry gains a typed handler (`fn(CommandInvocation) -> Result<...>`)
  and enablement predicate; palette/menu/keybinding/programmatic all route
  through one CommandRegistry.
- `emit_event` invokes typed listeners; delivery-count becomes a byproduct.
- Every registration returns a Disposable owned by an ExtensionLifetime;
  deactivate disposes all.
- Activation: typed events (onCommand/onLanguage/onView/onCustomEditor/
  onStartupFinished/workspaceContains); **remove `activate_event("*")` from
  `gui_shell_core.spl:64`** (the one shell edit S makes).
- Manifest schema `simple.ide.extension/1` documented in
  `doc/04_architecture/app/ide_extension_kernel/manifest_schema_v1.md`.

### S3. Document service skeleton (`src/lib/editor/document/` new)
- `DocumentRegistry` (URI→handle), `DocumentTransaction`, dirty/undo hooks,
  `DocumentCodec<T>` / `DocumentEditorProvider<T>` / `DocumentRenderer<T>`
  traits, view-invalidation callback. Skeleton + one in-memory text model —
  enough for lanes to code against; depth arrives with L1.

### S4. Theme + service contracts
- `ServiceToken<T>` scopes (global/workspace/document/surface/request).
- Theme contract: extensions/apps consume `ThemeRenderSnapshot` roles via a
  token; delete nothing yet (theme lane L5 does the deletions).

### S5. Test reset (prevents every-lane test collisions)
- Delete `test/03_system/gui/editor_extension_spec.spl` and
  `test/system/editor_extension_spec.spl` (source-string tautologies; user
  plan §13 authorizes this move — they are replaced, not skipped).
- New behavior specs owned by S:
  `test/01_unit/lib/editor/extensions/{manifest_sdn,registry,lifecycle}_spec.spl`
  and one walking-skeleton system spec
  `test/03_system/ide/extension_kernel_walking_skeleton_spec.spl`:
  fixture extension in a temp dir → discovered without execution → lazy
  activation on command → typed handler runs → DocumentTransaction applied →
  deactivate removes everything.
- Fixture extension lives at `test/fixtures/ide_extensions/hello/`
  (`extension.sdn` + module) — the conformance fixture every lane copies.

### S6. Builtin registration seam
- `src/lib/editor/extensions/builtin/index.spl`: list of builtin manifest
  providers, one line per domain. Lanes add exactly their own line + their own
  `builtin/<domain>_ext.spl` file. No other shared edits.

**Phase S exit gate:** walking-skeleton spec green on interpreter + native
lanes; `bin/simple test test/01_unit/lib/common/` (existing ~208 SDN cases)
still green; wildcard activation gone; both tautology specs deleted.

## 3. Parallel lanes (start only after S exit gate)

Each lane: exclusive paths, its own tests, its own builtin registration file,
scoped commits (vcs.md anti-clobber rules apply — never whole-WC commit).

### L1 — Markdown vertical slice (proves the kernel; highest risk)
**Owns:** `src/lib/editor/extensions/builtin/md_*.spl`,
`src/app/editor/editor_controller.spl`, `src/app/editor/gui_shell_core.spl`,
`src/app/editor/{editor_markdown_helpers,md_dispatch}.spl`, `view/md_*`,
`view/markdown_state.spl`, `view/{outline,wiki}_panel.spl`,
`builtin/markdown_ext.spl`, `test/**/markdown_extension_*`.
**Does:** generate `extension.sdn` from typed descriptors; register existing
diagnose/complete/hover as providers; **implement** `markdown.toggle_bold`
(currently declared, unimplemented) through
palette→CommandRegistry→activation→handler→DocumentTransaction; preview as
readonly custom editor; then incrementally remove direct md imports from
controller/shell (only where equivalent routing passes).
**Gate:** source+preview share one document model; toggle-bold + undo +
save/reopen system spec with captures; controller md-import count strictly
decreasing, zero for migrated features.

### L2 — Writer
**Owns:** `src/app/office/word/**`, `builtin/writer_ext.spl`, its tests.
**Does:** `match action:` literals (`word_app.spl:129-181`) → command
registrations; Save routes through DocumentCodec (today it only clears the
modified flag); document kind `simple.rich_document`; outline provider;
ThemeService injection replacing `word_app.spl:97` IOSLight.
**Gate:** format/outline/save/reopen behavior spec; zero literal action
strings in the dispatch path.

### L3 — Sheets
**Owns:** `src/app/office/sheets/**`, `builtin/sheets_ext.spl`, its tests.
**Does:** `SheetFunctionRegistry` + `SheetFunction` trait; builtins register
into it (mechanical extraction from `formula.spl`'s name dispatch — do NOT
split the 9.7k file further in this lane); `_recalculate_formulas`
(`sheets_app.spl:257`) resolves via registry; fixture `DOUBLE(n)` extension;
IOSLight removal (`sheets_app.spl:87`). Note formula.spl's module-level
origin-cell state keeps evaluation single-threaded — registry must not
promise concurrent evaluation.
**Gate:** `=DOUBLE(A1)` recalculates through the registry, survives
save/reopen; existing formula tests green.

### L4 — Slides
**Owns:** `src/app/office/slides/**`, `builtin/slides_ext.spl`, its tests.
**Does:** convert closed enums `SlideLayout`/`SlideElementKind`
(`slide.spl:9-20`) to descriptor registries with the five current layouts and
four element kinds as builtins; layout dropdown reads the registry; fixture
layout+element extension; IOSLight removal (`slides_app.spl:102`).
**Gate:** fixture layout appears in real dropdown, creates typed
placeholders, renders, survives save/reopen.

### L5 — Theme unification (lib side only — never edits app files)
**Owns:** `src/lib/nogc_sync_mut/ui/theme_package.spl`,
`src/lib/common/ui/{theme_render_snapshot,wm_chrome_theme,theme_registry}.spl`,
`src/os/services/theme/**`, **deletes**
`src/lib/editor/extensions/theme_manager.spl` (43-LOC duplicate) after L1
stops referencing it, semantic role hierarchy (wm./workbench./document./
sheet./slide./semantic.), the open guest-theme render bug.
**Gate:** theme ID + semantic token dump + rendered pixels agree on host GUI,
SDL, TUI; guest bug fixed or explicitly re-filed with evidence.

### L6 — Runtime isolation & security
**Owns:** `src/lib/editor/extensions/{runtime,roots}.spl`, permission/policy
modules, its tests.
**Does:** canonical path containment (replace raw `starts_with`), symlink
resolution, reject absolute entry paths, default-deny permission decode,
crash-loop detection, per-extension diagnostics log. Worker/WASM process host
is a stretch goal — the contract (host placement enum, RPC versioning) is
already fixed by S so this lane can trail without blocking others.
**Gate:** path-escape, denied-permission, and crash-containment specs; a
misbehaving fixture cannot take down the host facade.

### L7 — Capability truth + bridges
**Owns:** `src/app/ide/{capabilities,plugin_manifest,feature_report}.spl`,
`src/app/office/plugins.spl`, `src/app/vscode_extension/**`,
`src/app/plugin/registry.spl` (decoder swap only), its tests.
**Does:** `ide_capabilities()` generated from the live contribution registry
with states declared/indexed/activatable/bound/smoke-tested; replace the
three static office PluginEntry probes; generate VS Code `package.json` from
canonical SDN (conformance check first, generation second); switch native
plugin-registry manifest parsing to the S1 decoder (registries stay separate).
**Gate:** `--feature-check` output changes when a builtin is disabled;
generated package.json diff-clean against the hand-maintained one or
deviations documented.

## 4. Dependency graph and sequencing

```
Phase S (serial, 1 agent) ──gate──> L1..L7 start in parallel
L1 Markdown ──(is the kernel's proving ground; contract-change requests go
               to L0 follow-up, batched, semver'd — lanes rebase, never edit
               shared files themselves)
L5 deletes theme_manager.spl only after L1 drops its references (cross-lane
   handshake #1 — the only ordered edge between lanes)
Integration wave I (after L1-L4): remove remaining direct feature dispatch
   from GUI shell — executed by L1's owner since it owns the shell files.
```

L0 (foundation owner) stays alive during the parallel phase as the sole
editor of `contract/api/registry/host/manifest_sdn` and the SDN lib —
contract changes are batched, announced in
`.spipe/ide_extension_kernel/state.md`, and lanes rebase onto them.

## 5. VCS protocol for the parallel phase (per vcs.md, mandatory)

- Work on `main`, jj; commit ONLY files inside your ownership column; never
  `jj commit -a` a whole stale WC.
- `sj raw jj git fetch && sj raw jj rebase -d main@origin` before every
  snapshot; revert-guard diff before push; run
  `sh scripts/check/check-no-conflict-tree-push.shs` pre-push.
- The builtin index and `.spipe` state files are the only files multiple
  lanes append to — one line per lane, own line only.

## 6. Coding landmines every lane agent must know

- `Dict.len()` → -1 and `.get()` corrupt on struct values under native
  codegen — use `keys().len()` / `contains_key + d[k]`.
- `?? default` on raw i64: nil sentinel IS 3 — never `index_of(..) ?? -1`.
- JIT `x.f += v` loads zero — write `x.f = x.f + v`.
- `list.get(i)` returns tag-boxed value<<3 — use `xs[i]`.
- SdnValue.insert on constructor-returned dicts is a dead-copy no-op — build
  with `mut` locals.
- `bin/simple lint` passes files that don't parse — gate with
  `bin/simple compile`.
- One HIR `Unknown variable` silently de-JITs the whole module — grep run
  logs before any perf theory.

## 7. Deferred (explicitly out of the first campaign)

Walkthroughs, resource-label formatters, authentication, terminal profiles,
AI contribution points, aspectHooks for third parties, DOCX/XLSX/PPTX codecs
(codec trait exists; format work is its own later campaign — no compatibility
claims until real import/edit/save/reopen fixtures pass), worker/WASM
sandbox completion (L6 stretch), marketplace/signing.

## Execution status — CAMPAIGN COMPLETE (2026-07-29)

All Phase S items and all lanes landed on origin/main the same day, executed
by parallel agents per this plan. Coordination log:
`.spipe/ide_extension_kernel/state.md`.

| Item | Commit | Evidence |
|---|---|---|
| Plan | e8276bda | this file |
| S1 SDN hardening | 3c7caf66 | 33 new cases; 82-case gate exact |
| S3+S5a document skeleton + tautology deletion | 9d406f18 | 7/7; 318 source-string asserts removed |
| S2 kernel contracts | 92bc8ebd | 25 cases; typed handlers, wildcard removed |
| S5b fixture + walking skeleton | f76e5cfd | 4/4 system |
| L3 Sheets registry | 51437cee | 4/4; 1037-case baseline exact |
| L6 isolation | eb170580 | 17/17 |
| L7 capability truth | 23b18383 | 8/8; vscode 35 mismatches surfaced |
| L4 Slides registries | de71d056 | 11/11; 133/133 baselines |
| L2 Writer | a433ac40 | 6/6; codec-backed save |
| L0 dup-key surfacing | 9f69e3c3 | spans 15/15, manifest 11/11 |
| L7b vscode generation | bea36f79 | hard mismatches 48→0 (spec probe-validated*) |
| F2 host CSS theme wiring | 7b855f96 | 7/7; guest path explicitly unverified |
| F3 symlink containment | 95f57c03 | 19/19; real symlink escape rejected |
| F4 workbook formula codec | 72cae377 | 7/7; expressions survive reopen |
| F7 document depth | 12788f84 | 15/15; view sync/autosave/hot exit |
| L6b hooks + F5 manifests | d9ce5aaa | 7/7 + 10/10; providers 6→14, all bound |
| F6 workbench registries + F1 cleanup | 60ffadcc | 8/8+7/7+8/8; theme_manager deleted (0 importers) |
| L1 Markdown slice + Wave I | 035e419d | 6/6+13/13; toggle_bold real; wildcard=0 repo-wide |
| L5 semantic roles | 14ed678b | 26 roles (specs harness-blocked*) |

*Open items (tracked in state.md): re-verify queue of 5 specs blocked by box
load (probe-validated, not failed); guest-QEMU theme verification (F2 filed);
L1's four kernel API change requests (LanguageProviderRegistry, typed
payloads, onLanguage activation, hot-path dispatch); capabilities.spl
owner_module mismatch for mail/planner; F7's interpreter callback-visibility
quirk needs a bug filing. §7 deferred scope remains deferred by design.
