# Cache effectiveness audit — build caches (2026-08-23)

Tree: `origin/main` @ `e1f31f31da9`, worktree `/mnt/fast/wt-cache-1`.

## Measurement honesty statement

**No build was run and no hit rate was measured.** The lane's own constraint is
"check `free -g` and wait if free memory <20 GB"; the box held 3 GB free / 16 GB
available at 01:32 with load 46 and ~40 build workers from other lanes. No
existing log on this host carries `[frontend-cache]` / `[hir-cache]` /
`[hir-shard]` receipts (checked every `build/bootstrap/*.log` under
`/mnt/data/worktrees/*` newer than 3 days: zero matches), and the only populated
caches on the box are gate fixtures of 1-2 entries each
(`goal-main-1/build/bootstrap/native_cache/{default,gate14..17}`), which cannot
support a hit-rate claim. Everything below is **static analysis of the key
functions plus the numbers already recorded in the two cited bug records**.
Every quantitative claim is labelled with its source.

## Layer 1 — frontend parse cache (`.fpc`)

`src/compiler/10.frontend/frontend_parse_cache.spl` (162 lines).

- **Key:** `sha256(file content)` alone (`frontend_parse_cache_key`, l.89-95).
  The producer identity does **not** enter the filename — it rides in the entry
  header (`FRONTEND_CACHE_ENTRY_VERSION + FLAT_POOL_CODEC_VERSION + scope`,
  l.100) and in the directory (`native_cache/<scope>/frontend/`). A scope
  mismatch is therefore a header-check MISS, never a silent wrong hit. Correct.
- **Off by default when unscoped:** no `SIMPLE_FRONTEND_CACHE_SCOPE` published
  ⇒ cache disabled (l.62-73). Fail-safe, but it means any process the
  orchestrator does not scope gets 0% by construction.
- **Fixed today** at `a6233953eca` /
  `doc/08_tracking/bug/hir_shard_children_reparse_closure_2026-08-22.md`:
  `native_build_compiler_executable_hash()` hashed `args[0]`, which under
  `simple run <script>` is the *entrypoint script*, so parse-shard children
  (`parse_shard_main.spl`) and HIR-shard children (`native_build_worker.spl`)
  wrote **two disjoint scopes**. Recorded effect: every HIR child missed all 687
  entries and re-parsed the closure (>54 min per child); post-fix the fixture
  reports `hits=3 misses=0 parses=0` in all three processes.
- **Residual waste (not fixed):** the key is the *whole file content* hash, so
  a comment-only edit invalidates that module's parse. That is correct and
  unavoidable for a parse cache.
- **Hit rate: not measured.** Expected ~100% on a warm identical tree given the
  fix; the fixture-scale evidence in the bug record is 3/3.

## Layer 2 — HIR cache and shards

`src/compiler/80.driver/driver_hir_cache.spl` (371 lines).

- **Key** (l.102-109):
  `sha256(sha256(source) | closure_digest | is_entry | env switches | codec header)`.
- **`closure_digest` folds EVERY frozen surface** (l.84-92), using each
  surface's `content_hash` + `content_length` + names. The header comment
  states the trade-off explicitly and defends it: lowering builds a decl-owner
  index over the whole closure and re-export materialization walks non-imported
  package siblings, so a per-import key could serve a stale module.
- **Consequence — the single largest effectiveness gap in the system:** because
  the fold uses the *content* hash of every module, **one comment or function-body
  edit anywhere in the 687-module closure invalidates all 687 HIR entries.** The
  cache pays only for repeated builds over a byte-identical tree. For the actual
  developer loop (edit one file, rebuild) the HIR hit rate is **0% by
  construction**, and HIR is the ~60 min phase.
- Restore cost was cut 4-5x at `4dc2bbfea4a`, encode 170x at `13bf3b2beee`
  (both cited by the task; not re-measured here).
- **Shards** (l.205-360): claim order is a real Kahn topological levelling; the
  claim queue is `flock`'d with a static path-hash fallback, and a malformed
  spec owns everything (fail-closed). No correctness objection found.
- **Recomputed per shard child, needlessly:** each of the N children rebuilds
  the source closure and freezes surfaces itself. That costs ~16-26 s of freeze
  **plus a restore of every one of the 687 `.fpc` entries at ~0.5-1 s each**
  (numbers from the bug record's run10 observations), i.e. ~6-12 min per child
  before it lowers anything, for N×687 restores where 687 would do. The driver
  never persists frozen surfaces.

## Layer 3 — object / native cache, and the SMF manifest

- `native_build_cache_scope_key` (`driver_build/incremental.spl:341`) folds
  backend, CPU, features, opt level and compiler identity, and the lane
  (`SIMPLE_CACHE_SCOPE`) partitions by directory. Sound.
- **`.claude/rules/commands.md` is now STALE on one point and still right on the
  other.** `interface_digest_of` is no longer callerless: `interface_digest_of_source`
  is live in `cache/action_key.spl`, `watcher/smf_manifest.spl`, and
  `driver_build/incremental.spl` (`incremental_dependency_interface_fold`,
  l.432-444, with `dep_iface_gate_record` / `dep_iface_gate_valid` at l.958-968).
  A body-only edit leaves the fold unchanged; a signature edit changes it —
  exactly the primitive a dependency-aware rebuild needs, and it is written and
  documented.
- **But it is wired to nothing.** `grep` over `src/**` for
  `dep_iface_gate_record|dep_iface_gate_valid` outside its own file returns
  **zero** call sites; `DependencyEntry.needs_recompile` still has zero
  external callers; `smf_manifest_entry_verifies` is still exported from
  `watcher/__init__.spl:34` with zero callers; no build path traverses
  `simple.sdn`'s `dependencies:`. **There is still no dependency-aware or
  partial rebuild.**
- Cheapest real win here: *not* a full target/dependency model. It is to feed
  the already-shipped `interface_digest_of_source` into the HIR closure digest
  (item 1 below), which turns the same primitive into a hit-rate win without
  needing a build graph at all.

## Ranked fixes

| # | Fix | Est. saving | Risk | Notes |
|---|---|---|---|---|
| 1 | **Key `hir_cache_closure_digest` on each surface's `interface_digest_of_source`, not its file `content_hash`.** A body/comment edit then leaves every other module's HIR key unchanged. | Turns HIR hit rate on an incremental (1-file) build from 0% to ~(n-1)/n. On the ~60 min HIR phase that is the difference between a full re-lower and one module. | **MEDIUM** — must first prove `source_interface_parts` covers everything a frozen surface exposes (extend decls, re-export aliases, impl blocks, trait default methods). A gap = a stale hit, i.e. a wrong build. Needs a differential spec: mutate each surface-visible construct, assert the digest moves. | Reuses shipped, tested machinery. Highest value in the table. |
| 2 | **Persist frozen surfaces; shard children restore instead of rebuilding.** | ~6-12 min per shard child of serialized pre-lowering time (N×687 → 687 `.fpc` restores), from the run10 numbers. | **MEDIUM, larger than it looks** — *not* the "low-risk obvious candidate" it was scoped as. `ModuleSurface` transitively carries `Type`, `ParserTypeParam`, `ParserFunction` (trait `default_methods`), `Variant`, `AssocTypeDecl`, `TraitBound`, `Dict<text, ModuleSurfaceCallable>` (`module_surface_types.spl`, 471 lines). Persisting it means a **new codec over a large slice of the AST**, comparable in size and divergence risk to `hir_codec`. It needs a design note and a roundtrip gate (`check-hir-codec-roundtrip.shs` is the precedent), not an inline edit. | Deliberately **not implemented in this pass** — see below. |
| 3 | **Make the frontend cache scope's absence loud.** Today an unscoped process silently runs at 0% hit rate; that is precisely the failure mode that hid the `a6233953eca` bug for a full run. Emit the `[frontend-cache]` receipt with `scope=<none>` even when disabled. | 0 directly; buys detection of the next scope split. | **LOW** | Small, safe, and the cheapest thing in this table. |
| 4 | Wire `smf_manifest_entry_verifies` / `dep_iface_gate_valid` into a real rebuild decision. | Unknown; potentially the whole partial-rebuild win. | **HIGH** — needs the target/dependency model that does not exist. | File as a design item, do not attempt piecemeal. |

## Why nothing was implemented in this pass

Item 2 was the pre-assigned candidate and the audit downgraded it: it requires a
new AST-carrying codec, so it is a design change, not a minimal
semantics-preserving edit. Item 1 is the higher-value fix but is a
*correctness-critical* key change — landing it without the ability to run a
build or the differential digest spec would risk stale HIR hits, i.e. silently
wrong binaries. With 3 GB free memory and the lane's own no-build rule in force,
neither could be validated. Both are recorded here rather than landed blind.
