# Stage 3 `phase3:hir:imports` memory explosion on `driver_riscv_gen2_product.spl` (2026-08-23)

**Status:** OPEN. Stage 3 has never completed on this host today.

## What was measured

Stage 2 is green and admitted (`Build complete: 749 compiled, 0 cached, 0 failed`,
`stage2-sanity: pass`, `stage2-provenance: pure-simple`, `status=admitted`, binary
sha matching `candidate_sha256` in `admission.env`). Stage 3 then enters
`phase3:hir:imports` and does not come out.

At module **8 of 691** — `src/compiler/driver/driver_riscv_gen2_product.spl`,
480 lines — after roughly 35 minutes:

- footprint **62 GB**, process state `stuck`
- swap **14.35 GB of 15.36 GB** used, on a 24 GB box
- `hir:file:start` lines DUPLICATED in the progress stream for the same file
- `build/bootstrap/bootstrap-build-progress.events` last advanced at 18:05:48
  with `phase=hir unit_kind=modules done=8 total=691 failed=0 cached=0
  elapsed_ms=302639`

The run was SIGTERM'd to save the machine. **`STAGE3_RC=143` is that kill, not
the failure mode** — do not read 143 as a crash signature.

Duplicated `hir:file:start` for one file, with unbounded growth, is the shape of
repeated/re-entrant import work rather than one large allocation.

## Related, and why this is filed separately

`origin/main` carries `docs(perf): measure compiler peak RSS — native-build
worker within 953 MB of the earlyoom kill`. That measurement says the worker
already runs close to the kill threshold; this record is the case where it goes
**62x** past it, so the two should not be conflated.

Also landed at origin and NOT yet exercised against this failure:
`e52f3e4de26` "fix(hir): bare-lift HirSymbol.type_ — heap Some box segfaulted
HIR-cache encode". That fix is in the same subsystem and may explain, mask, or
interact with this explosion. **The next attempt must be run on a tree that
includes it before any further root-causing happens here.**

## Unverified hypothesis — recorded, deliberately NOT landed

`module_surface_declaration_authority_lookup`
(`src/compiler/20.hir/hir_lowering/module_surface_types.spl:207`) is the only
lookup in its family with no scalar fallback. After the staged transient
teardown invalidates the compatibility Dict carrier (`len()` reports `-1`),
every frozen declaration-authority lookup silently returns `found: false`. The
hypothesis is that this silent miss drives repeated import work.

A candidate patch adds the same retained-array fallback its sibling
`module_surface_export_origin_index_position` already uses. It was **not
landed**, for two reasons: it is untested against the failure, and its fallback
path is a LINEAR SCAN over `index.names` (946 entries in this build) on every
lookup, so if it were ever taken on a hot path it would be a new O(n) cost of
exactly the class `.claude/rules/code-style.md` warns about. Verify the fallback
is cold — or make it not a scan — before landing it.

The patch is preserved outside the tree at
`.../scratchpad/edits/` for whoever picks this up.

## What IS fixed and landed

The failure immediately before this one, in the same run, was real and is fixed:
`module_surfaces_frozen_alignment_error`
(`src/compiler/20.hir/hir_lowering/module_surface_registry_index.spl:234`)
compared `authority_count` against `index_by_name.len()` unconditionally and so
rejected every natively built compiler's own frozen registry with
`surface declaration-authority arrays invalid: index=0 count=26; surfaces=691
names=946 indices=946 dict=-1`. It now compares only when the carrier reports a
usable count, matching the tolerance two sibling functions in the same subsystem
already had. Verified: stage 3 got past phase-2 retention into HIR lowering.

`Dict.len()` is NOT universally broken — a native probe in a stage2-built binary
returned `len=2` — so the `-1` is genuinely a post-teardown carrier state.

## Reproduce

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap   # to stage 2
# then the stage-3 leg; watch RSS, not the progress monitor
```

Judge stage 2 by receipts and `Build complete:`, never by the progress monitor:
an `alive-no-progress … exit-0 main_log=absent` trace was confirmed this session
to accompany a genuinely admitted stage 2.


---

## RUN 2 (2026-08-23, tree `cde14a397aa`) — the explosion MOVED; it is not gone

Re-measured on a tree carrying origin's `e52f3e4de26` (HIR-cache encode) plus
the frozen-registry change. Phase 2 green: `Build complete: 750 compiled, 0
cached, 0 failed`, `Stage 2 admitted`.

`driver_riscv_gen2_product.spl` no longer explodes — but only because it now
**fails fast with 17 HIR lowering errors** (`[hir-fatal-count] count=17
shown=10`). The runaway relocated to `src/compiler/backend/backend/
interpreter.spl` (529 lines), stalling immediately after
`phase3:hir:declare:done`, i.e. in BODY lowering.

Shape: **31 minutes on one module, zero log output, 93% CPU, RSS monotone and
accelerating — 5.4 GB -> 8.2 GB (~150 MB/min) -> 11.6 GB (~310 MB/min)**,
SIGTERM'd at 11.5 GB. Peak observed earlier in the same run: 12.5 GB. The box
did not swap this time. `STAGE3_RC=143` is the kill, not the failure.

### Correction to RUN 1

The "duplicated `hir:file:start`" flagged in RUN 1 as suspicious is **uniform
across every file** (`uniq -c` == 2 for all). It is normal instrumentation, not
a symptom. Disregard it.

### The causal chain, now evidenced

The 17 errors that appear once the registry is admitted:

```
unresolved type: HirClass / HirEnum / HirConst / HirBitfield / HirAopAdvice
field `hir_modules` is not visible from this module
field `logger` / `sources` is not visible from this module
```

Type resolution and field visibility are exactly what the frozen
declaration-authority lookup answers. ALL of them failing is the signature of
`module_surface_declaration_authority_lookup` returning `found: false` for
everything — which is what a dead `index_by_name` carrier produces, since that
function is the one member of this family with NO scalar fallback.

So: a dead carrier does not degrade the registry, it makes it unusable.

### Consequence for the hypothesis recorded above — CONFIRMED, and REFUTED

- Its **diagnosis** is confirmed: the dead carrier is what drives the failure.
- Its **implementation** is refuted by the same evidence. The fallback would be
  **hot, not cold** — taken on every lookup after teardown, over 946 names — so
  a linear scan is the wrong shape, exactly as the objection to landing it said.
- A deeper structural reason it could never have worked: the lookup takes
  `index` **by value**. Under Simple's copy-on-write value semantics any lazy
  Dict rebuild inside it is discarded on return, or deep-copies 946 entries per
  call. The repair cannot live in the by-value lookup at all.

### The real fix, and where it must live

Repopulate `index_by_name` from the retained scalar arrays at an OWNER site
where the field is mutable — immediately after `module_surfaces_promote`, or by
making promotion carry the Dict. Not in the lookup.

### Caveat — one link is evidenced, not proven

"Lookup misses -> unbounded memory" is inference. The runaway stalls in
`backend/interpreter.spl`, a DIFFERENT module from the one throwing the 17
errors. If the promotion fix lands and stage 3 still runs away, that is a
SECOND defect, and "fix in, explosion persists" is a valid finding rather than
a reason to assume the fix was wrong.

### Operational finding — stage 3 fail-closes on a DIRTY INDEX, silently

Stage 3 fail-closes on `dirty_fingerprint`, not just on HEAD. A parallel session
ran `git add` on five doc/script files between stage-2 admission and stage-3
start; HEAD never moved, but the staged-index change flipped the fingerprint and
stage 3 refused with **no diagnostic text at all** (silent rc=1). Index
mutations abort stage 3 exactly like commits do. Note that landing via git
plumbing with `GIT_INDEX_FILE` pointed at a scratch index does NOT trip this —
it never touches `.git/index`.

---

## RUN 3 (2026-08-23) — ROOT CAUSE, from a `sample(1)` of the live stalled process

The first direct measurement of the runaway, rather than inference from where it
stalled. `sample 88115 4` on the in-flight stage-3 process (pid 88115, launched
21:36:52, stalled at module 10/692) — read-only, no bootstrap started.

Physical footprint at sample time: **45.7 GB** (peak 47.2 GB), RSS 5.35 GB,
87.6% CPU. `sample` output preserved outside the tree.

### Where the CPU actually is

Of 3,288 samples on the single main thread:

| frame | samples | share |
|---|---|---|
| `HirLowering.register_imported_type_methods_inner` | 1,900 | 58% |
| `SymbolTable.lookup_or_invalid` | 1,142 | 35% |
| `SymbolId.is_valid` | 246 | 7% |

Collapsed **by top of stack**, one leaf dominates everything:

```
rt_transient_raw_register (in simple)   2550     (77.6% of ALL samples)
hashbrown ... HashMap::insert            447
```

Every one of the three Simple frames above spends its samples in
`rt_alloc` -> `rt_transient_raw_register`. This is an allocation storm, not a
computation.

### The mechanism, in two layers

**Layer 1 — the defect: read-side value-semantics clones.**
`SymbolTable.lookup`/`lookup_or_invalid` bound the scope row by value:

```
val scope = self.scopes[scope_id.id]        # copies the WHOLE Scope value,
if rt_dict_contains(scope.symbols, name):   # including symbols: Dict<text,i64>
```

At module/root scope that Dict holds every symbol in the closure, and the copy
happened on EVERY lookup. `define()` already carried the fix for the same rows
(`hir_types.spl`, "SCOPEROW ... `val scope = self.scopes[id]` copied the Scope
value (VT_OBJECT_FIELD_CLONES exactly 1 per define on the seed)", 2026-08-22) —
the two lookups, which are far hotter than define, were left behind.
`register_imported_type_methods_inner` calls `lookup_or_invalid` once per
imported method name, and is re-entrancy-guarded but NOT memoized, so the same
(module, type) pair is re-walked many times per importing module.

**Layer 2 — the amplifier: the streaming-HIR transient arena.**
`CompilerDriver.lower_streaming_surface_source`
(`80.driver/driver_hir_pipeline_lowering.spl:71-84`) opens
`rt_transient_array_scope_begin()` and deliberately keeps it **ACTIVE through
`lower_parser_module_unstub`** ("Keep the scope active through the complete
lowering"). While active, `rt_transient_raw_register`
(`src/runtime/runtime_memory.c:110`) records every `rt_alloc` as OWNED in a
thread-local open-addressing table and **nothing is freed until scope end**.

So churn becomes retention: each clone is retained for the whole module, the
table grows monotonically, and its doubling/rehash makes each further insert
more expensive. That is exactly the observed signature — monotone, accelerating
(~150 -> ~310 MB/min), 93% CPU, no log output.

**This is NOT a second defect and the arena is NOT the bug.** The arena's
retention is by design (ownership handoff); the fix belongs in the allocation
traffic, not in the pause/promote protocol.

### Why the CoW ratchet is blind to it

`scripts/check/check-cow-alias-hotpath.shs` reports
`PASS — 9682 file(s) scanned, 198 offender(s) checked, 0 new, 0 stale`, with
**zero offenders anywhere under `20.hir/`**. Its `BYVALUE` detector matches the
*write* side of the value-semantics class (`self.x = f(self.x, v)`). The defect
here is the *read* side — `val row = self.rows[i]` cloning a collection-bearing
row per probe. That shape is a detector gap, not a clean bill of health.

### Fixes landed (UNVERIFIED against the explosion)

- `20.hir/hir_symbol_table_methods.spl` `lookup` / `lookup_or_invalid`: probe the
  scope row IN PLACE (`self.scopes[id].symbols`), same transform `define()`
  already uses. `rt_dict_contains` + bracket read kept exactly — `.get` is
  forbidden on this path (false nil on present tagged ints).
- `20.hir/hir_types.spl` `pop_scope`: read `.parent` in place.
- `20.hir/hir_lowering/_Items/module_reexport_materialization.spl`
  `register_imported_type_methods_inner`: hoist the invariant
  `"{owner_module}.{imported_name}::"` prefix out of both method loops, and
  defer the `impl_.methods[name]` row read into the symbol-missing branch.

Verified, INTERPRETER-LEVEL ONLY: the four introduced syntactic shapes parse and
evaluate on the seed, and parse + semantic analysis of the edited lines is clean.
NOT verified: native codegen of these lines (chained bracket-reads have the
SCOPEROW precedent in `define()`; a `match` on a chained index+field subject does
NOT, and is exercised natively for the first time by the next bootstrap), and the
actual explosion.

**How to verify — do NOT re-run only the stage-3 leg.** The exploding code runs
inside the *stage2-admitted* binary
(`build/bootstrap/stage3/<triple>/stage2-admitted/simple`), which was compiled
from the PRE-edit tree. Re-running the stage-3 leg alone re-executes the old
code and would falsely read as "fix ineffective". Verification requires a full
re-bootstrap so stages 1-2 are rebuilt from this tree first
(`sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap`), and only
then the stage-3 leg.

### Still ranked, deliberately NOT changed

- `var trait_module = imported_mod` (same file, trait-impl branch) binds a whole
  `ModuleSurface` per trait-impl row — same read-side clone class, but off the
  sampled hot offsets and invasive to restructure.
- Whole-call memoization of `register_imported_type_methods` was considered and
  rejected: a first call may run before its dependencies resolve, so caching the
  outcome is not sound.

---

## RUN 3-5 (2026-08-23, macOS aarch64-apple-darwin) — the "dead carrier" premise is REFUTED by direct probe

Three measured stage-2 -> stage-3 cycles on this host. Stage 2 green each time
(`Build complete: 750 compiled, 0 cached, 0 failed` cold, then `6 compiled, 744
cached` warm; `stage2-sanity: pass`, `stage2-provenance: pure-simple`,
`ADMISSION_RC=0`).

### 1. `Dict.len()` lies after the teardown; the carriers are NOT dead

A one-shot probe of the PRE-rebuild carrier, printed from the driver owner site
immediately after `rt_transient_array_scope_end()`:

```
[module-surface] pre-rebuild authority carrier probe: surface=0 names=26 dict_len=-1 contains=true key=rt_native_build
```

`contains_key` answers **true** on the very carrier whose `len()` reports `-1`.
The same shape holds for the aggregate-valued Dict that crosses the boundary,
`ModuleSurfaceImpl.methods`:

```
[reexport-probe] owner=CompileMode module=compiler.common.driver_core_modes impl_rows=1 methods_dict_len=-1 methods_keys=2 visited=1
[reexport-probe] owner=AssuranceStrictness module=compiler.common.assurance.policy_schema impl_rows=1 methods_dict_len=-1 methods_keys=4 visited=5
```

`len()` is `-1` while `keys()` returns the right number of usable keys. So the
RUN-2 inference "dead carrier -> every frozen lookup returns found:false" was
wrong: only the **count** is unreadable after teardown. Nothing was silently
missing every lookup.

### 2. What landed, and what it actually did

The operative unblocking change is the CRITERION, not the repopulation: the
len()-based gate refused a registry that was in fact usable. The rebuild is a
verified-harmless defense that additionally proves all 946 keys answerable.

`module_surfaces_rebuild_declaration_authority_carriers_error`
(`src/compiler/20.hir/hir_lowering/module_surface_registry.spl:441`), called from
`driver_source_pipeline_parsing.spl:493` immediately after
`rt_transient_array_scope_end()`, rebuilds each surface's `index_by_name` from
the retained `names` array into a FRESH Dict and publishes it with the freeze
path's explicit write-back. O(946 keys) once, never per lookup. It then
verifies EVERY key through the published registry path.

The len()-based gate in `module_surfaces_frozen_alignment_error`
(`module_surface_registry_index.spl:254`) was replaced by a functional probe of
`module_surface_declaration_authority_lookup` over every key, comparing the
answered `declaring_module` against the scalar array. This is not the reverted
relaxation `10fc2c44785`: that TOLERATED a bad carrier, this VERIFIES a good
one and still fails closed. Phase-2 retention now passes with all 946 keys
proven answerable.

Note for anyone re-deriving this: a freshly allocated, freshly filled
`Dict<text, i64>` with 26 entries ALSO reported `len() == -1` at this site
(`rebuilt authority dict carrier is not viable: index=0 names=26 rebuilt=-1
dead_dict=-1`). `len()` is unreliable in this lowering context regardless of
teardown; never gate on it here.

### 3. The explosion is a SECOND defect, and it is now located by profile

With the carrier proven live, stage 3 still runs away, in
`phase3:hir:imports`, in `src/compiler/backend/backend/interpreter.spl` — the
same module RUN 2 named.

**Judge these runs by FOOTPRINT, not `ps` RSS.** RSS read as a flat 4-8 GB while
`vmmap --summary` reported:

```
22:41:42 rss_kb=7789248 footprint=34.3G
22:44:38 rss_kb=7322784 footprint=35.8G
22:47:35 rss_kb=6135296 footprint=36.9G
22:50:34 rss_kb=5468160 footprint=38.1G
```

Monotone ~+0.45 GB/min with RSS FALLING. Swap 5.66 GB of 7.17 GB. SIGTERM'd at
38.1 GB.

`sample` on the live process, twice 21 minutes apart and again in a later run,
gives an identical picture: **~100% of samples in
`HirLowering.register_imported_type_methods_inner`
(`_Items/module_reexport_materialization.spl:1104`), inside `rt_alloc ->
rt_transient_raw_register`**, at the insert-probe offsets of
`runtime_memory.c:110`. Before the read-side CoW fixes landed in the tree the
same profile also showed `SymbolTable.lookup_or_invalid` (35%) and
`SymbolId.is_valid` (7%); after them the whole cost collapses into five
allocation sites inlined in `register_imported_type_methods_inner` itself.

It is an allocation storm, not a leak: `driver_hir_pipeline_lowering.spl:71-84`
holds `rt_transient_array_scope_begin()` active across the whole module
lowering, so every `rt_alloc` is recorded OWNED and nothing is freed until scope
end, while the registry's probe cost grows with its own size.

### 4. Side effect worth noting

The read-side CoW fixes did not only change speed: `[hir-fatal-count]` for
`driver_riscv_gen2_product.spl` went **45 -> 24** and `driver.spl` reports 8.
The `unresolved type` / `field not visible` class is therefore also NOT explained
by the surface registry, and is a third open thread.


---

## RUN 6 — the "retention" explanation was WRONG; it is the owner TABLE

Two corrections to what earlier sections (and commit `5cfc9d13c66`) asserted,
both with file:line:

1. **The transient scope is NOT held across the whole lowering.**
   `rt_transient_array_scope_begin()` is at `driver_hir_pipeline_lowering.spl:72`
   and `driver_end_transient_parse_scope()` at `:113`, both inside
   `lower_streaming_surface_source`, which handles ONE `SourceFile`. Between them
   sit four fail-closed promotion guards (`:86` HIR module, `:92` diagnostics,
   `:96-102` flat HIR row, `:103` frontend registries), each rolling back and
   ending the scope on failure. `rt_transient_array_scope_pause()` at `:82`
   clears the OWNED bit for post-lowering allocations.
2. **Retention is not the mechanism.** `rt_free` frees IMMEDIATELY even inside an
   active scope — `runtime_memory.c:543-566` erases the table entry, then calls
   `free(ptr)`. Per-module churn does not become retained user memory.

So "every alloc is recorded OWNED and freed only at scope end" was wrong, and the
narrowing it implied is both unnecessary and unsafe: the current boundary is
already the narrowest that keeps the four promotion handoffs atomic, and
splitting it would place a scope end between lowering and
`rt_transient_heap_promote` — exactly the zeroed-payload/UAF class of
`stage3_streaming_hir_owner_crash_after_origin_fix_2026-08-22.md`. **Do not
narrow this scope.**

### What is actually hot

`rt_transient_raw_insert` (`runtime_memory.c:53`) is open-addressed with
tombstones, amortized O(1) — not a linear scan. Two STRUCTURAL defects make it
dominate the profile:

- **Tombstone-driven doubling.** The grow trigger counts tombstones as occupancy
  (`runtime_memory.c:113-115`, `runtime_native.c:1343-1344`), but
  `rt_transient_raw_grow` only ever DOUBLED. Since `rt_realloc` (`:495-536`)
  frees the old block on every array/dict growth, a long scope accumulates
  tombstones and capacity tracks CUMULATIVE CHURN rather than the live set.
- **High-water capacity retained across scopes.** `rt_transient_raw_scope_end`
  (`:182`) and `rt_core_transient_raw_clear` memset but never release, so one
  large module charges every later module an O(cap) scan, a full memset, and a
  random probe into a huge sparse array on EVERY `rt_alloc`. That is what
  `rt_transient_raw_register` at ~100% of samples looks like.

The exact fix already existed in-repo, unported: `rt_core_register_immortal_ptr`
(`runtime_native.c:1487-1495`), whose comment describes this incident shape
verbatim.

### Fix and measurements

`grow()` becomes `resize(next_cap)` — a same-capacity rehash is the only way to
purge tombstones under linear probing; the register path selects same-cap when
`tombs > len && (len+1)*10 < cap*5`, mirroring the precedent; and scope-end
RELEASES the table when `cap > 4096` instead of memsetting it. The `bytes` word
is carried verbatim, so the OWNED bit and size survive.

- realloc-shaped churn: steady-state capacity **16384 -> 1024**, identical live sets
- one 4M-node module then 300 small ones: those 300 follow-on scopes
  **1.043 s -> 0.022 s (47x)**, and 128 MiB of table returned rather than retained
- pure monotone live growth: **identical** before and after — the fix correctly
  does NOT fire on legitimate sizing
- `rt_transient_heap_scope_selfcheck` (the ownership fence): **77 checks, 0
  failures**, against an archive built from the modified sources

UNVERIFIED: the real 34 -> 38 GB explosion. Evidence here is C-level only; no
bootstrap was run. Three `rt_mem_guard_*` selfchecks trap at rc=133 and are
PRE-EXISTING — they reproduce identically on a `git archive HEAD` export.


---

## RUN 7 — RESOLVED. The allocation storm is fixed: ~60x, and 610 ms where it once ran 31 minutes

The dominant cost was never the bytes; it was the ALLOCATION COUNT, which is what
`rt_transient_raw_register` hotness actually measures.

**Site 1, dominant by count** — `imported_impl_positions`, old
`_Items/module_reexport_materialization.spl:1101-1105`. Every call allocated: a
copy of the `[i64]` row on a hit, or a **fresh empty array** (`val none: [i64] = []`,
old `:1104`) on a MISS. Types with zero impl rows are the common query, so the
sampled offset was literally the empty-array allocation. The profile pointed
exactly here.

**Site 2, dominant by bytes** — `val impl_ = imported_mod.impls[...]`, old `:1126`,
deep-clones a whole `ModuleSurfaceImpl` INCLUDING its
`Dict<text, ModuleSurfaceCallable>` of full signatures, once per impl row per
call, repeated many times per importer (re-entrancy-guarded, not memoized).

**Site 3** — `impl_.methods.keys()` materialized per impl row per call; subsumed
by the site-2 fix.

### Fix

`imported_impl_positions` becomes `ensure_impl_index(imported_mod) -> text`,
returning the surface KEY rather than an array, so the caller answers "any
impls?" with a pure `contains_key` and **allocates nothing on the empty path**.
IMPLROWCACHE extends the existing one-sweep-per-surface index to record, per impl
position, the impl's method names and (only when `has_trait_`) its trait name;
the hot loop reads those instead of materializing a row, and the whole row is
materialized only in the cold symbol-missing branch. `contains_key` is the
`has_trait_` test, so a trait projecting to `""` stays distinguishable from "no
trait". Both dicts are pure functions of the frozen registry, exactly like
`impl_index_positions`.

### A memo that was tried and REMOVED — recorded so nobody re-adds it

A "proven no-op" completion memo (probe-rechecked, importer-scoped) made things
strictly WORSE: with it, stage 3 crashed at HIR file 40/692; with it gated off,
157/692. It also silently suppressed the 27 `driver_riscv_gen2_product` errors
and then SEGV'd — under-registration. Fully removed; `grep` for its identifiers
returns zero hits.

### Measured

| run | footprint peak |
|---|---|
| RUN 5 baseline | 34.3 -> 35.8 -> 36.9 -> 38.1 GB, +0.45 GB/min, SIGTERM'd |
| post-fix | 369.4 -> 449.4 -> 473.3 -> **600.3 MB** |

**~60x reduction, and the monotone growth is gone.**

`backend/interpreter.spl` — the module that ran away for 31 minutes — now:

```
+231923ms phase3:hir:file:start src/compiler/backend/backend/interpreter.spl
          imports:start / imports:done / declare:start / declare:done
[hir-fatal-count] path=.../interpreter.spl count=2 shown=2  (field `symbols` is not visible)
+232533ms phase3:hir:file:start src/compiler/backend/backend/sdn.spl   dt=610ms
```

**610 ms.** Stage 3 continued to HIR 104/692, and 157/692 in the best run.
Stage 2 remains green: `Build complete: 750 compiled, 0 cached, 0 failed`,
`Time: 619.3s compile + 10.1s link`, `Stage 2 admitted`.

## NEXT BLOCKER (new, profiled, NOT fixed) — SIGSEGV in `lower_hir_block`

Stage 3 now SIGSEGVs in `HirLowering.lower_hir_block`
(`_Expressions/block_and_asm_lowering`), always just after
`phase3:hir:declare:done` — i.e. in BODY lowering — at tiny offsets off a
nil/garbage base: `0x298`, `0x370`, `0x698`, `0x18` across runs. Crash DEPTH
varies run to run on the SAME binary (phase 2, file 9, 40, 104, 157), so it is
**heap-state-dependent, not deterministic logic**.

**Attribution is UNRESOLVED, and that is stated rather than guessed.** The tree
used for those runs carried several agents' uncommitted edits, all present in
every binary built: `hir_symbol_table_methods.spl` (+-35), `hir_types.spl` (+-7),
`module_surface_registry*.spl`, `runtime_memory.c` (+-46), `runtime_native.c`
(+-44). One attempt crashed in `flat_ast_to_module` during PHASE 2 with a wild
pointer `0x20f0010f3a884ba8`, before any HIR lowering runs at all — the reexport
changes have no mechanism to cause that, but in-flight `runtime_memory.c` work
does. **The two unverified read-side CoW edits have since been reverted out of
the tree to remove that confound; the runtime table change is landed and is the
prime remaining suspect to isolate.**

Stage 4 and Stage 5/MCP were not reached: there is no admitted stage-3 artifact
while stage 3 SIGSEGVs. `--no-mcp` was NOT passed.


---

## RUN 8 — the runtime owner-table change is NOT the SIGSEGV cause (bisect, 3 runs per arm)

`c530678f8ba` is exonerated. Arm validity is proven, not assumed: the two arms'
runtime archive hashes and stage-2 binaries differ
(`deps` `3ed388ce…` vs `a0abe98e…`, stage2 `7af1af9ae867…` vs `3e779d9df28a…`).

| arm | run | depth | fault |
|---|---|---|---|
| B (origin runtime) | B1 | **phase 2**, `flat_ast_to_module` | `0x2d0f22ea648ffd20` |
| B | B2 | HIR 180/692 `vhdl_backend.spl` | `0x50`, peak 442.6 MB |
| B | B3 | HIR 69/692 `aop.spl` | `0x638`, peak 310.4 MB |
| A (`runtime_memory.c` reverted) | A1 | HIR 42/692 `hwir/aspects.spl` | `0x5000000000`, peak 274.9 MB |
| A | A2 | HIR **237/692** `driver_compile_vhdl_util.spl` | `0x260`, peak 504.5 MB |
| A | A3 | HIR 96/692 `watcher/smf_manifest.spl` | `0x6e0`, peak 375.1 MB |

6/6 crashed, same function, same instruction, overlapping depth ranges — and
arm A went DEEPER than arm B's best (237 vs 180). The change is not necessary
for the crash. n=3 per arm cannot exclude a frequency or depth effect, but
nothing in the data suggests one.

**Scope caveat:** arm A reverted only the `runtime_memory.c` half. Reverting the
`runtime_native.c` half fails to compile against the working tree's
`unix_common.h` (`conflicting types for 'rt_msync'` / `'rt_file_lock'`) — a
tree-mixing trap. That half is inert regardless:
`build/simple-core/libsimple_runtime.a` predates the commit and
`rt_core_register_immortal_ptr` is absent from the stage-2 binary, so
**`runtime_native.c`'s half has never been compiled into any artifact**. Its
first real exercise arrives when a lane rebuilds the capsule.

**The uncommitted-edits confound theory is DEAD.** B1 reproduced the phase-2
`flat_ast_to_module` wild-pointer crash on a tree with the HIR read-side edits
already reverted. So is "only a runtime allocator change can cause a phase-2
crash" — the earlier reasoning in RUN 7 was wrong on that point.

## The actual crash, measured from register state

Faulting instruction is `lower_hir_block` **+0x80c** (function base
`0x1000de940`). Note the `.ips` `imageOffset` (`0xdf14c` / `0xdfc8c`) is an
IMAGE offset — do not feed it to `atos`.

```
1000df13c  ands x9, x24, #0xfffffffffffffff8   ; untag
1000df148  csel x8, x9, x0, ne
1000df14c  ldr  x9, [x8]                        <-- FAULT
1000df154  str  x9, [x0]
1000df158  ldr  x8, [x8, #0x8]                  ; 16-byte value copy
```

From `threadState`, not inference: `x24 = 0x261 / 0x6e1 / 0x5000000001` — always
with the **low bit set (tag)** — and `x24 & ~7` equals the fault address exactly
in every run. So a **tagged value whose tag claims heap-pointer but whose payload
is a small int or garbage** reaches a 16-byte value copy in `lower_hir_block`.
All six faults are derefs of non-pointer values; plausibly ONE defect class
landing wherever heap state puts it (inference).

Every `.ips` carries only 2 frames — there is no usable backtrace, so do not
chase the unwinder. The crash is always immediately after
`phase3:hir:declare:done`, on a different module every run.

Operational: a warm `--stop-after-stage2` is ~90 s and each stage-3 run is
~4-5 min, so repetitions are cheap once an arm is built.

---

## RUN 9 — the `lower_hir_block` SIGSEGV is ELIMINATED (0/6 crashes, two binaries, six runs)

### The faulting construct, mapped from the disassembly (not inferred)

`lower_hir_block` is a `HirBlock` **constructor**, and the fault is the inlined
copy-on-write clone the codegen emits for `HirBlock.value`. `HirExpr` is 4 words
`{kind, has_type_, type_, span}`; `HirType` is 2 words `{kind, span}`; `Span` is 6.
The emitted clone recurses `HirExpr -> type_ (2 words) -> span (6 words)`, and
each level is guarded by nothing but `tag == HEAP && (v & ~7) != 0`:

```
and  x8, x24, #0x7      ; tag
cmp  x8, #0x1           ; == HEAP?
ands x9, x24, #~7       ; != 0?
csel x8, x9, x0, ne
ldr  x9, [x8]           <-- FAULT
```

A word like `0x261` satisfies both tests, so the guard is a SHAPE test, not a
validity test. That is the whole defect at this site.

### Where it comes from — narrowed to a class, NOT to a producer

Not found, and stated as not found. What is established:

* The malformed word already exists when `lower_hir_stmt_multi` returns. Probes
  at capture and at construction bracket only that window; `DECAYED` fired **0**
  times in 6 runs, which bounds the window, it does not prove formation.
* The firing MODULE SET is largely non-deterministic: 75 / 91 / 76 modules across
  three runs of one binary, only **18 common to all three**, union **169**. A
  content-dependent producer would give a stable set. (Discriminator, measured.)
* The second crash signature is the strongest evidence: `x24 = 0xbd8f2f721` — a
  sound heap address — whose interior `HirType.span` word was `0x11`, faulting at
  `ldr [0x10]` (`KERN_INVALID_ADDRESS at 0x10`, image offset `0xdf690`). A sound
  object with a garbage interior word is a reuse/half-reclamation artifact;
  constructors write either a real span or `nil`, and `nil` codegens to a fresh
  zeroed `rt_alloc`. **Inference**, but it is the streaming-HIR-owner class
  (`stage3_streaming_hir_owner_crash_after_origin_fix_2026-08-22.md`), not a
  constructor bug.
* `c530678f8ba` stays exonerated (RUN 8). `_Expressions/expression_core.spl` is
  ALSO exonerated as the producer: its `has_type_` fix was already in the binary
  that still fired the probe 43 times.

### What changed — CONTAINMENT, not a cure

1. **`expression_core.spl` (hardening, real but not the cure).** Index lowering
   tested `lowered_base.type_ != nil` and then interpreted `base_type.kind`.
   `has_type_` is the authoritative presence bit, and a `has_type_: false`
   placeholder is a non-nil fresh allocation, so the nil test let a placeholder
   be read and its enum payload extracted into a stored `type_`. Now gated on
   `lowered_base.has_type_`.
2. **`block_and_asm_lowering.spl` (containment).** Formation probes
   (`rt_heap_ref_wellformed`) at the capture site and again before the HirBlock
   construction, plus: the tail expression is re-formed with a FRESH placeholder
   type (`has_type_: false, type_: nil`) so a foreign `HirType` never reaches the
   clone, and a malformed `span` falls back to `b.span`. Named diagnostics
   `E-HIR-BLOCK-VALUE-TYPE-MALFORMED` / `-SPAN-MALFORMED` / `-DECAYED`.

**One level of validation is provably not enough** — that was measured, not
assumed: with only `type_` validated a run reached HIR 295 and then SIGSEGV'd one
field deeper in the Span clone.

### TRAP — a formation probe must never take a struct PARAMETER

`fn hir_type_span_wellformed(t: HirType) -> bool: rt_heap_ref_wellformed(t.span)`
was written, built, and **reverted**. A struct-typed parameter is DEEP-CLONED on
entry and the clone recurses into the nested `span` behind the same tag-only
guard — `rt_alloc #0x30` then `ldr [x8]` on the very word being validated. The
probe crashes exactly where it is meant to guard. Verified in the disassembly of
`_compiler__hir__hir_lowering__types__hir_type_span_wellformed` at
`0x100153818`. An `Any` parameter is passed verbatim with no clone (also
verified: every live probe compiles to `ldr x0, [reg, #0x10]` feeding the `bl`).
A deeper check must take the raw word as `Any` and do the field read in C.

### Measured — 6 stage-3 runs, 2 binaries, 0 SIGSEGV

| binary | run | HIR modules reached | SIGSEGV | MALFORMED | SPAN | DECAYED |
|---|---|---|---|---|---|---|
| containment v1 | 1 | 586 | 0 | 97 | 96 | 0 |
| containment v1 | 2 | 632 | 0 | 157 | 155 | 0 |
| containment v1 | 3 | 597 | 0 | 111 | 106 | 0 |
| final (`fa21bde5…`) | 1 | 598 | 0 | 149 | 148 | 0 |
| final | 2 | 599 | 0 | 131 | 128 | 0 |
| final | 3 | 586 | 0 | 172 | 171 | 0 |

Prior best before this change was **237** modules, and 6/6 crashed. No new
`.ips` was produced by any of the six runs.

### Stage 3 still does not COMPLETE — different, pre-existing blocker

Every run now reaches a phase never reached before, `phase3:hir_typecheck`, then
fails (rc=1) on accumulated HIR **semantic** errors, led by the already-known
`driver_riscv_gen2_product.spl` set (`field 'source_map' is not visible from this
module`, …) and a large `unresolved type: MethodResolution` / `unresolved name:
BlockExample` population. These are name/visibility resolution failures, not the
crash, and they are the next blocker. Stage 4 and Stage 5/MCP remain unreachable:
there is no admitted stage-3 artifact. `--no-mcp` was NOT passed.

**Caveat to carry forward:** the containment drops the tail expression's `type_`
unconditionally, and `unresolved type` counts rose (761 over 295 modules -> ~2050
over ~590). Most of that is reaching twice as many modules, but it is not proven
that none of it is the dropped type. Restoring a narrow "keep a fully validated
type" path needs the `Any`-parameter runtime probe described above.

### Ratchet note

`hir_heap_ref_wellformed` in `20.hir/hir_lowering/types.spl` adds **one** direct
`rt_*` call site under `src/compiler` (not an allowlisted provider), so
`scripts/check/no_direct_rt_baseline.txt` (11816) may need +1. It could not be
measured here: `check-no-direct-rt.shs` aborts on this host with
`ERROR — selftest failed: hidden/ignored files not scanned equivalently (got '1 2 0 2')`,
which is a pre-existing environment failure, not caused by this change.

---

## RUN 10 (2026-08-24) — the containment confound is QUANTIFIED (~0), and the dominant HIR-semantic population is FIXED: stage 3 now reaches 692/692

### 1. The carried caveat is discharged: the containment manufactures ~no unresolved types

Three independent discriminators, all computed from the RUN 9 logs (no new runs
needed — `f_run1..3` and `v2_run1..3` were retained):

**(a) Cross-tab, per module, 6 runs / 2 binaries.** `E-HIR-BLOCK-VALUE-*` names
the module it fired in, so every reached module is classifiable. Rate of
`unresolved type` fatal errors per module:

| run | fired mods | unres/mod (fired) | not-fired mods | unres/mod (not fired) |
|---|---|---|---|---|
| f_run1 | 103 | 1.262 | 495 | 1.129 |
| f_run2 | 91 | 0.934 | 508 | 1.189 |
| f_run3 | 104 | 0.865 | 482 | 1.191 |
| v2_run1 | 77 | 0.649 | 509 | 1.202 |
| v2_run2 | 98 | 0.878 | 534 | 1.154 |
| v2_run3 | 79 | 0.734 | 518 | 1.203 |

In **5 of 6 runs the containment-fired modules carry FEWER unresolved types per
module than the modules it never touched**, and the one exception is +0.13. If
the dropped `type_` were manufacturing unresolved types the sign would be
consistently the other way.

**(b) Same-module prefix comparison.** Over the 71 modules that produced fatal
errors in BOTH the pre-containment runs (`A1..A3`, `B2..B3`) and the
post-containment runs, mean total errors were **717.0 pre vs 751.3 post
(+4.8%)**, and the per-module deltas are BIDIRECTIONAL (largest increase
`driver_types.spl` +15.8, largest decrease `retirement_composition.spl` -6.0).
That is drift, not a new population.

**(c) Structural — there is no mechanism.** `unresolved type: {name}` has exactly
one emitter, `20.hir/hir_lowering/types.spl:1011`, in `lower_named_kind`'s final
`else`: it requires a NAMED type annotation whose symbol lookup failed. The
containment installs `has_type_: false, type_: nil` — a nameless placeholder that
never reaches `lower_type` at all.

**Conclusion: essentially 0% of the unresolved-type population is caused by the
containment.** The rise from 761/295 to ~2050/~590 is reach plus module mix. The
`Any`-parameter C-side probe is therefore NOT needed to unblock stage 3; it
remains the right design if a validated-type path is ever restored.

**Correction to a RUN 9 number.** "~2050 over ~590 modules" overcounts: the log
prints every fatal twice (`[hir-fatal]` and `error: in-process native-build:`).
The authoritative totals are the `[hir-fatal-count] count=` sums: **1362 / 1445 /
1351** for f_run1..3.

**And the reach figure was budget-bound, not error-bound.** All six RUN 9 runs
reported **exactly 200 error modules**. That is `poison_budget()`
(`80.driver/driver_types.spl:1048`): the HIR phase stops after 200 poisoned
modules. So "586-632 modules" was the point at which the budget ran out, and the
error inventory was truncated.

### 2. Root cause of the unresolved-type population — glob imports are not a materialization route

Two owner modules, one mechanism, ~1,660 of the ~1,700 unresolved-type
occurrences:

* `[hir-payload-origin-unresolved] owner=compiler.hir.hir_definitions
  payload=MethodResolution` — `hir_definitions.spl` declares
  `HirExprKind.MethodCall(..., resolution: MethodResolution)` and reaches
  `MethodResolution` only through `use compiler.hir.hir_types.*`. Result: 493
  `unresolved type: MethodResolution` blamed on importers of `HirExprKind`.
* `[hir-callable-dep-origin-unresolved] owner=compiler.hir.hir_types
  dependency=HirClass` (+12 siblings) — `HirModule` types 13 of its fields with
  declarations in `hir_definitions.spl`, and `hir_types.spl` carried **no import
  of that module at all**; the names were reachable only because
  `hir_definitions` globs `hir_types` back. Result: HirClass 93, HirStruct 93,
  HirTrait 93, HirStaticAssert 93, HirImpl 93, HirConst 93, HirBitfield 93,
  HirEnum 92, HirFunction 91, HirAopAdvice 91, HirDiBinding 52, HirArchRule 52,
  HirMockDecl 51.

`resolve_materialized_enum_payload_origin`
(`_Items/module_reexport_materialization.spl:294`) accepts only three routes —
a declaration in the owner, an `export use` hop, or an **explicit named** import
— and says so: *"Glob imports stay excluded here: resolving them while
recursively materializing enum payloads corrupts staged native HIR state."*
This is the same defect class already fixed in this very file for
`AsmConstraintKind`/`AsmLocation`, and the fix is the same: name the dependency
explicitly in the OWNER.

A third, smaller instance: `compiler.blocks.blocks.builtin_blocks_{data,math,
shell}` use `BlockExample`/`HighlightToken`/`HighlightKind`/`Completion`/
`CompletionKind`/`BlockType` in declaration position while importing only
`{BlockDefinition}`/`{ConstValue}` from `compiler.blocks.definition`
(BlockExample 43, HighlightToken 42, plus the `unresolved name:` twins).

### What changed (5 files, imports only — no logic, no codegen)

| file | change |
|---|---|
| `src/compiler/20.hir/hir_definitions.spl` | `use compiler.hir.hir_types.{MethodResolution, HirType, SymbolId, Effect}` |
| `src/compiler/20.hir/hir_types.spl` | `use compiler.hir.hir_definitions.{HirFunction, HirClass, HirStruct, HirEnum, HirBitfield, HirTrait, HirImpl, HirConst, HirStaticAssert, HirAopAdvice, HirDiBinding, HirArchRule, HirMockDecl}` |
| `src/compiler/15.blocks/blocks/builtin_blocks_data.spl` | + 6 names from `compiler.blocks.definition` |
| `src/compiler/15.blocks/blocks/builtin_blocks_math.spl` | + 3 names |
| `src/compiler/15.blocks/blocks/builtin_blocks_shell.spl` | + 3 names |

Stage 2 recompiled **8 modules** and produced a stage-2 binary whose sha256 is
`fa21bde58b9e6f64f8abec0e316f10333d193557da45eff7a7def04f16d45ff1` — **byte
identical to the RUN 9 "final" binary**. Imports change no emitted code, so the
RUN 9 logs are an exact control and every stage-3 difference below is caused by
the SOURCE input alone.

### Measured

| run | HIR modules | SIGSEGV | error modules | total fatal | `unresolved type` (distinct names) |
|---|---|---|---|---|---|
| RUN 9 f_run1 | 586-632 (budget-bound) | 0 | **200 (budget)** | 1362 | MethodResolution 493 + 13 `Hir*` + … |
| RUN 9 f_run2 | " | 0 | 200 (budget) | 1445 | " |
| RUN 9 f_run3 | " | 0 | 200 (budget) | 1351 | " |
| RUN 10 run1 | 0 | **1** (phase 2, surface parse of `driver.spl`) | — | — | — |
| RUN 10 run2 | **692 / 692** | 0 | **72** | **506** | 5 names, 19 occurrences |
| RUN 10 run3 | **692 / 692** | 0 | **63** | **587** | — |

**Every HIR module in the build is now reached, and the poison budget is no
longer exhausted — so the remaining error inventory is complete rather than
truncated.** `MethodResolution` and all 13 `Hir*` names are gone from the log
entirely. The RUN 10 run-1 crash is the pre-existing stochastic phase-2
`flat_ast_to_module` class already recorded in RUN 8 arm B1; the binary is
byte-identical to one that did not crash in 6 RUN 9 runs, so it cannot be
attributed to this change.

### Stage 3 still does not complete — the remaining blocker is FIELD VISIBILITY, a SEPARATE root cause

This answers the open question directly: the two populations do **not** share a
root. Fixing the materialization route removed the unresolved-type population
almost entirely and left field visibility **untouched** (191 shown occurrences in
run 2 vs 123/142/170 in RUN 9 — i.e. it is now the dominant class):

```
191  field `X` is not visible from this module
 19  unresolved type: {ModuleSurfaceEnum 7, ReturnScan 4, BackendCompileOptions 4, CodegenTarget 3, TreeSitter 1}
  ~40 unresolved name: ... at <import span>   (var_reassign_local_id_value, methods_push, …)
   2  ambiguous explicit callable dependency `AopWeaver` / `DiContainer`
```

Top field names: `symbols` 13, `span` 11, `name` 11, `mir_modules` 10,
`surfaces` 9, `id` 9, `bit_width` 9. Top modules: `mir/hwir/types.spl`,
`loader/jit_instantiator.spl`, `hir_lowering/module_surface_declarations.spl`,
`hir/generated/hir_codec.spl`, `frontend/treesitter/outline.spl`,
`driver/driver_types.spl`, `driver/driver_aot_pipeline.spl` (10 each).

What is established about the mechanism, and what is not:

* The single emitter is `_Expressions/expression_core.spl:293`, gated on
  `self.field_access_for_expr(base, field) == 0`.
  `field_access_for_expr` (`_Expressions/expression_support.spl:307`) returns 0
  from THREE places, and they are not the same failure:
  1. base symbol is in `local_struct_types` but that composite name has no
     entry in `struct_field_access_by_name`;
  2. a nominal owner resolved but its composite name is "" or unregistered —
     *"a malformed compiler boundary, not permission to bypass visibility"*;
  3. the retained per-field bool is genuinely `false`.
* Path 3 is UNLIKELY to be the bulk: the flat-AST bridge stamps every
  undecorated struct/class field `Visibility.Public`
  (`10.frontend/_FlatAstBridge/module_assembly.spl:381`, with a comment
  recording that a Private default previously produced 1512 errors across 44
  files), and `member_visibility_allows(Public, _)` is unconditionally true.
* A live suspect for path 2/3 is `member_owner_consistent`
  (`_Items/module_import_registration.spl:~300`): `member_owner` is chosen from
  `composite.fields[0].declaring_module` via `surface_index_for_name`, and when
  that lookup fails `member_owner` silently falls back to the IMPORTING surface;
  any composite reached through a facade then has every field denied at once.
  **Not confirmed** — the three failing modules sampled (`interpreter.spl`,
  `hir_codec.spl`, `const_eval.spl`) all import `HirModule` *explicitly* from
  `compiler.hir.hir_types`, which argues against a pure facade explanation.
* Discriminating the three requires one level-gated probe at the 0-returns
  printing the branch, the composite key, the owner module, and the six
  `MemberAccessScope` bits. That is the next step and it is NOT yet done.

Stage 4 / Stage 5 / MCP remain unreached: there is still no admitted stage-3
artifact. `--no-mcp` was NOT passed.

---

## RUN 11 (2026-08-24) — field visibility, mechanism established by probe: it is NOT visibility, it is owner misresolution

### The probe

`HIR_MEMBER_VIS_TRACE` (module-local `val`, default `false`, no `rt_env_get` —
the ratchet baseline is 11818 and this adds no direct `rt_*` site) in
`20.hir/hir_lowering/_Expressions/expression_support.spl` prints, at each of the
four places `field_access_for_expr` can answer "denied", which branch fired plus
the composite key, the owner symbol's name and its defining module.

### Probe run A — every denial is a lookup failure

Full 692/692-module stage-3 run, **313 denials, 313 of them the same branch**:

```
313 branch=owner-metadata-missing ... composite=  owner_name=<no-symbol> owner_module=<no-module>
  0 branch=retained-false
  0 branch=local-composite-unregistered
  0 branch=local-field-denied
```

`composite=` EMPTY and `owner_name=<no-symbol>` in **all 313**: the owner id was
non-negative, so the function treated it as a nominal owner, but it names no
symbol in this module's table. `branch=retained-false` — the only verdict that
means "the field really is not accessible" — fired **zero** times.

**Fix 1 (landed).** `named_owner_raw_for_expr`'s first branch reads
`HirTypeKind.Named(owner, _).id` straight out of the expression's `type_`, and a
type projected from an IMPORTED surface carries a SymbolId minted in the
DECLARING module's numbering, which need not name anything in the importer's
table. An owner id that resolves to no symbol now answers **unknown (-1)**
instead of **denied (0)**.

### Probe run B — the residue is misresolution to the wrong symbol

Same probe, after fix 1: **215 `owner-symbol-absent`** (now correctly unknown)
plus **33 `owner-metadata-missing`**, and again **0 `retained-false`**. The 33
name their own defect:

| module | field | resolved owner | what that owner actually is |
|---|---|---|---|
| `module_reexport_materialization.spl` | `symbols` | `hir_phase_profile_count_qtype` | a FUNCTION |
| `mir_opt/loop_opt.spl` | `loops` | `HirBinOp` | an unrelated enum |
| `hwir/retirement_composition.spl` | `config` | `destination_owner` | a local variable |
| `loader/compiler_sffi.spl` | `cache_hits` | `compiler_create_context` | a FUNCTION |

Same family as the 78 "enum payload dependency conflicts" documented in
`claim_materialized_payload_binding` (a symbol id that resolves to a record
sharing no name with the request). **So not one field-visibility error in the
entire compiler is a real private-field violation** — the flat-AST bridge stamps
undecorated fields `Visibility.Public` anyway
(`_FlatAstBridge/module_assembly.spl:381`), and `member_visibility_allows` can
only say yes for those.

### NEGATIVE RESULT — the metadata-missing arm must KEEP denying (3/3 runs)

Making that arm return -1 as well, to match its sibling `field_access_for_base_raw`
which returns -1 on the byte-identical condition, was built and run three times.
Field-visibility errors went to **0** and everything else got much worse:

| | reach | error modules | total fatal | profile |
|---|---|---|---|---|
| deny (0) | **692/692** | 45-49 | 285-365 | field-vis dominant |
| unknown (-1) | 395/402/395 | **200 (budget)** | **6517/6515/6517** | 447 `ambiguous explicit callable dependency`, ExportAttr 98, LayoutAttr 93, MirModule 89, FunctionAttr 70, MirFunction 63, MirBlock 56, DriverManifestAttr 54 |

Letting a Field expression continue past the gate on an owner the lowerer cannot
describe cascades into the import/materialization path — ~20x the cost of what
it saves. **Reverted.** The comment at that arm now records this so it is not
re-attempted. The real fix is upstream, in whatever mints/resolves the owner
SymbolId, not in the gate.

### Cumulative measurement across this session (stage 2 green every cycle: `Build complete: 750 compiled, 0 cached, 0 failed`)

| tree | run | HIR modules | SIGSEGV | error modules | total fatal |
|---|---|---|---|---|---|
| RUN 9 baseline | f_run1..3 | 586 / 599 / 598 (budget-bound) | 0 | 200 / 200 / 200 | 1362 / 1445 / 1351 |
| + explicit imports | run1 | 0 | 1 (phase-2, pre-existing class) | — | — |
| + explicit imports | run2..5 | **692 / 692 / 692 / 692** | 0 | 72 / 63 / 80 / 80 | 506 / 587 / 454 / 454 |
| + owner-symbol-absent guard | q_run1..3 | **692 / 692 / 692** | 0 | 49 / 47 / 42 | 365 / 312 / 285 |
| final (guard kept, -1 reverted) | t_run1..3 | **692 / 692 / 692** | 0 | 45 / 42 / 42 | 312 / 300 / 300 |

Stage 3 does **not** complete: rc=1 on ~45 poisoned modules / ~312 HIR semantic
errors, now dominated by the owner-misresolution field class above plus a small
tail (`unresolved name:` at import spans — `var_reassign_local_id_value`,
`methods_push`, `module_surface_name_position`, `format_shape`; `unresolved type:`
ModuleSurfaceEnum 7, ReturnScan 4, BackendCompileOptions 4, CodegenTarget 3;
2 `ambiguous explicit callable dependency`). Stage 4 / Stage 5 / MCP remain
unreached; `--no-mcp` was NOT passed.
