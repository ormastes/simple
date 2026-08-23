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
