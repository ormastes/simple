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
