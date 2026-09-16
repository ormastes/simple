# Persistent native-build cache has no GC and a key that has rendered corrupt

- **ID**: native_build_cache_scope_key_renders_corrupt_persistent_cache_2026-08-08
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity**: HIGH (guaranteed unbounded disk leak on a 95%-full disk; plausible silent wrong-binary path in the stage-3 lane)
- **Found by**: adversarial review of `5b569e96986d` ("stop wiping stage2/stage3 native-build cache every run")
- **Files**:
  - `src/compiler/80.driver/driver_aot_native_output.spl:74-79, 101-111, 256-282, 348`
  - `src/compiler/80.driver/driver_build/incremental.spl:59-130, 414-433, 447-479`
  - `scripts/bootstrap/bootstrap-from-scratch.sh:1311, 1596`
  - `scripts/bootstrap/resume-stage3-from-admitted.sh:86-93`

## Summary

`5b569e96986d` stopped unconditionally `rm -rf`-ing the stage2/stage3
native-build cache dirs, on the stated grounds that the driver's own cache key
is content-hash based and therefore cannot serve a stale object. Two problems:
that `rm -rf` was also the **only garbage collector** for a cache whose scope
dirs are mint-once-never-reused, and the key's design soundness is undercut by a
rendering path that has demonstrably corrupted in practice.

## Finding 1 (confirmed, current) — the cache never reuses and never collects

`cache_scope_root` = `<dir>/backend=…;opt=…;compiler=<exe-sha>+src<tree-fp>/sources-<closure-hash>`.
Every component changes on any relevant edit, and the `sources-` component
covers the **whole** loaded closure — the commit's own plan doc concedes a single
changed file forces a full recompile. So each edit-and-build cycle mints a
*brand-new* scope dir holding a full object set, and nothing ever deletes the
prior ones.

This is not hypothetical. `build/native_cache` on this box, 2026-08-07, one
compiler binary (`f5dd94de…`), six scope dirs in a single day:

```
07:21  …+src39ae88b9bfee6e82n3081
11:38  …+src23e1793ddec7ef14n3083
16:03  …+srca7962324863ae746n3091
16:30  …+src887b73b0463f77f0n3093
17:58  …+src4bc1112888640976n3095
22:39  …+srcd27402ead0bd36e0n3097
```

Six full object sets minted, zero collected, zero reused (each has a distinct
key, so none could hit). A stage-3 scope measures 687 objects / 19 MB in this
repo; a full closure is larger. The host is at **95% disk (204 GB free,
`build/` alone 184 GB)** and has had two prior ENOSPC events that wiped `main`.
The removed `rm -rf` was the bound on this. Confidence: **high** — the dated
directory listing above is direct current evidence.

## Finding 2 (confirmed) — the key is nondeterministic for identical inputs

From the same cache, two scope dirs with the **same** 64-hex compiler sha, the
**same** source-tree fingerprint `src3f6dcd257a5fb590n2971`, the same backend,
the same mtime — differing only in a garbage `opt`:

```
backend=cranelift;cpu=nil;features=;opt=1061101969;compiler=6253cd59…+src3f6dcd257a5fb590n2971
backend=cranelift;cpu=nil;features=;opt=526418881;compiler=6253cd59…+src3f6dcd257a5fb590n2971
```

`opt` is an `i32` interpolated into the key
(`incremental.spl:130`); the driver only ever passes 0 or 3
(`driver_effective_native_opt_level:48-53`). Both values are garbage, and they
*differ between two runs of the same configuration*. `cpu=nil` is a second
rendering failure in the same string — `native_build_cache_scope_key`'s
`case nil: "native"` arm should have produced `native`.

Consequence: when this fires, the key never repeats, so the cache can never hit
and every run leaks a fresh scope dir. This makes the commit's claimed benefit
nil and Finding 1's leak deterministic. Confidence: **high** (two dirs are a
controlled pair, differing in exactly one field that had no legitimate reason to
differ).

## Finding 3 (single instance, plausible) — identity collapse enables collision

One scope dir shows four simultaneous rendering failures:

```
backend=cranelift;cpu=;features=;opt=81508897;compiler=<value:0x4e8a771>+srcn0
```

- `compiler=<value:0x4e8a771>` — the executable sha256 replaced by a raw
  pointer (the known native `to_text` defect family).
- `+srcn0` — `native_build_compiler_source_fingerprint`
  (`incremental.spl:59-102`) returns `"{digest.substring(0,16)}n{lines.len()}"`,
  so `srcn0` is an **empty digest with a file count of zero**. Verified against
  the return statement, not inferred from the prefix. Note the function has an
  `unfingerprintable-{pid}-{micros}` fallback that did *not* trigger, and a
  `digest.len() == 64` gate that *passed* — so a real digest existed and was
  lost at interpolation.

If this state recurs, two different `src/compiler` trees and two different
compiler binaries all render the same degenerate
`compiler=<value:0x…>+srcn0`, collapsing into one cache scope. With an unchanged
stage-3 source closure the `sources-<H>` component matches too, and every module
is a cache hit — stage 3 would link objects produced by a **different compiler**
and be admitted as a green self-host build. Silent, no warning.

Confidence: **medium**. This is a single directory exhibiting four corruptions
at once, which reads as one wholesale-broken binary rather than four independent
defects, and it is dated 2026-07-25. It is a demonstrated capability of this
code path, not a demonstrated recurrence.

## Why the fail-closed guard does not catch Findings 2 and 3

`native_build_compiler_identity()` (`incremental.spl:112-120`) falls back to
`uncacheable-{pid}-{time}` only when the executable hash is the **empty string**,
and `native_build_compiler_executable_hash()` gates on `hash.len() == 64`. In the
observed failure both checks passed and the value was lost afterwards, during
interpolation into the key string. A validity check on the *value* cannot detect
a corruption of the *rendering*. The guard fails open.

There is no second line of defense on this axis.
`BuildCache.has_cached_object` (`incremental.spl:447-467`) re-hashes the **source
file** and checks output existence, so the source-content axis is genuinely
double-checked; the **compiler identity** axis is checked only by the scope-root
path string.

## Was the wipe load-bearing?

Yes, on both counts — incidentally rather than by design (`git log -S` shows no
stale-object fix as its origin, so it was not placed as a deliberate mitigation).
It was the only GC (Finding 1), and it made Findings 2 and 3 unreachable in the
bootstrap lane: a cache emptied at the start of every run cannot serve a stale
object or accumulate dead scopes regardless of key quality.

## Secondary findings

- **`build_cache.sdn` is unscoped and shared.** `driver_native_build_cache_path`
  puts the index at the cache-dir **root**, above all scopes. On a scope
  mismatch `driver_aot_native_output.spl:348` calls `remove_entry`, so two
  alternating scopes mutually evict each other's index entries while their
  objects stay on disk unreachable — leaked *and* no hit.
- **`BuildCache.save()` (`incremental.spl:414-433`) is non-atomic** — direct
  `incremental_file_write_text`, no temp-then-rename, no completion marker. A
  kill mid-save (earlyoom is active here) now leaves a truncated index that
  persists across runs. Mitigated in practice: `load()` fails safe to an empty
  cache on parse error (`incremental.spl:405-412`), so the consequence is a lost
  cache, not a wrong one. Should still be made atomic.
- **Design gaps in the key**, independent of rendering:
  - `driver_aot_native_output.spl:77` hardcodes `target_features` to `[]`.
  - `SIMPLE_BOOTSTRAP_STAGE4` is read at `:242` but is not in the key.
  - `is_release` reaches the key only via `driver_opt_level`; when
    `ctx.options.opt_level` is explicitly set,
    `driver_effective_native_opt_level` returns it directly and `is_release`
    becomes invisible to the key while still being passed to
    `_compile_one_module`.

## Honest scoping

The Finding 1 evidence is from 2026-08-07 and is current. The Finding 2 and 3
corrupt dirs are dated 2026-07-25, produced by a compiler roughly two weeks old;
the newest scope dirs render cleanly, so those interpolation defects are not
currently reproducing in the lane that wrote them. That does **not** clear them:
most of `build/native_cache` was not written by a natively-built stage-2
compiler, which is the lane at risk. The burden of proof sits with the commit,
which landed by inspection only — its author reported being unable to run the
intended A/B/C/D scale verification because the stage2 binary segfaulted.

## Recommendation

**Revert the stage-3 half of `5b569e96986d`** (`bootstrap-from-scratch.sh:1596`
and `resume-stage3-from-admitted.sh`) until the cache has a GC and the scope key
is proven to render correctly under a *natively built* stage-2 compiler. Finding
1 alone justifies this: the commit trades a guaranteed, currently-observable disk
leak on a 95%-full disk for a benefit confined to the nothing-changed case.

Not fixed inline. The obvious small fix — a fail-closed shape assert on the
rendered key (`compiler=` is 64 hex, `opt=` parses to a small int, `src…`
non-empty), falling back to `uncacheable-{pid}-{time}` — is **unsafe on its own**
here: with no GC, every failing build would mint a fresh never-reused scope dir
that nothing deletes, converting a probabilistic leak into a deterministic one.
GC must land first.

Follow-up work, in dependency order:
1. Add scope-dir GC (keep N most recent) — prerequisite for everything below.
2. Then add the fail-closed rendered-key shape assert described above.
3. Make `BuildCache.save()` write-temp-then-rename.
4. Scope `build_cache.sdn` under `cache_scope_root` instead of the cache root.
5. Add `target_features`, `SIMPLE_BOOTSTRAP_STAGE4`, and `is_release` to the key.
6. Only then re-enable cache persistence in the bootstrap scripts.

---

## Resolution 2026-08-08 — measured correction, GC landed, no revert

Re-measured `build/native_cache` directly before acting on the recommendation
to revert. Three of this document's quantitative claims do not survive the
measurement, and the corruption is **not current**.

### Count correction: 86 scope dirs, not 186

`build/native_cache` holds 186 *entries*, but only **86** are scope
directories — the other 98 are loose `*.smf` files at the cache root. The
"186 scope dirs" figure counted both.

### Legality correction: 83 of 86 keys are legal, not 3

Distribution over the 86 real scope dirs:

| `opt=` value | dirs |
|---|---|
| `3` | 78 |
| `2` | 5 |
| garbage int (`81508897`, `526418881`, `1061101969`) | 3 |

So **83 of 86 (97%) carry a legal `opt`**, and exactly **one** dir has the
`compiler=<value:0x…>` pointer rendering. The "only 3 of 186 have a legal
opt" reading inverted the tally (it read the `78 3` / `5 2` histogram rows as
a count of 3). `cpu=` likewise renders correctly in 85 of 86: `native` ×63,
`riscv32-unknown-none` ×20, `nil` ×2, empty ×1.

### Currency correction: all corruption is confined to 2026-07-25

Scope dirs by mtime date, split by key legality:

```
date        legal  garbage
2026-07-22      3        0
2026-07-24     18        0
2026-07-25      5        3   <-- every corrupt dir, this day only
2026-07-28      9        0
2026-07-29      1        0
2026-08-01     11        0
2026-08-02      6        0
2026-08-04      2        0
2026-08-05     10        0
2026-08-06      6        0
2026-08-07     12        0
```

All 3 garbage-`opt` dirs and the single pointer-rendered `compiler=` dir are
dated **2026-07-25**. Every one of the 83 dirs written on the eleven other
dates — including all 12 written on 2026-08-07 — renders legally. The
rendering defect was live for one day two weeks ago and is not reproducible
in current output. Findings 2 and 3 are therefore **historical, already
fixed**, not live defects. No shape assertion was added: it would guard a bug
that no longer occurs, at the cost of editing compiler source (and its
bootstrap-rebuild blast radius) for zero current benefit.

### The key IS stable across runs — so the persistent cache does pay off

Finding 2's load-bearing conclusion was that the key is nondeterministic for
identical inputs, making cache hits impossible and commit `5b569e96986d` pure
leak. Tested directly on the 12 scope dirs written on 2026-08-07: stripping
the `+src<fp>n<count>` suffix collapses all 12 to a **single** distinct
prefix —

```
backend=llvm;cpu=native;features=;opt=3;compiler=f5dd94dea5924d03…d21e7d
```

— identical backend, cpu, features, opt, and compiler sha across every run
that day. Only the source fingerprint varies, and the module counts differ
with it (`n3073`, `n3079`, `n3081`, `n3083`, `n3091`, `n3093`, `n3095`,
`n3097`): those are genuinely different source closures from the many lanes
editing this repo concurrently, which is exactly what the fingerprint is
supposed to discriminate. The two dirs cited as proof of nondeterminism
(identical compiler+src, differing `opt`) are both from the 2026-07-25
corrupt batch and carry garbage `opt` values, so they evidence the historical
rendering bug rather than a live instability.

**Conclusion: the cache key is deterministic and the persistent cache does
hit.** Commit `5b569e96986d` is not all-cost-no-benefit, and is not reverted.

### Finding 1 stands and is now fixed

The GC gap was real and is the one finding that survives unchanged: scope
dirs are mint-once and nothing collected them once the unconditional wipe was
made conditional. Fixed by an age-based reaper, `bootstrap_native_cache_prune`,
defined inline in `scripts/bootstrap/bootstrap-from-scratch.sh` and
`scripts/bootstrap/resume-stage3-from-admitted.sh`, invoked on the preserved
path of each:

- Removes only entries matching the `backend=*` scope-dir shape, so sibling
  `build_cache.sdn` and `*.smf` files are never touched.
- Age-based (default 7 days, `BOOTSTRAP_NATIVE_CACHE_TTL_DAYS` to override,
  `0`/non-numeric disables). Age was chosen over LRU specifically so it needs
  no bookkeeping sidecar and **no lock protocol**: several lanes build
  concurrently on this host, and a scope dir untouched for 7 days cannot
  belong to a live build, so the reaper cannot pull artifacts from under a
  running lane.
- Fixture-verified before landing: 3 stale scope dirs pruned, 2 fresh ones
  kept, 3 old non-scope entries (`build_cache.sdn`, a plain dir, a `.smf`)
  all preserved; TTL=0, non-numeric TTL, missing dir, and idempotent rerun
  each exit 0 silently.

It was **not** placed in `scripts/check/lib/bootstrap-stage3-provenance.shs`:
that facade is byte-bound by the provenance manifest and documents "keep this
file small", so appending a utility there risks the Stage 3 provenance gate.

### Disk-pressure framing

The urgency premise ("96% disk, 167G free and falling") is real but is not
attributable to this cache. `build/native_cache` totals **12M**; the stage2/3
provenance caches this commit made persistent are 21–48M each across 24 dirs,
well under ~500M combined, against 167G free on a 3.7T volume. The reaper is
still correct to add — unbounded growth with no collector is a defect on its
own terms — but this cache was not a plausible ENOSPC vector, and no manual
`rm` sweep was performed (other lanes are mid-build).

### Not addressed

The secondary design gaps above (hardcoded `target_features`, absent
`SIMPLE_BOOTSTRAP_STAGE4` in the key, `is_release` invisible under explicit
`opt_level`, unscoped `build_cache.sdn` at the cache root causing alternating
scopes to `remove_entry` each other, non-atomic `BuildCache.save()`) are all
real and all remain open. They are correctness/efficiency issues in the key
and cache-index design, independent of both the GC gap and the persistence
change, and none of them is a disk-growth vector.

## Verification 2026-08-17 (w02/s4 lane) — GC half CONFIRMED LIVE

Classified by CONTENT (session brief CORRECTION 1).

Split verdict, matching the triage row:

- **Key half: FIXED.** `native_build_cache_scope_key` is present in
  `src/compiler/80.driver/driver_build/incremental.spl` at line 198, and
  `.claude/rules/commands.md` documents the lane axis (`SIMPLE_CACHE_SCOPE` /
  `--cache-scope`) landing 2026-08-17, partitioning entries by a scope-derived
  directory.
- **GC half: LIVE.** `grep -c 'cache_gc\|prune\|evict\|gc_'` over that same file
  returns **0**. There is no eviction, no pruning, and no size cap anywhere in
  the file that owns the cache scope key. The persistent native-build cache
  therefore still grows without bound on an already 95%-full volume.

Scoping entries by lane (the 2026-08-17 change) makes this *worse*, not better:
each additional scope gets its own directory of entries, and nothing reclaims any
of them.

**Verdict: LIVE (GC half only). No patch applied** — adding cache eviction is a
design change (retention policy, LRU vs size cap, concurrency against the live
bootstrap writing into `build/bootstrap/native_cache/<lane>/`), not a bug fix,
and this lane was instructed not to touch `build/bootstrap/**`.
Not proven: actual disk consumption was not measured this session.
