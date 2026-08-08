# Persistent native-build cache has no GC and a key that has rendered corrupt

- **ID**: native_build_cache_scope_key_renders_corrupt_persistent_cache_2026-08-08
- **Status**: OPEN
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
