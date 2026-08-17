# Tier-less `use std.X` picked a tier by raw readdir order

- **ID:** tierless_std_import_readdir_order_2026-08-17
- **Severity:** P1 (silent wrong-symbol selection, not reproducible across machines)
- **Status:** MITIGATED 2026-08-17 (selection made deterministic; still not an error)
- **File:** `src/compiler/99.loader/module_resolver/resolution.spl`
- **Supersedes the open half of:**
  `tierless_std_import_ambiguity_resolves_by_registration_order_2026-07-29.md`

## Correction to the earlier record

The 2026-07-29 record describes the selection as being made by "registration
order". That understates it. The tier-less `use std.<path>` fallback searches
`src/lib/*/` with

```
val subdirs = self.cached_dir_list(lib_dir)
for subdir in subdirs:
```

and returns the **first** tier that resolves. `cached_dir_list` is a thin cache
over `rt_dir_list`, i.e. raw `readdir` order. So the winning tier was decided by
the filesystem, not by any order the compiler controls, and it is not stable
across machines, filesystems, or fresh checkouts. The same source could bind a
different module on a different box, silently.

The prior lane added `maybe_warn_tier_ambiguity`, a **non-fatal** warning that
by its own comment "never alters resolution". The wrong-selection defect was
therefore live and untouched.

## Fix

Search in a fixed precedence instead of listing order:

```
val TIER_PRECEDENCE: [text] = [
    "common", "nogc_async_mut_noalloc", "nogc_sync_mut",
    "nogc_async_mut", "gc_async_mut",
]
```

Least-capability-first: `common` is pure and cannot pull a runtime family in,
so it is tried first; the rest ascend in capability. `tier_ordered_subdirs` is
a pure **permutation** of the listing — every entry appears exactly once, and
non-tier directories keep their relative order but sort after every canonical
tier, so an unrelated directory dropped into `src/lib/` can never pre-empt a
real tier.

This cannot change the outcome for any path that exists in exactly one tier,
which is the overwhelming majority. It only makes the ambiguous case
reproducible.

## Deliberately NOT done

Making tier ambiguity a hard error. The prior record notes 1611 call sites in
the AMBIG bucket, and these files are in a live bootstrap's compile path;
turning this fatal is a separate, scheduled change. The honest status is that
an ambiguous tier-less import is now *deterministically* resolved and warned
about, not *rejected*.

## Evidence

Spec: `test/01_unit/compiler/module_resolver/tierless_std_import_order_spec.spl`
(4 reproducer examples pinning precedence and permutation-independence,
7 detection examples pinning the permutation property — totality, non-tier
retention, non-tier ordering, empty input, and full five-tier ordering).

The detection half exists because a fix that merely sorted alphabetically, or
that filtered the listing down to known tiers, would satisfy the reproducer
and be wrong.

**THE SPEC HAS NEVER PRODUCED A VERDICT. Do not treat this fix as verified.**
Three runs were started; all three were **killed (exit 144)** before reaching
their `Results:` line, on a box under a live 16-job bootstrap at load 120-185.
This is a kill, not a slow run — re-running it is the outstanding action:

```
bin/simple test test/01_unit/compiler/module_resolver/tierless_std_import_order_spec.spl --timeout 1200
```

Note for whoever picks this up: an `OK` from `check-test-verdict-not-silent.shs`
does not settle it either. Only a `Results: N total, N passed` line does.

## Not proven

- No end-to-end test demonstrates a real `use std.X` binding the wrong module
  before the fix; constructing one requires two same-named modules in two
  tiers, which the repo does not currently ship in a way a spec can import
  hermetically. The unit-level property is what is pinned.
- The chosen precedence is a design decision, not a derived one. If a tier
  ordering is later specified normatively, `TIER_PRECEDENCE` is the one place
  to change.
