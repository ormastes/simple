# Naming a provider DELETES an unbacked rt_* group instead of owning it

- **Filed:** 2026-09-06
- **Component:** `scripts/check/gen-api-registry.shs`, `scripts/check/check-rt-api-groups.shs`
- **Severity:** the grouping gate's unowned count can fall for the wrong reason

## Symptom

Adding `src/os/installer/staged_root_tree_retained_provider_v1.spl` to
`scripts/check/no_direct_rt_allowlist.txt` — the correct owner for the `staged`
group under the policy's mechanical criterion — did not mark the group owned.
It removed the group from `config/api/api_registry.sdn` entirely. The
`api_groups` row `rt, staged, 8, 9, "-", unowned` disappeared, all eight
`rt_staged_tree_provider_*_v1` symbol rows disappeared, and the unowned group
count fell by one.

## Mechanism

`gen-api-registry.shs` builds its symbol universe as

```
{ cut -f1 lanes.tsv; grep -v '^#' sites.tsv | cut -f1;
  cat ctext.txt rtext.txt; } | sort -u > all.txt
```

`sites.tsv` is the **forbidden** call-site census — allowlisted calls are
routed to `prov.tsv` instead and `prov.tsv` is used ONLY to derive the
`provider` column, never to populate the universe. `ctext.txt`/`rtext.txt` are
C and Rust *definition* lines.

So a symbol survives allowlisting only if it also has a C or Rust definition
line. `rt_port_*` and `rt_dma_*` do (`runtime_port_io.c`, `dma_<arch>.c`), which
is why owning those two groups worked. `rt_staged_tree_provider_*_v1` are
unbacked externs with no definition line anywhere, so allowlisting their sole
caller removed their last trace from the universe.

`check-rt-api-groups.shs` has the same universe (`scan`, `defs.txt`), so the
gate cannot see the deletion either.

## Fix

Fold the provider census into the universe in both files:

* `gen-api-registry.shs`: add `grep -v '^#' "$WORK/prov.tsv" | cut -f1;` to the
  `all.txt` join.
* `check-rt-api-groups.shs`: request `--provider-out` and append its first
  column to `defs.txt`. The census exits non-zero when a tree has **no**
  allowlisted provider call site at all (a legitimate fixture state), so that
  second pass must be tolerated while the fail-closed non-vacuity contract
  stays on the forbidden census.

## Why it is not fixed in this lane

Measured with both edits applied: the universe grows 4185 -> 4782 symbols and
180 -> 191 named groups, because 11 groups are reachable only through
allowlisted providers and were invisible before. The frozen, reviewed
`scripts/check/rt_api_group_baseline.txt` has no `budget` row for any of them
and its `ungrouped` set no longer describes the tree, so the gate goes from
5 to 10 over-budget groups and 0 to 13 stale baseline entries. Clearing that
requires `--generate-baseline`, which is a reviewed action reserved for the
gate owner. Shipping the widening without it would leave the gate strictly
redder, so this lane reverted it and filed this instead.

`staged` therefore stays `unowned` even though it meets the ownership
criterion. That is the concrete cost of the defect.

## Second instance, observed in the same pass: `rt_dma_bytes_to_array`

Owning the `dma` group had the same side effect on one symbol.
`rt_dma_bytes_to_array` is a real extern with no text-greppable C definition
line, and its only two call sites moved into the now-allowlisted owner
`src/lib/nogc_sync_mut/io/dma.spl`. It is therefore **absent from the
regenerated registry** (`grep -c rt_dma_bytes_to_array config/api/api_registry.sdn`
= 0). The `dma` group is reported as owned, which is true, but it is reported
with 9 symbols rather than 10, and the missing one is the one the migration
touched most recently. Same root cause, same fix.

## A separate census defect surfaced by the same measurement

`dma` dropped 17 -> 9 symbols. Only one of those eight is the erasure above.
The other seven were never APIs at all: the census regex
`rt_[a-z0-9_]*\(` matches Simple **function definitions** whose names begin
with `rt_`, and `src/lib/nogc_sync_mut/io/dma.spl` defines
`rt_dma_alloc__fallback`, `rt_dma_free__fallback`, ... as ordinary Simple
functions. They were being counted as rt_* API symbols and as direct call
sites. Allowlisting their file removed them, which happens to be the right
answer, but the classifier should not have admitted them in the first place —
a `__fallback` suffix on a Simple `fn` is not a runtime boundary.
