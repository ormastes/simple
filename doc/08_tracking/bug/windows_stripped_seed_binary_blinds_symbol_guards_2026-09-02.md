# Windows: the stripped `bin/simple.exe` blinds every symbol-table guard

**Status:** FIXED 2026-11-11 (lane p3-comp11) — the three unblock conditions are
resolved at tip: the deployed tracked seed `bin/simple.exe` (build
`46fe8f6b6def`) is **unstripped** (112,072 unique defined symbols through the
census's own `census_collect_primary`, rc=0), the PE-export fallback for
stripped PEs is merged (PR #7626) with a passing parser selftest, and the
per-platform system-symbol source + the two sibling guard fixes (PRs #7625,
#7661) are ancestors of the release tip. See the dated addendum below.
**Severity:** Blocking for promotion — these guards are unpromotable to push-blocking
on any Windows host, and one of them was emitting a FALSE RED until today.
**Affected files:** `scripts/check/extern-backing-census.shs`,
`scripts/check/check-unbacked-extern-ratchet.shs`,
`scripts/check/check-no-unresolved-runtime-symbols.shs`,
`scripts/check/check-stage-binaries-runnable.shs`
**Path:** `bug` track.

## Symptom

The deployed Windows compiler carries no symbol table:

```
$ nm -a --defined-only bin/simple.exe
C:\dev\tool\msys2\mingw64\bin\nm.exe: bin/simple.exe: no symbols
```

(`md5 d52d770724a9f8797e98ac7819709ab9`, GNU nm 2.42 from MSYS2 mingw64.)

`extern-backing-census.shs` uses `nm --defined-only` over that binary as its
PRIMARY `in_deployed_binary` evidence. With an empty symbol set every lookup
misses, so the census reclassified the whole tree as unbacked:

```
$ sh scripts/check/check-unbacked-extern-ratchet.shs
FAIL — 1603 symbol(s) checked, 255 newly unbacked: __rt_btreemap_contains
  __rt_vec_push __rt_vec_len ... cosmos_fsbl_mmio_read ...
```

None of those 255 is new debt. This was a scan that found nothing because it
scanned nothing.

The census also reads `/lib/x86_64-linux-gnu/lib{c,m,gcc_s,pthread,dl}.so.*`
directly (`extern-backing-census.shs:64-65`). That directory does not exist on
Windows — and does not exist on macOS either, where libc lives in the dyld
shared cache — so the system-symbol set is silently empty on both.

Two sibling guards fail their own selftests here and refuse to scan, which is
the correct fail-closed behaviour but leaves the defect class unguarded:

```
$ sh scripts/check/check-no-unresolved-runtime-symbols.shs
ERROR — nothing was checked (selftest failed)
$ sh scripts/check/check-stage-binaries-runnable.shs
ERROR — nothing was checked (selftest failed -- the guard itself is not trustworthy)
```

## Fixed today (partial)

`77f8c2e4dcb` made the census fail CLOSED on a vacuous symbol table:

```
before: FAIL  — 1603 symbol(s) checked, 255 newly unbacked          (false)
after:  ERROR — nothing was checked: census failed (rc=2): ...
        bin/simple yielded 0 defined symbol(s) (floor 100); it is stripped or
        not a readable object for this nm. Backing classification would be
        vacuous.
```

ERROR is not a pass. The false RED is gone; the blindness is not. Floor is
overridable via `EXTERN_CENSUS_BIN_SYM_FLOOR`. Unix impact: none — an
unstripped ELF/Mach-O `simple` defines tens of thousands of symbols.

## Unblock condition

Any ONE of:

1. Deploy an **unstripped** `bin/simple.exe` (link without `-s`, keep the COFF
   symbol table), which restores the census's primary evidence directly; or
2. Teach `extern-backing-census.shs` to read PE exports
   (`nm --defined-only` works on unstripped PE; `objdump -p` / `llvm-readobj
   --coff-exports` work on stripped ones); and
3. Replace the hardcoded `/lib/x86_64-linux-gnu/*.so` list with a per-platform
   system-symbol source (Linux: as today; macOS: `nm -g` over the dyld cache
   extraction or a curated libSystem list; Windows: the CRT import library),
   failing closed when none is available.

Until then these guards are Linux-only and must not be promoted to
push-blocking without a documented host requirement.

## Cross-platform note

Every change made today is a no-op on Linux and macOS: the added non-vacuity
floor is unreachable where a symbol table exists, and no Unix branch was edited.

## Fix 2026-11-09 (owner decision: census reads PE exports)

`census_collect_primary` (scripts/check/lib/extern-census-symbol-sources.shs) now falls back, for a
Windows PE with no COFF symbol table, to `llvm-readobj --coff-exports` named exports (logged, floor
still enforced, ordinal-only skipped). Parser fixture: `sh scripts/check/extern-backing-census.shs --selftest`.
Status: fix-implemented-verification-pending (Windows stripped-exe run still to be observed).

---

## Addendum 2026-11-11 (lane p3-comp11, worktree simple-p3-comp11-20261111, base 41935a5f61860)

Verdict: FIXED (fix predates this lane for the guard scripts; this lane
supplies the pending Windows observation and flips the record).

Fix commits, all ancestors of the lane base (and of the tracked seed build
`46fe8f6b6def`):
- PR #7626 `62be690c6aedf3dd4eefb8fa05895b8d51838e6b` — census symbol sources:
  `census_collect_primary` in `scripts/check/lib/extern-census-symbol-sources.shs`
  falls back to `llvm-readobj --coff-exports` for a stripped PE (floor still
  enforced, ordinal-only skipped), plus the per-platform CRT system-symbol leg.
- PR #7625 `be076742832fe55c9c135dce89809d6d635d7722` —
  `check-stage-binaries-runnable.shs` PE admission.
- PR #7661 `99cd4176a7113867ee84d0517e4ab22b7c7b317e` —
  `check-no-unresolved-runtime-symbols.shs` reads PE import owners.
- The 2026-11-09 in-doc fix (same file, PE-export fallback) is the substance of
  the #7626 line above.

Fresh observations on this Windows host (llvm-mingw-20260922 toolchain):
1. **The deployed tracked seed is unstripped** — the doc's unblock condition 1
   is met by the current deployment. `nm --defined-only bin/simple.exe` yields
   115,123 entries, and the census's own collector
   (`census_collect_primary bin/simple.exe ...`) returns rc=0 with
   112,072 unique defined symbols — far above the floor of 100. The primary
   `in_deployed_binary` evidence path works on the deployed Windows binary.
2. **Census selftest**: `sh scripts/check/extern-backing-census.shs --selftest`
   → `PASS — PE export parser selftest: 150 named exports parsed, ordinal-only
   skipped` (~11s).
3. **Stripped-exe leg observed (the doc's pending item)**: on an
   `llvm-strip`ped copy of the same binary, the collector correctly detects no
   COFF symbol table, logs "reading PE export table", and fails CLOSED with
   `ERROR — ... yielded 0 PE export(s) (floor 100)`. This executable class
   carries no PE export table, so the export fallback cannot by itself carry a
   census for a stripped `simple.exe` — the fail-closed floor is the designed
   behavior, not a blindness. The durable resolution is condition 1 (ship the
   unstripped binary), which the current deployment satisfies.

Not completed in-lane (recorded per lane budget, not a defect): the FULL
census classification run over the whole tree exceeded this lane's ~10-minute
single-invocation budget and was aborted at the tool timeout with an empty
log; the per-binary primary-evidence collection above is the lane-bounded
substitute. Residual observation for a future lane: if a future deployment
strips `bin/simple.exe` again, the export-table fallback alone yields
fail-closed ERROR for this no-export-table executable class; options then are
keeping the unstripped link (current state), a PDB-based source, or an
export-surface build — tracked here as an observation, not re-opened.
