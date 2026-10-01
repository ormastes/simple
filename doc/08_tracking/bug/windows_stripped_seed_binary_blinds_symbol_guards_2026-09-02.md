# Windows: the stripped `bin/simple.exe` blinds every symbol-table guard

**Status:** OPEN 2026-09-02 — three guards cannot produce a verdict on Windows.
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
