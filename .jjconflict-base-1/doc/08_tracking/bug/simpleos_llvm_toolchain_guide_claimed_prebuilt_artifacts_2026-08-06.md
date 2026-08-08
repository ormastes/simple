# BUG: `simpleos_llvm_toolchain.md` claimed prebuilt cross-toolchain artifacts that do not exist

- **ID:** simpleos_llvm_toolchain_guide_claimed_prebuilt_artifacts_2026-08-06
- **Date:** 2026-08-06
- **Severity:** MEDIUM (documentation truth; wastes agent/human time and can
  produce false "toolchain ready" claims downstream)
- **Component:** `doc/07_guide/os/simpleos_llvm_toolchain.md`
- **Plan defect id:** D4 in
  `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md` §0 — fixed by
  Lane C2
- **Status:** **FIXED** — see *Fix* and the caveat under *What FIXED means*

## Symptom

The guide's opening paragraph asserted the toolchain was **"already built, just
not on the `PATH`"**, its §Locations table described
`build/os/llvm/cross-x86_64-unknown-simpleos/bin/` as holding a 131 MB `clang-20`
plus `ld.lld`/`lld`/`llvm-nm` in a ~954 MB tree, claimed an aarch64 cross variant
with "same layout", carried a section titled **"Build + link hello world
(verified)"** ending in "**Compile and link work today**", and said the guest
candidate "**now exists** at `build/os/clang_static/bin/clang_static`".

None of those artifacts are on disk. A reader following the guide gets
`No such file or directory` on the very first command.

## Evidence (commands run 2026-08-06, repo root `/home/ormastes/dev/pub/simple`)

```
$ ls -la build/os/llvm/cross-x86_64-unknown-simpleos/
CMakeCache.txt  CMakeFiles/  CPackConfig.cmake  CPackSourceConfig.cmake
# -> no bin/, no build.ninja

$ find build/os/llvm -maxdepth 3 -name build.ninja -o -maxdepth 3 -name bin
build/os/llvm/host-tools/bin
build/os/llvm/host-tools/build.ninja
# -> ONLY host-tools; nothing under cross-*

$ ls build/os/llvm/cross-aarch64-unknown-simpleos
ls: cannot access 'build/os/llvm/cross-aarch64-unknown-simpleos': No such file or directory

$ ls -la build/os/clang_static/
ls: cannot access 'build/os/clang_static/': No such file or directory

$ ls -la build/os/.bake_include_toolchain
ls: cannot access 'build/os/.bake_include_toolchain': No such file or directory

$ ls build/os/llvm/host-tools/bin
clang-tblgen  llvm-lit  llvm-min-tblgen  llvm-tblgen
# -> stage 1 IS built (4 tools, no clang)

$ ls build/os/llvm/host-tools/bin/clang-20
ls: cannot access '.../clang-20': No such file or directory

$ ls build/os/sysroot/lib build/os/sysroot/share/simpleos
lib:   crt0.o libc++.a libm.a libsimpleos_c.a libsimple_runtime.a
       libsimple_runtime_compat.a simple_entry.o
share/simpleos: simpleos.ld target-triple.txt
# -> sysroot IS present and correctly described; NOT part of this defect

$ git -C /home/ormastes/llvm-project log -1 --format='%H %d'
59612206386553df81efc06ec0421acf646d49ef  (HEAD -> simpleos)
$ git -C /home/ormastes/llvm-project remote -v
origin  https://github.com/ormastes/llvm-project.git (fetch)

$ grep -n 'LLVM_REVISION' src/os/port/llvm/build.spl
71:val LLVM_REVISION = "59612206386553df81efc06ec0421acf646d49ef"
```

Actual three-stage status: **stage 1 `host-tools` PRESENT**, **stage 2 `cross`
NOT BUILT** (x86_64 configured-only, aarch64 not even configured), **stage 3
`compiler-rt` not staged**.

## Root cause

The guide recorded a past build environment and was never re-checked against the
filesystem after `build/` was cleaned. Nothing regenerates or validates it, so a
stale "already built" claim survived indefinitely and read as current status.

## Fix (Lane C2)

`doc/07_guide/os/simpleos_llvm_toolchain.md` edited to state true current status:

1. Above-the-fold **Build status** block with the measured per-stage table and the
   build command `LLVM_SRC=/home/ormastes/llvm-project sh src/os/port/llvm/build.shs`
   (stages `host-tools` / `cross` / `compiler-rt`; outputs
   `build/os/llvm/cross-<triple>/`, and `build/os/clang_static/` for the
   deprecated static lane).
2. §Locations rows re-stated as PRESENT / NOT BUILT / ABSENT per the evidence
   above; size figures kept but reframed as *expected output once built*. Sysroot
   and host-tools rows kept as PRESENT — the fix does not overstate in the other
   direction either.
3. New **LLVM source fork** section: `github.com/ormastes/llvm-project` branch
   `simpleos`, checkout `/home/ormastes/llvm-project` at `596122063`, and
   `build.spl:71` pinning `LLVM_REVISION` to that same sha (pin == fork tip
   today). Notes that `build.shs` uses `$LLVM_SRC` and does not itself enforce
   the pin.
4. The in-guest `-cc1` ladder section relabelled **HISTORICAL, COMMIT-PINNED** at
   `7cf0b6aec3a` (`scripts/os/scp_retrieve_over_ssh_uefi.shs`), explicitly noting
   its artifacts are absent today and that re-proof is Lane C3.
5. "Build + link hello world (verified)" retitled **NOT currently reproducible**;
   commands kept verbatim, "Compile and link work today" removed, and the block
   explicitly *dissociated* from `7cf0b6aec3a` (that commit proves the in-guest
   `-cc1` ladder, not this host-side sequence). Sample `llvm-nm` addresses flagged
   as an obsolete `0x10000000` link base vs the current `0x40000000`.
6. `clang_static` "now exists" → past tense + "absent today"; the
   `clang_static` + `.bake_include_toolchain` gate requirement annotated as both
   absent; and the adjacent "Embedded LLD **now** builds … zero undefined
   symbols" qualified as last-recorded-build, not reproducible today (it
   otherwise contradicted the ABSENT marking two lines above).
7. **Same defect class, also found and fixed in this file:** the Simple-native
   table row claimed `bin/release/<arch>-unknown-simpleos/simple` (~4 MB static
   EXEC per arch). Verified absent — `bin/release/x86_64-unknown-simpleos/` and
   `bin/release/riscv64-unknown-simpleos/` exist but are **empty**, and there is
   no `aarch64-unknown-simpleos` dir. Row now states this, with
   `bin/simple build simpleos` as the rebuild command and the 2026-07-14
   boot-proof marked historical. (This matches the plan §0 row
   "`bin/release/{x86_64,riscv64}-unknown-simpleos/` EMPTY".)

No build instructions were deleted — only their status framing corrected.

## What FIXED means here

FIXED = **the document now matches the filesystem**. It does **not** mean the
cross toolchain exists. Building it is Lane C1; re-proving the `-cc1` ladder is
Lane C3.

## Related stale record (not fixed here, out of C2 scope)

`doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md` §0 ground-truth
table still says `Fork pin | LLVM_REVISION=3b33ba807 — 2 commits behind fork tip
92fa40246`. Primary sources contradict it: `build.spl:71` and the checkout's HEAD
are both `59612206386553df81efc06ec0421acf646d49ef`, i.e. **pin == fork tip**.
That row should be refreshed by whoever owns the plan.

## Prevention

A `--status` style check that compares the guide's asserted artifact paths against
the filesystem (or moving the artifact table into generated output from
`src/os/port/deploy_toolchains.spl --status`) would keep this from recurring.
