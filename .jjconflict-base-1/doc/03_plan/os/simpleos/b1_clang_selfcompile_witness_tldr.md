# B1 clang self-compile witness — TL;DR

Full doc: `b1_clang_selfcompile_witness.md`. Host-side prep only; no QEMU ran.

- **TU chosen:** `llvm/lib/Support/DivisionByConstantInfo.cpp` — real LLVM
  (Hacker's-Delight magic numbers over `APInt`), no I/O, and the smallest `.i`
  among the substantial candidates (17 candidates measured).
- **Staged input:** `build/os/b1_witness/TU1.I`, **1,164,308 B** (`-E -P`, zero
  host absolute paths). One file in the FAT32 root; nothing else to stage.
- **Self-contained: proven.** 0 `#include` left; compiles with
  `-nostdinc -nostdinc++ -nobuiltininc --sysroot=/nonexistent` and yields a
  **byte-identical** object to the full-flag build.
- **Reproducible: YES.** 6 independent runs (incl. `env -i`, different cwd,
  TMPDIR, HOME, output dir) → identical bytes. clang `-cc1` on a preprocessed TU
  is deterministic; the sibling lane's non-deterministic Simple-payload build
  does **not** generalise. B1's oracle is sound.
  Required flags: **`-fno-ident`** (kills the `.comment` version banner — the one
  guaranteed diff), `-fdebug-compilation-dir=/`, `-fcoverage-compilation-dir=/`,
  no `-g`. `-frandom-seed` not needed for this TU.
- **Reference object:** `TU1.O`, 10,616 B,
  sha256 `f71aa3f9545c908c3e0b3bc3eddf4d1b11bde443152e45a04207b8969252cfb4`,
  `readelf -h` → ET_REL / EM_X86_64 / ELF64 LE.
- **Guest file must be named `TU1.I`** — the `STT_FILE` symbol is the input
  basename.
- **Guest accepts the `-cc1` line: verified host-side.** All 21 cc1 options
  grep-confirmed present in `clang-20` itself, with positive (`emit-obj`) and
  negative (`zzz-not-an-option`) controls. No QEMU cycle will be burned on a
  missing flag.
- **Open risk R1:** host clang is Ubuntu 20.1.8, in-guest clang is the fork's
  20.0.0git. No host-runnable fork build exists. Narrowed by inspection: the
  fork's `SimpleOSTargetInfo` changes only preprocessor defines + wchar/wint
  types (**no** codegen defaults), and its ToolChain is driver-level so `-cc1`
  bypasses it — so R1 is plain upstream-revision skew and tier 1 is a reasonable
  expectation. Two-tier oracle in `compare_object.shs` (tier 1 = byte-exact;
  tier 2 = same `.text`/`.rodata`/relocs/symbols with the skew explained). A
  tier-2 pass must be reported as tier 2.
- **Acceptance is a positive marker**, never absence-of-failure: require
  `[oo-nvme] persist /TU1.O -> OK`, size 10,616 B + sha256, and the
  `compare_object.shs` verdict. Exit status alone is fail-open.
- **Retrieval hazard:** L5 `getfile` previously returned an empty object. A
  0-byte `TU1.O` is a transport failure, not a compile failure — check against
  10,616 B first.
