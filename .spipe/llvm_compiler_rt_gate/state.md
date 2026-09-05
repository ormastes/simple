# Lane LLVMGATE — compiler-rt `-simpleos` triple gate

Status: COMPLETE (uncommitted — lane instructed not to commit)
Owner: lane LLVMGATE
Date: 2026-07-28

## 1. The dead assertion

Lane FSDICT restored 35 assertions in the LLVM/rustc port specs that had never
been asserting. One newly-live assertion failed for a genuine reason:

    it "gates compiler-rt behind -simpleos triples":
        check(src.contains("ends_with(\"-simpleos\")"))

Present in BOTH spec trees:
- `test/integration/os/port/llvm/per_target_build_spec.spl:82`
- `test/02_integration/os/port/llvm/per_target_build_spec.spl:157`

`src/os/port/llvm/build.spl` contained **no `ends_with` at all**. compiler-rt
was not gated by triple. The spec encoded a safety property the implementation
never had; the dead assertion hid it.

## 2. Intent reconstructed — what the gate protects against

`build.spl` builds compiler-rt in a **freestanding / baremetal** configuration
that is only correct for SimpleOS:

- legacy path `build_compiler_rt(config: BuildConfig)` (line ~173) passes
  `-DCOMPILER_RT_BAREMETAL_BUILD=ON`,
  `-DCMAKE_C_FLAGS=--target=<triple> -ffreestanding -nostdlib`, then
  `ninja install` into `config.install_prefix`
  (default `/opt/simpleos-toolchain`, overridable with `--prefix`).
- cross path `build_compiler_rt_for_target(triple)` runs `build.shs` stage
  `compiler-rt` and then stages `libclang_rt.builtins*.a` into the clang
  resource dir `build/os/sysroot/lib/clang/<ver>/lib/<triple>/`.

Harm if a non-SimpleOS triple reaches either path:

1. **Host-toolchain poisoning.** The legacy path's `--target` accepted *any*
   value with zero validation (`parse_args`, line ~63). `--target
   x86_64-unknown-linux-gnu --prefix /usr/local` would `ninja install` a
   `-nostdlib -ffreestanding` baremetal builtins archive over a real host
   toolchain's compiler-rt. That library is wrong for a hosted target
   (no libc assumptions, baremetal ABI), and it silently replaces a working one.
2. **Wrong resource-dir population.** The cross path stages builtins under
   `lib/clang/20/lib/<triple>` — a directory name the clang driver keys on.
   Populating a host triple's slot with SimpleOS baremetal builtins mislinks
   every subsequent host compile that resolves that resource dir.
3. **Unbounded triples via env.** `cross_selected_targets()` honours the
   `SIMPLE_TARGET` env override and `--target` / `--targets` CSV with no
   filtering at all — arbitrary strings become triples.
4. **Panic instead of refusal.** `cross_llvm_arch_for` `panic()`s on an
   unrecognised arch, so a stray triple crashes the plan printer rather than
   being cleanly rejected.

Existing partial protection: `cross_target_supported()` exact-matches an
allowlist and is consulted by `cross_build_stage_for_target`. It is an
allowlist of five triples, not a triple-shape gate, and it does not cover the
legacy path at all. Both SimpleOS triple spellings in this file
(`x86_64-simpleos` and `x86_64-unknown-simpleos`) end in `-simpleos`, so the
suffix is the correct invariant.

**Gate property:** compiler-rt is built/installed only for triples ending in
`-simpleos`. Fail-closed: an unrecognised or arbitrary triple is refused, never
silently granted compiler-rt.

## 3. Implementation

All in `src/os/port/llvm/build.spl` (no spec edits — both spec trees assert
against this one shared source file, so one change satisfies both).

One predicate, four enforcement points:

    fn is_simpleos_triple(triple: text) -> bool:
        triple.ends_with("-simpleos")

| # | Site | Behaviour on non-SimpleOS triple |
|---|------|----------------------------------|
| 1 | `build_llvm` (guarded by `config.build_compiler_rt`) | `panic` before hours of LLVM work; message points at the existing `--no-compiler-rt` flag |
| 2 | `build_compiler_rt(config)` — legacy path, ends in `ninja install` into the prefix | `panic` at the point of harm |
| 3 | `cross_target_supported(triple)` — shape check runs *before* the allowlist | `return false` |
| 4 | `build_compiler_rt_for_target(triple)` — stages into `lib/clang/<ver>/lib/<triple>/` | prints refusal, `return false` |

Site 3 is placed before the allowlist loop deliberately: it also shields
`cross_llvm_arch_for`, which `panic()`s on an unrecognised arch, so a stray
`SIMPLE_TARGET` value is now cleanly refused instead of crashing the plan
printer.

**Fail-closed and non-regressive.** The gate is a strict narrowing — it can only
turn `true` into `false`, never the reverse. All five `CROSS_SUPPORTED_TARGETS`
entries end in `-simpleos`, so nothing previously accepted is now rejected.

## 4. Verdicts

Source-text-guard traps both checked and clear:
- **Non-vacuity:** all four asserted source paths (`build.spl`, `build.shs`,
  `compiler_rt_cmake.cmake`, toolchain `README.md`) exist on disk, so no
  `read_file`-returns-empty vacuous pass.
- **Interpolation:** the `{...}` literals are already escaped as
  `cross-{{triple}}` / `compiler-rt-{{triple}}`; the new assertion's string
  contains no braces.

Spec verdicts (`bin/simple run`, example counts confirmed non-zero):

| Spec | Tree | Before | After |
|------|------|--------|-------|
| `per_target_build_spec` | `test/integration` | 21 examples / **1 failure** | **21 / 0** |
| `per_target_build_spec` | `test/02_integration` | (twin, same assertion at :157) | **60 / 0** |
| `cross_build_plan_spec` | `test/integration` | 14 / 0 | **14 / 0** |
| `cross_build_plan_spec` | `test/02_integration` | — | **21 / 0** |

The single remaining failure was indeed this one, and it is now green with the
other 20 untouched.

Behavioural check (beyond the source-text guards) — predicate and
`cross_target_supported` exercised directly:

    x86_64-unknown-simpleos   is_simpleos=true   supported=true
    x86_64-simpleos           is_simpleos=true   supported=false  (allowlist spelling, pre-existing)
    x86_64-unknown-linux-gnu  is_simpleos=false  supported=false
    aarch64-apple-darwin      is_simpleos=false  supported=false
    "" / bogus                is_simpleos=false  supported=false
    -simpleos-x86_64          is_simpleos=false  supported=false  (suffix, not substring)

## 5. Follow-up (not in scope of this lane)

`x86_64-simpleos` and `riscv32imac-simpleos` — the spellings used in
`SUPPORTED_TARGETS` and in this file's own usage docstring — are **not** in
`CROSS_SUPPORTED_TARGETS`, which uses only `-unknown-simpleos` forms. Two
triple vocabularies coexist in one file. Pre-existing, untouched by this lane
and not a gate defect, but worth reconciling.
