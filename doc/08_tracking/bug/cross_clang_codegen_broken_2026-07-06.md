# Cross clang-20 aborts (SIGABRT) on all codegen

**Date:** 2026-07-06
**Area:** os/llvm_self_hosting, cross toolchain, SimpleOS Phase 4 (clang_static)
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

**Re-verification (2026-08-10):** The referenced binary
`build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang-20` does not exist in
this working copy — it is a build artifact (not source-controlled) produced
by a full LLVM cross-toolchain build (see `scripts/os/build_simpleos_llvm_image.shs`
and `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md`). Confirming
or fixing the SIGABRT requires rebuilding that LLVM cross toolchain with
assertions enabled (a bootstrap-scale LLVM build), which is out of scope for
a routine verification pass (no bootstrap-scale rebuilds). No source-level fix
is available without that rebuild + backend bisection. Left honestly open per
the doc's own "Next Check" section; the host-clang workaround remains the
only unblocked path for Phase 4 codegen.

## Symptom

The prebuilt cross clang shipped for SimpleOS,
`build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang-20`, exits 134
(SIGABRT, no diagnostic) on ALL C++ codegen and on C at `-O1` and above.
The front-end is healthy: `-fsyntax-only` always passes, and C at `-O0`
is the only configuration that emits an object.

Behavior matrix (same input, same cross clang):

| Input           | Flags            | Result            |
|-----------------|------------------|-------------------|
| C / C++         | `-fsyntax-only`  | PASS (exit 0)     |
| C               | `-O0 -c`         | PASS, emits `.o`  |
| C               | `-O1`/`-O2` `-c` | ABORT (exit 134)  |
| C++ (any)       | `-O0..-O3 -c`    | ABORT (exit 134)  |

No compiler diagnostic is printed before the abort; the process dies with
SIGABRT after front-end work completes, pointing at a codegen/backend crash
inside this particular cross build rather than a source problem.

## Minimal repro

```bash
CC=build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang-20

# Front-end fine:
printf 'int main(){return 0;}\n' > /tmp/t.c
$CC -fsyntax-only /tmp/t.c            # exit 0

# C at -O0 fine:
$CC -O0 -c /tmp/t.c -o /tmp/t.o       # exit 0, emits object

# C at -O1 aborts:
$CC -O1 -c /tmp/t.c -o /tmp/t.o       # exit 134 (SIGABRT), no diagnostic

# C++ aborts at any -O:
printf 'int main(){return 0;}\n' > /tmp/t.cpp
$CC -O0 -c /tmp/t.cpp -o /tmp/t.o     # exit 134 (SIGABRT), no diagnostic
```

## Impact

Blocks SimpleOS Phase 4 (`clang_static`, a guest-native clang that builds
and runs C/C++ on the SimpleOS filesystem) from using this cross clang for
any real codegen. C++ is the standard-library and exception path (already
provisioned in Phase 3), so a codegen-only-at-`-O0`-C toolchain is not
usable for self-hosting.

## Workaround

Use the HOST `clang-20` with `--target=x86_64-unknown-simpleos` (plus the
Phase 3 sysroot and final-link flags `--eh-frame-hdr
--no-dependent-libraries --allow-multiple-definition`) for any codegen.
The cross clang remains usable only for `-fsyntax-only` front-end checks.

## Next Check

Rebuild the cross clang with assertions enabled to capture the failing
backend assertion, or bisect the LLVM backend/target config for the
`x86_64-unknown-simpleos` triple that diverges from the host build. Until
then, all Phase 4 codegen must route through host clang.

## Lane J re-verification 2026-08-17 (classified by CONTENT, not SHA ancestry)

**Verdict: STILL-OPEN (ARCHITECTURAL).** Re-verified 2026-08-10 per the doc; a documented -O0
workaround exists so this is not a blocker. Out of scope for this lane (toolchain-level, and
`scripts/os/build_simpleos_llvm_image.shs` requires a cross clang-20 run that would contend
with the live bootstrap).
