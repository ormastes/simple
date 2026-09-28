# Linux SIMD search blocks bootstrap with undeclared memmem

- Severity: P1 (Linux bootstrap C compilation blocker).
- Status: source fix verified by focused native checks; full Linux bootstrap pending.
- Observed on main `97020f7badf5a4fac26943bfad83bf6ae32222b1` and release/1.0
  `1606003a9d31bbad4e7a81b0f1e43e725cce30d4`.
- Environment: Ubuntu 22.04 on WSL2 x86_64, Clang 14.0.0 and GCC 11.4.0.

## Failure and cause

The prior Linux Stage2 run compiled 1,059 Simple source files before the C
runtime authority failed at `src/runtime/runtime_simd_search.c:52`:
`implicit declaration of function 'memmem' is invalid in C99`.
A standalone compile reproduced that error and the accompanying integer to
pointer conversion error from the implicit return type:

```sh
clang -std=c99 -Werror=implicit-function-declaration -Werror=int-conversion     -c src/runtime/runtime_simd_search.c -o /tmp/runtime_simd_search.o
```

`runtime_simd_dispatch.h` includes system headers and `<string.h>` before the
source selects GNU features. On glibc, the `memmem` prototype is guarded by GNU
feature selection. Selecting the GNU language dialect alone does not expose
this libc declaration. Allowing implicit declarations would also risk truncating
pointer return values; suppressing the diagnostic is not a repair.

## Fix

Define `_GNU_SOURCE` for Linux, only if it is not already defined, before
including the dispatch header. Keep the existing libc search algorithm and
platform dispatch. The main branch's Windows fallback is unchanged; the release
backport needs only the feature macro, without copying the Windows fallback.
There are no compiler, language, API, or search semantic changes.

## Focused verification

Run each compiler against the checked-in regression:

```sh
CC=clang sh scripts/check/check-runtime-simd-search-native.shs
CC=gcc sh scripts/check/check-runtime-simd-search-native.shs
```

Both passed strict C99 standalone runtime compilation without a command-line
`-D_GNU_SOURCE`, then passed 200 cases through both the scalar function and the
runtime-selected SIMD function. Cases cover empty buffers/needles, needle longer
than input, absent and single-byte matches, overlapping matches, binary zero and
high bytes, every valid offset across a 96-byte input, and truncated input lengths.
The harness includes the runtime source before any system headers to exercise
feature-macro ordering and access the otherwise private scalar fallback.

Evidence: `build/test/runtime_simd_search_native_check/{baseline,clang,gcc}.log`.
The baseline log contains the expected compiler errors; the two fixed logs each
contain `PASS: 200 scalar and selected SIMD search cases`.
`git diff --check`, working/staged direct-env runtime guards passed, and there
were zero executable `*_spec.spl` files in `doc/06_spec` before commit.

## Remaining acceptance

This resolves the isolated C declaration failure. It does not establish that
full Linux bootstrap succeeds: the prior session reached its three-cycle limit,
so no full bootstrap was retried for this change. Preserve the original bootstrap
checkout, cache, and logs for a separately authorized follow-up. macOS, Windows,
and non-x86 runtime execution are not claimed by this Linux-focused check.

## Release backport evidence

The backport is based on release/1.0
`1606003a9d31bbad4e7a81b0f1e43e725cce30d4`. Its runtime diff adds only the
six-line feature-macro block; no Windows fallback or unrelated runtime changes
were copied from main. The unmodified release source independently reproduced
the undeclared `memmem` failure. Clang 14 and GCC 11 both passed the release
source's strict C99 compile and all 200 scalar/selected SIMD cases. The same
three evidence logs are retained in the isolated release worktree. Both env
guards passed, and a tracked-tree scan found zero misplaced executable specs.
