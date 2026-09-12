# Stage4 Windows C ABI inference used the object suffix

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Symptom

Stage4 classified every Windows `.obj` provider as COFF-MSVC and every `.o`
provider as COFF-MinGW. The suffix came from `SIMPLE_LINKER_FLAVOR`/`MSYSTEM`,
while C flags came from the independently selected `SIMPLE_CC` driver. Thus a
GCC override under the default MSVC environment was scanned as MSVC, and a
`cl.exe` override under MinGW was scanned as MinGW. `clang-cl` was also sent
GNU-style flags because its MSVC-compatible driver spelling was not recognized.

## Reproducer and prevention

The pure regression in
`test/01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl` covers
MSVC, clang-cl, ambiguous plain-clang rejection, MinGW GCC, prefixed MinGW GCC, incompatible
compiler/linker pairs, unknown wrappers, and non-Windows rejection. The runtime
compiler unit test covers mixed-case forward/backslash MSVC driver paths.

## Fix

The hosted C compiler is resolved once and reused for runtime and entry C
compilation. Stage4 classifies object ABI from the normalized driver identity,
rejects ambiguous plain clang plus contradictory/unknown Windows toolchains,
uses linker policy only for archive spelling, and passes object ABI, linker flavor,
and Windows path semantics separately to every provider builder. Ordinary
LLVM/Cranelift linking remains on the existing linker route.

An explicit `*-pc-windows-msvc` target is also rejected when the selected
compiler and linker resolve to MinGW, before any temporary object is compiled.

Runtime/native execution remains pending because this session was explicitly
restricted to static/source checks.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
