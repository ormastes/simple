# Stage4 Windows C ABI inference used the object suffix

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
