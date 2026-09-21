# Windows C compiler authority lint

The Windows toolchain lint admits C compiler selections only when the source
binds them to an official LLVM 23.1.x Windows MSVC distribution and validates
the output of that selected compiler with a fail closed version check.

## Symbol binding

- Normalize shell and PowerShell variable references before comparing names.
  `$name`, `${name}`, and `name` identify the same symbol.
- A target specific `CC_x86_64_pc_windows_msvc` assignment may refer through
  `CC` to the already validated root bound `clang-cl.exe` driver.
- Derived values are version evidence only when the assignment transforms the
  queried compiler output. Diagnostic, metadata, log, and attestation strings
  that merely mention the output are not version evidence.
- A PowerShell join is admitted only when its complete right hand side is the
  queried symbol joined with a newline literal. Interpolation, concatenation,
  array construction, or a fabricated prefix is rejected.

## Assignment classification

Classify plain, exported, batch, PowerShell, YAML, and `GITHUB_ENV` compiler
assignments consistently. Quoting the target specific variable name does not
change its meaning. `CC` and `CC_x86_64_pc_windows_msvc` must select admitted
LLVM 23.1.x `clang-cl.exe`; every CXX target assignment and every selection of
`cl`, GCC, G++, MinGW, or a C++ driver is rejected.

## Version family

The version predicate must require the literal family `23.1.` followed by one
or more decimal digits and a token boundary. A wildcard in place of either
literal dot, a pattern without the family boundary, or an additional regex
alternative outside the admitted boundary is rejected.
The exact regex must be the active predicate operand. A matching pattern in a
throw message or diagnostic does not validate a weaker predicate. CMake quoted
escape decoding is handled separately from PowerShell single quoted regexes.

## Falsifiable fixtures

The canonical unit spec retains the production shell as a positive fixture and
contains independent negative fixtures for diagnostic-only derivation, a
quoted target `GITHUB_ENV` export, wildcard family dots, and a missing family
boundary. It also rejects fabricated array joins and extra family alternatives.
A change is acceptable only when every negative produces a lint finding and
the production source produces none.
