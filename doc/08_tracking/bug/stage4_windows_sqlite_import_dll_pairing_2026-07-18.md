# Stage4 Windows SQLite import-library/DLL pairing

## Problem

Strict Windows Stage4 links `sqlite3.lib` through the configured linker search
path, but runtime neighbor discovery can independently select `sqlite3.dll`
from `SIMPLE_SQLITE3_DLL` or `PATH`. A successful link therefore does not prove
that the staged DLL matches the import library's architecture and export ABI.

## Reproduction

1. Put `sqlite3.lib` from one Windows SQLite build on `LIB`.
2. Point `SIMPLE_SQLITE3_DLL` at a different architecture or incompatible
   SQLite build.
3. Run the strict Windows full-CLI Stage4 path.
4. The link can succeed, while process loading fails against the staged DLL.

## Required fix

- Resolve the import library and DLL as one explicit pair.
- Validate the DLL PE machine against the selected target.
- Validate the required SQLite named exports before staging.
- Include both file identities in the Stage4 link-profile receipt/cache input.
- Add a focused mismatch test and a native Windows launch receipt.

The current vcpkg CI lane supplies both files from the same x64-windows
installation, but that environmental pairing is not sufficient for arbitrary
override or `PATH` builds.
