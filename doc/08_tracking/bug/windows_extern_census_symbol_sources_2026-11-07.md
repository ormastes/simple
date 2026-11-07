# Windows extern census: platform symbol-source acquisition

**Status:** verification pending; scoped host/provider repair with focused
native fixture checks passed. Full deployed-compiler census remains unverified. Parent
`windows_stripped_seed_binary_blinds_symbol_guards_2026-09-02` remains OPEN.

At source base `0dd1df0250ae3dba932654653cba0748a188b563`, the census selected a
Linux deployment path and silently collected no system-provider symbols on
Windows: every `/lib/x86_64-linux-gnu/*.so` candidate was absent. Its primary
`nm | awk | sort` pipeline also discarded the producer's failure status.

The repair selects a Windows `.exe` deployment (or explicit `SIMPLE_BIN`),
checks the actual symbol-reader exit status, and requires a nonempty COFF
symbol table before applying the existing minimum of 100 defined symbols.
`EXTERN_CENSUS_NM` and `EXTERN_CENSUS_READOBJ` select compatible tools without
changing global PATH. A floor below 100 cannot disable the non-vacuity guard.

Windows system-provider evidence comes from the named exports of the actual
`SystemRoot/System32/ucrtbase.dll`, optionally selected explicitly with
`EXTERN_CENSUS_WINDOWS_CRT`. Missing/unreadable/non-DLL/empty provider evidence
stops classification. Its separate `windows_crt_export` tier establishes only
that the inspected CRT advertises a name. It does not prove this compiler's
imports, ABI compatibility, resolution of all forwarders, or successful use of
every exported function. Linux provider collection retains its existing scope;
Darwin and other Unix provider discovery remain separate work.

The parent report's historical suggestion to substitute PE exports for the
primary executable census is insufficient: exports omit internal definitions.
No such fallback is implemented. A stripped deployment still needs an immutable
matching unstripped/symbol companion artifact, or an unstripped executable,
before a complete primary census is possible. This slice does not implement
that artifact pipeline or repair the separate unresolved-symbol guard.

## Executed focused evidence

On native Windows x64, LLVM 23.1.1 built three private C fixtures and all three
executables returned zero. No Simple compiler or Rust seed was executed.

- Unstripped fixture: 152 COFF symbols, including a private definition; admitted.
- Stripped copy: zero COFF symbols but 150 named PE exports; rejected.
- CRT fixture: `malloc` and `free` linked with Windows SDK
  `10.0.26100.0/ucrt/x64/ucrt.lib`, then executed successfully against the host
  CRT. This validates these two concrete functions only.
- Focused acquisition assertions also passed for deployment selection with
  spaces, explicit override, failed `nm` despite plausible partial stdout,
  forbidden zero floor, actual CRT names/separate tier, and missing CRT error.
- Review found an overflowing decimal-floor bypass and incomplete successful
  COFF-header admission. New focused negatives passed for an oversized floor,
  missing symbol pointer and missing executable-image flag. Positive admission
  of the real full-COFF fixture also passed with the stricter checks.

Preserved evidence directory:
`D:/dev/simple-windows-census-evidence-20261107-01`.
`native-fixtures.sdn` records source HEAD and SHA256 for LLVM tools, CRT DLL,
SDK import library and native executables. Build/run logs and generated C are
retained there; `check-bounds.log` preserves the additional negative results.
The initial focused assertion PASS was captured in the execution session; a
subsequent bounds-only check replaced its original log. Native build/run logs
and the native artifact receipt were preserved unchanged.

Reproduction uses `scripts/check/tests/check-extern-census-windows.ps1`:
run `-Phase Prepare -EvidenceDir <new-private-directory>` once, then
`-Phase Check -EvidenceDir <same-directory>`. Tool/SDK/Bash paths are explicit
parameters. Check reuses native execution evidence rather than rebuilding.

The full-tree declaration extractor and census, ratchet baseline, unresolved
guard, and compiler qualification were not run. Sparse fixture inputs were not
used to bypass the census's 5,000-declaration gate. No general Windows symbol
guard or full bootstrap PASS is claimed.
