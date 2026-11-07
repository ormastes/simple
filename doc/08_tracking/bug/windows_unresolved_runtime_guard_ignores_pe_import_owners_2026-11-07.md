# Windows unresolved-runtime guard ignored PE import owners

**Status:** verification pending; focused native fixture evidence collected.
**Source base:** `a9f5300584e3031b9f18f01c6ce3bf05ae6896c8`.
**Parent:** `windows_stripped_seed_binary_blinds_symbol_guards_2026-09-02`
remains OPEN. Census and runnable-guard repairs are separate landed slices.

The guard's platform branch distinguished Darwin from all other hosts. Windows
therefore used `nm -D` and `ldd`, neither of which supplies its PE import-owner
evidence. A full COFF table could make the artifact non-vacuous while the
runtime import set remained invisible. The Windows selftest also used ELF-only
link/strip flags and could not establish a trusted oracle.

## Actual before/after evidence

LLVM 23.1.1 built a native Windows x64 executable importing
`owner.dll:rt_fixture`. Its valid owner DLL and executable ran together and
returned zero. A second candidate directory contains the same executable, an
actual same-name owner DLL missing that export, and an unrelated DLL exporting
`rt_fixture`. The original guard returned exit zero and:

```
PASS — 0 symbol(s) checked across 1 binary(ies) + archive, 0 unresolved
```

The repaired guard checks one runtime import. It returns PASS for the valid
candidate and FAIL naming `owner.dll:rt_fixture` for the wrong owner. The
unrelated DLL cannot satisfy an import from another owner. The broken candidate
was not executed; its guard failure is static owner evidence, not an observed
Windows loader exit.

## Bounded Windows contract

The new route supports AMD64 PE executable images with a readable, nonempty
full COFF symbol table. It checks actual reader exit statuses and separately
reads PE imports. Each named runtime-prefixed import is checked against the
exact DLL basename in the candidate application's directory. Missing owner or
reader evidence is ERROR; a readable owner lacking the named export is FAIL.
Actual undefined COFF runtime symbols are also checked; an `__imp_` spelling is
associated with a target only when the PE import-owner fact exists.
An ordinary undefined runtime symbol remains FAIL even if a same-name PE import
exists: import evidence does not define a missing direct thunk.

Other architectures, ordinal imports, delay imports and forwarded runtime
exports explicitly return ERROR as unsupported coverage. Reader output is
capped at 16 MiB per invocation; descriptors, imports, providers and exports
have finite count bounds. Failed readers cannot admit partial stdout.
Successful but structurally truncated reader output is also rejected: every
Import/Export opener and symbol/name/value record must belong to a complete
parsed block.

This is static candidate-owner evidence. It does not prove the loader's full
search policy, transitive DLL closure, ABI/call compatibility, or compiler
health. Exports do not replace the executable's full COFF table. Stripped
deployment binaries still require a matching immutable symbol artifact; no
companion-artifact protocol is introduced. Materialized historical binaries
with unavailable owner DLLs fail closed. Unix and archive semantics retain
their previous scope; neither was qualified by these Windows fixtures.

The Windows selftest entry dispatches its own native PowerShell fixture suite,
using LLVM tools beside the selected `PE_READOBJ`. Select compatible tools with
`NM` and `PE_READOBJ`. Explicit paths containing spaces remain one artifact.

## Preserved evidence and remaining verification

`D:/dev/simple-windows-unresolved-evidence-20261107-02` retains generated C/DEF
files, native artifacts, build logs, the good native execution log,
`native-fixtures.sdn` tool/artifact hashes and `legacy-wrong-owner.log`.
The focused suite invokes the actual guard's `--bin` route. Native unsupported
fixtures cover stripped COFF, ordinal imports and forwarded runtime exports.
Reader fault injections separately cover partial failure, unsupported machine,
missing header evidence, delay-import coverage, and mapped/unmapped undefined
COFF names; these injections are not claimed as native undefined-link repros.
Seven base and seven additional assertions passed, followed by five new review
assertions for same-name direct-undefined masking, truncated final import/export
blocks, archive-only independence from PE tools, and conflicting selftest flags.
These are focused `--bin`/CLI results; they do not qualify automatic selftest
dispatch. Logs are `check.log`, `check-extra.log` and `check-review.log`.

The harness supports Prepare (fresh private output), Check (reuse native
evidence), CheckExtra (new reader/path assertions), and All. No green native
build/execution was repeated after the producer evidence was established.
Initial fixture argument assembly and reader redirection failures were repaired
within the finite test/fix budget. The first failed preparation remains in the
separate `...-01` directory.
Generated C/DEF byte hashes are retained in `native-source-hashes.sdn`.

Whole deployed-compiler scanning, the public automatic `--selftest-only`
dispatch, archive checks, Unix regressions and compiler/bootstrap qualification
remain pending. No Simple compiler or Rust seed, global cache/lock mutation,
bootstrap rerun or full-health PASS was used for this repair.
