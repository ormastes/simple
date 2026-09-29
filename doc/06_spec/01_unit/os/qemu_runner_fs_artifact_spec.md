# Filesystem wrapper artifact admission

Requirement: [REQ-019, evidence and traceability](../../../02_requirements/feature/simple_platform_unification.md).
Executable source: [qemu_runner_fs_artifact_spec.spl](../../../../test/01_unit/os/qemu_runner_fs_artifact_spec.spl).

Status: **MissingEvidence** for Simple execution and generated docgen output.
This is a maintained manual, not a claim of a passing generated specification.
The current workspace has no admitted pure-Simple host runtime. The Rust seed
was not used as substitute test or qualification evidence.

## Operator workflow

1. Build either `fs_test_entry.spl` (`x64-nvme-fat32`) or the toolchain VFS
   wrapper with the admitted host compiler.
2. The runner reads the completed ELF symbol table before accepting the build.
   A cached output is inspected again. Direct QEMU run, `test_os`, and both
   named-scenario run/test paths check their resolved kernel before process
   creation. The named-scenario paths do not rely on a preceding build check.
3. On failure, inspect `phase=artifact-admission`, `reason`, and `symbol`.
   Restore the shared provider implementation or link composition, then rebuild.
4. Once a pure-Simple runtime is admitted, execute
   `bin/simple test test/01_unit/os/qemu_runner_fs_artifact_spec.spl` and generate
   this spec's manual with the canonical docgen workflow.

## Contract scenarios

| Input evidence | Expected result |
|---|---|
| All required strong definitions; zero-sized entry aliases | `ready` |
| Unrelated defined weak syscall default | `ready` |
| Generated `_stubs_freestanding.c` FILE record | `generated-freestanding-stubs` |
| Any required weak function or counter | `required-symbol-not-strong` |
| Any absent required symbol or stripped symbol table | `required-symbol-missing` |
| Strong undefined symbol anywhere | `undefined-symbol` |
| Versioned nine-field undefined row, including required weak imports | `undefined-symbol` |
| Required null address, malformed address, ABS/COM/section zero | `required-symbol-not-defined` |
| Required function represented as data | `required-symbol-wrong-kind` |
| Assembly NOTYPE function and GNU/LLVM whitespace | `ready` |
| Unsupported entry | `unsupported-entry` |
| Unavailable/failing symbol inspection tools | `symbol-inspection-failed` |

The toolchain entry additionally requires its path-read, buffer-address, and
text-to-bytes dependencies. The filesystem entry requires NVMe/FAT32 operations
and its test-counter storage. The gate does not reject every weak symbol, and
`SIMPLE_ALLOW_FREESTANDING_STUBS=1` never disables the check.

## Evidence limits

Symbol admission cannot prove arbitrary strong function bodies are correct.
It does not prove ELF loadability, guest storage behavior, persistent NVFS,
firmware boot, or compiler execution inside SimpleOS. Those remain independent
qualification requirements. Static integration checks and inspecting a known
bad ELF cannot substitute for executing this Simple specification.

On 2026-09-13 the bounded source check confirmed all four admission hooks and
their order before success/stamp publication or QEMU spawn. A separate readelf
inspection of the retained `build/os/simpleos_fs_test_32.elf` found the generated
FILE marker and eight required weak 8-byte functions. Its SHA-256 was
`8b351bd57d731c2b45a5c942d65ba3dbd0a054d531950f84f27994182581f1e7`.
These are static integration and rejected-artifact observations only. A review
found three additional launch paths; the follow-up patch gates
`_run_scenario_impl`, `test_scenario`, and `test_os`. Two source-contract
specifications assert those calls precede QEMU launch and special-probe
dispatch. The bounded follow-up source checks passed for all three paths and
their shared helper. The parser accepts optional readelf version-index columns
and normalizes `@VERSION`/`@@VERSION` suffixes before checking required names;
versioned undefined rows cannot be skipped. Execution of the Simple
specifications remains `MissingEvidence`.
