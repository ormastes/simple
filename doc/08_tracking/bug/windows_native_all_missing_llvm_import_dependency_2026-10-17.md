# MSVC aggregate runtime omitted its qualified LLVM import library

Status: source repair authored; Simple regression execution and canonical
producer qualification pending. No existing failed compiler is admitted.

Requirement: `REQ-WINDOWS-NATIVE-ALL-LLVM-DEPENDENCY`.

## Real boundary

The retained f612 diagnostic compiler reached real Hello parsing/HIR with one
module and zero errors, then the MSVC native link reported LLVM C API symbols
such as `LLVMAddGlobal` and `LLVMBuildIntToPtr` from the selected aggregate
compiler archive. `core-c-bootstrap` still selects the existing backfill and
native-all archives; native-all's LLVM references require its producer's C API
import library. This is distinct from the preceding `__simple_pow` provider
omission and from later discarded `rt_value_print`/`rt_value_println` archive
relocations observed after a diagnostic exact-library injection. None of those
failures is a timeout or successful canonical Hello receipt.

## Source repair

`native_all_support.spl` now selects only the exact `LLVM-C.lib` sealed in the
same absolute runtime authority as the selected native-all archive. It preserves
archive order, makes the dependency unique and last, refuses missing bytes,
foreign paths and unsupported MSVC target spellings, and leaves aggregate-free
links alone. There is no PATH search, runtime export guess, generated DLL stub
or fallback to an arbitrary installed LLVM package.

`native_linking.spl` invokes this selector in both internal COFF and external
MSVC paths, including explicit aggregate inputs. Managed runtime preflight
includes the import library in its existing snapshot pin checks; link-time
selection also revalidates the dependency through the established runtime
authority owner. Existing linker duplicate/unresolved-symbol policies do not
change. The actual import archive must have the correct target machine; the
linker's ordinary COFF validation still owns that check.

## Producer staging and snapshot

The existing bootstrap LLVM build authority already records exact Windows
23.1.1 C API import-library path and SHA-256, alongside the producer's LLVM
configuration and runtime DLL identity. `prepare_seed_generation` accepts that
captured authority as an optional ninth argument and stages those exact import
bytes before sealing the new generation. It verifies source hash before/after
copy and destination hash, emits a producer receipt and refuses mismatches.
Windows tuple projection carries the dependency and receipt forward. Existing
directory snapshots and generation hashes therefore include it; an already
sealed generation or admitted runtime snapshot is never mutated.

Fresh publication and explicit legacy migration pass the captured producer
authority through their existing call path. An admitted parent forwards its
already-staged library/receipt without rediscovering LLVM. Old sealed tuples
lacking this dependency remain incomplete rather than silently borrowing a
different installation. Fresh Windows staging currently admits the existing
x86_64-pc-windows-msvc producer contract only; another architecture needs its
own producer qualification.

## Required evidence

The five-case Simple selector spec has an authored mirrored manual and remains
TEST_BLOCKED pending a qualified runner. The bounded shell staging test checks
real temporary file custody, target/authority refusal, duplicate authority rows,
hash changes, and unchanged forwarding. These fixture bytes do not prove actual
LLVM import ABI or a working compiler.

On the current Windows host, explicit `C:/dev/tool/Git/bin/bash.exe` syntax
validation passed for all four changed shell files. The custody test passed
with `windows LLVM import staging checks PASS (byte custody only)` and exit 0.
Its first actual run exposed a missing test-harness import of the existing
`command-snapshot.shs` manifest reader; adding that canonical helper import
resolved the harness failure. No Simple spec, native LLVM link, generation
publication or canonical compiler qualification ran in this repair lane.

Retain both frozen failed trees, all original archives and 1349 module objects.
The build owner must resolve the separate discarded-section failure, build a
new canonical producer containing this repair, inspect the selected exact
library/DLL identities and compile/run real Hello before dependent smux phases.
