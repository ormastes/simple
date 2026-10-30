# Mixed C runtime selects incompatible text/byte providers

Status: source repair authored; refreshed native execution pending.
Scope: the pure-Simple runtime builder's C-owned bundle containing both
`runtime.c` and `runtime_native.c`. This is not an SDN grammar change.

## Actual failure and attribution

Three native artifacts select the legacy C bodies despite calling the tagged
text/array ABI. Disassembly establishes the actual implementations:

| Artifact | SHA-256 | Selected byte/text symbols |
|---|---|---|
| Candidate retention probe | `eedbd0c471fa8066d298d407d13d0abec1c4598c5f1201254d1dc62f61dad09c` | `rt_text_to_bytes` at `0x42ea0`; `rt_bytes_to_text` at `0x42fa0` |
| Release baseline V1 probe | `abc78d217f6818b9f4bf92d3873cb72112b8b78f5adb2e3899b9b2c2b7097b71` | `0x3fca0`; `0x3fda0` |
| Strict parser diagnostic | `77127c655a90f2b2aa9fffcbb4070e3c4b862e8e005313c6d1ccc3c0ab194f1a` | `0x32240`; `0x32340` |

The selected `rt_text_to_bytes` calls `strlen` and allocates a private 24-byte
buffer record. The selected `rt_bytes_to_text` calls `rt_array_len_safe`, then
copies `rt_array_data_ptr` directly to `rt_string_new`. The same artifacts'
`rt_string_bytes` produces generic tagged integer slots. Copying those storage
bytes does not recover the original text.

The strict diagnostic rejects valid `x: 1` at offset 4 and the historical V1
writer output at offset 10 with `missing_value`; an empty inline array passes.
Its nonempty SHA-256 inputs all report the empty-input digest. Both text/byte
owners are therefore repaired together. No SHA algorithm change follows from
these observations.

The exact diagnostic link command places `host_runtime.o` before
`host_runtime_native.o` and permits multiple definitions. An independently
inspected producer archive is a different composition; it does not identify the
owners selected in these emitted executables.

Artifacts and link receipts remain under
`/tmp/scv-retention-nativeprobe-20261030/build/` and
`/tmp/scv-retention-baseline-nativeprobe-20261030/build/`. Their execution was
performed by the assigned native probe lane. This repair lane only inspected
the retained binaries, commands and outputs.

## Narrow source repair

The existing pure-Simple runtime compilation owner privately renames only
`runtime.c`'s two obsolete exports when the selected owner is C and both source
units are present. `runtime_native.c` keeps the canonical tagged functions.
No C source, link order, global weak-symbol policy, parser or wire format changes.
The legacy translation unit has no internal calls to either canonical name.

To respect the source-size limit, the existing hosted platform/compiler selection
block moves unchanged into `runtime_host_compiler_v1.spl`. Every moved helper is
explicitly public; `runtime_compiler.spl` explicitly re-exports the named helpers
and `HostedCCompilerPlan`, preserving existing import paths. Source-contract tests
follow the owning module and retain the cleanup and I/O facade checks.

The policy version and selected decision enter the POSIX cache key and Windows
cache context; the actual define arguments also enter Windows preprocessing and
object material. After cache-hit and fresh-compilation convergence, materialized
objects must prove both canonical names absent in the legacy object and strong
in the native object. Windows preprocessing may already omit legacy definitions;
their private aliases need not exist in that case.

Unit contracts cover composition boundaries, both compiler flag spellings and
stale/missing/weak owner rejection. The standalone native fixture checks actual
ASCII, embedded NUL, UTF-8, validated source custody, known SHA-256 vectors and
unchanged scalar/V1/V2 grammar. Typed V2 retention admission remains a separate
integration check. No repaired native PASS is claimed by this report.
