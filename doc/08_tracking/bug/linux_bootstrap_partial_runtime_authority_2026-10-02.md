# Linux bootstrap accepted a provider archive as a complete runtime

The 2026-10-02 Linux bootstrap compiled 1,118 Simple units, then missed
`rt_dir_is_real_no_follow`, `rt_shared_parse_cell_read_v1`, and
`spl_thread_current_id`. Two provider-only archives named
`libsimple_native_all.a` made the failure worse: bootstrap runtime admission
accepted any nonempty file, bypassing the complete runtime and leaving core
allocation, argument, array, and string symbols unresolved.

## Correction to the initial investigation

The original entry is `src/app/cli/bootstrap_main.spl`. It requires the hosted
`rt_native_build` implementation. Its explicit `core-c-bootstrap` option does
not mean it can run with a C-only archive: the bootstrap-entry authority branch
selects native-all first. The complete original authority was beside the real
path of the pinned seed, in its immutable bootstrap generation. The old source
checkout has broken git administration; its HEAD is not asserted as provenance.

The seed SHA-256 was
`a6c7bb60b8eb9aa777de1edc950d6258b985f5d696a618c598903ad3633b9f8b`.
Its complete native-all SHA-256 was
`4cde5db743726158a0f4c9de7e5153c969ff5165ba0d0301ba2343c6e47197eb`.
Provider sources were taken from frozen Simple revision
`6b9edd328cc2fd3d7372c2c685a1b2256999fa1c`, with per-source hashes retained.

## Repair

Bootstrap archive admission now requires the hosted driver and the core
allocation, string, and array owners. A provider-only archive fails admission.
The shared parse reader also has a declaration in the C-linkage runtime header;
without it, a C++ driver mangles this one provider.

`scripts/bootstrap/repair-linux-bootstrap-runtime.shs` derives a Linux ELF
authority from an explicitly hashed complete seed archive. It compiles the
three exact provider source units in C mode, localizes unrelated definitions,
collects only the requested function sections, and strips unused symbol-table
entries. It rejects unexpected dependencies, runtime-private functions, mutable
state, and any change to the original export multiset. It never copies
`rt_string_new` into the supplement: that reference resolves to the original
runtime's matching allocation/free owner.

The reviewed derived archive has SHA-256
`d0c9cd0be5ad8635868289de61acaebc526213d92044b684608c64df2f3675bd`.
All 43,782 original exported names and their counts are preserved; exactly
three names are added. This recipe is Linux-specific, while the admission and
C-linkage fixes are shared across hosts.

Archive admission requires a working `llvm-nm`; `nm_command()` supports an
explicit `SIMPLE_NM` path and otherwise selects LLVM tools from PATH. On this
Windows host the MSYS2 PATH copy failed to load with `0xc0000135`. The native
MSVC LLVM 23.1.1 tool at
`C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin/llvm-nm.exe`
successfully read the pinned Windows native-all archive and found each of the
eight required names exactly once, without decoration. Windows launchers must
pin that working tool (or another verified LLVM tool), rather than relying on
the broken PATH copy. Windows authority SHA-256 was
`2dff45ba14c7d0c24263c51628a4602e688c8f3ae04909f14f702bb0b5018470`.
This read-only native-tool check does not claim a rebuilt Windows Rust seed.

## Focused evidence

- Admission unit test rejects both historical partial-archive shapes and
  accepts the required owner set. Exact function/test compiled with `rustc
  --test`; a full Rust seed rebuild was not required.
- The actual repair script rejects an actual three-provider archive before
  compiling anything.
- `src/runtime/test/bootstrap_linux_provider_selfcheck.c` passed against the
  derived archive: directory truth, symlink rejection, real bounded payload
  reads, missing/oversized/nonregular misses, matching string free, and native
  thread identity.
- The shared reader remains an unmangled C export when its unit is compiled
  with a C++ driver after the header correction.

## Bootstrap validation

The guarded retry linked successfully: 2 modules compiled, 1,116 reused,
0 failed; 50.2 seconds and 1,910,628 KiB peak process-tree RSS. The seed warned
that `--mode dynload` was unsupported and emitted one binary; dynload was not
validated. Phase 2 SHA-256 is
`04d72b6adc0e9d1b6696f721bb4a088b5194f10d80642f0e43c2cdabb6c5444d`.

That Phase 2 compiler then compiled the real hello fixture with LLVM, and the
ELF printed `Hello World` with exit 0. Compile/run guards both reported complete,
quiescent, and 4,718,592 KiB enforcement; peaks were 247,268 and 8,264 KiB.
Hello SHA-256 is
`97a8ea0f75b262f8e55a8a3538616dab532496867b1ca4a3b299aa284f926537`.
The first hello invocation using broad project-source arguments was rejected
at source-inventory admission; the supported positional-file route succeeded.

Frozen source and runtime evidence remain under
`/root/linux-bootstrap-ext4/spawn-abi-9e89-run1/linux-runtime-binding-20261002`
in D-backed Debian. Exact guarded hello receipt SHA-256 is
`453323b23cce7dda3c97b4f22d9ea81dbdfe85bee5ddf142a33b37e858eb6ea2`.
This evidence does not claim a completed Phase 3/4 or a production release PASS.
