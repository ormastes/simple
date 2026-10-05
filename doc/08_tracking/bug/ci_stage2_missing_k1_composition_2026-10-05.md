# CI Stage 2 omitted the selected K1 composition

Status: workflow repair drafted; rebuilt compiler qualification pending.

The Linux Phase 2 artifact from GitHub Actions run `37262871663`, source
`817fef0`, starts successfully but cannot compile Hello. Its SHA256 is
`62b1e64c1fe0b06cce02fbf1fb746d9aac602e3fd1cd9ad77700783f041ca674`.
The retained `hello-build.log` reports `PLUG-E-K1-POLICY`, selected policy
`unselected`, and `stub: no K1 composition bound`. This is a compiler
composition failure before application execution, not a DB/web test result.

`build-binaries.yml` supplied only `--source src`. Canonical bootstrap instead
supplies `src/compositions/kernel_llvm_cranelift` before the compiler, app,
and lib source roots. That overlay provides the selected K1 module; the
compiler's default module intentionally refuses an unselected composition.
Both Linux and Windows cross-build commands now use the canonical ordering,
explicit Cranelift producer backend, core-C bootstrap runtime, and one worker.

The Linux build job previously accepted `--version` while ignoring failures
from `--help` and `-c`. It now invokes the existing
`check-stage2-hello-world-native-build.shs` before uploading the artifact.
The gate requires compilation and execution through the explicit-entry arm
and checks the positional-entry arm for crashes. It uses the produced
compiler's LLVM backend: the core-C bootstrap runtime contains named
Cranelift bridge traps, independently of the seed's functioning Cranelift
code generator. A failing gate stops upload. This does not qualify Windows
execution or replace the full bootstrap admission gates.

The selected LLVM port uses the pure-Simple LLVM IR emitter and the `llc`
command, not the separate `llvm-lib` backend's shared-library loader. No
libLLVM resolver environment is required for this gate. The Linux tool
installation prerequisite now checks `llc` as well as Clang, LLD, and llvm-nm;
if absent, the existing `llvm` package installation supplies it. Tool discovery
still validates the executable through the canonical compiler resolver.

## Local recovery evidence

The downloaded Linux seed from the same CI run has SHA256
`e5d49e42816843002f11a6fbd5f619168063253c9b2d8a91a4ae2f38111d380d`.
Its version command succeeds under WSL Ubuntu and identifies it as a
bootstrap-only seed. Its source revision accepts the corrected arguments.
WSL has Clang 23.1.1, GCC, GNU linker/archive tools, and LLVM libraries.

A corrected Stage 2 build was launched separately against frozen release
source `c8d61d4d719199f48d156531516109f3152ac64c` in the WSL-native checkout
`/var/tmp/simple-item5-phase2-20261005`, with a 1200-second timeout, one
worker, and enforced process-tree RSS cap of 5859375 KiB. It timed out with
exit 124 after 1200 seconds, peak RSS 1195840 KiB, and confirmed quiescence.
It retained 629 cache files and 630 native-object-directory files; no compiler
binary was produced. This was a progressing build stopped by its time budget,
not a memory-cap failure.

One continuation retains the same seed, worker count, native cache, and
enforced RSS cap with a 3600-second budget. Before restart, the quiescent
checkout fast-forwarded to release `17cdbe022a6b7861b22d7c74e227a0581b896073`.
Reviewed changes were the Windows cross-target seed ABI repair, subsystem
matrix tooling, and a FreeBSD-specific observer default; no Simple compiler
or C runtime input changed. The prebuilt seed is unchanged, so its bytes do
not acquire the new Rust ABI repair retroactively. The continuation writes
separate `continuation-1.rss.env` and log evidence; the original receipt and
object cache remain intact.

Continuation 1 reached the linker: `compiled=570 reused=628 failed=0`,
then exited 1 because `llvm-nm` was absent from PATH. Peak RSS was 1183876
KiB, with confirmed quiescence. All 1198 source objects were available in
the native cache. LLVM's `llvm-nm`, `llvm-ar`, and `ld.lld` were verified under
`/usr/lib/llvm-23/bin` (23.1.3). A separate 1200-second continuation adds that
directory to PATH, preserving the original `/usr/local/bin/clang` selection
(23.1.1), and sets `SIMPLE_LLVM_BIN` for the subsequent pure-Simple tool
resolver. It retains the same enforced memory cap and object cache.

Continuation 2 reused 1196 objects and compiled two, but a short-lived child
exited between opening and reading `/proc/PID/stat`. The watchdog terminated
with observation failure 89, peak 1170828 KiB, and confirmed quiescence.
A separately tested watchdog repair treats only ESRCH/ENOENT reads as vanished
tasks, preserving fatal handling for other I/O errors and malformed records.
Continuation 3 used that isolated guard without changing compiler sources.
It reached the linker and exited 1 normally, peak 1250728 KiB: the core-C
runtime link lacked `rt_any_to_int`, `rt_shared_parse_cell_read_v1`, and
`rt_value_truthy`. At that point no Phase 2 executable existed.

`rt_shared_parse_cell_read_v1` already has C and pure-Simple implementations;
the seed's runtime translation-unit selection does not include its C owner.
`rt_value_truthy` has a Rust runtime owner, while the missing `rt_any_to_int`
requires further lowering/runtime contract diagnosis. None may be replaced
with a placeholder return merely to make the compiler link.

The runtime exports and binary-safe process capture subsequently landed in
release PR #2568. The first Hello attempt also exposed the canonical gate's
fixture under `scripts/`, outside the admitted source inventory. The default
fixture now lives at `test/04_smoke/bootstrap_hello_world.spl`, with identical
content; existing certification fixture callers remain intact. A second
attempt exposed the separate decimal fingerprint/SHA-256 mismatch described
in `native_capsule_fingerprint_sha256_2026-10-05.md`.

With those concrete owners repaired, the compiler built from release
`f21317acc86ad9ada43023328173b9283fa9a24a` plus the fingerprint repair has
SHA256 `b0fccf9f6667808acbb01bee6dbeaa53f3d0038e31068f9aeee58a21c6b4a53e`.
The final canonical gate exited zero: `PASS — 2 case(s) checked`. Its entry
arm compiled and executed the expected `hello` output; its positional arm
checked for crashes. The compiler hash remained unchanged. The outer log is
`build/review/item5-linux-phase2-hello.log`; the isolated WSL checkout retains
`build/item5-phase2/hello.result.json`, including explicit private runtime
archive identities. This is local native qualification, not an executed CI
workflow result. No DB/web correctness or AVX512 performance claim follows
from this source change.

Clean-CI review also found that the native job only restored an optional
Cargo cache, which cannot guarantee the archive pair required by the
produced compiler's linker. The Linux seed job now builds both canonical
`simple-native-all` with `spl_hosted_runtime` and `simple-compiler-backfill`
for the explicit Linux target using the bootstrap profile, records
their SHA-256 values, and uploads a required runtime artifact named for the
same source revision. Before Hello, the native job downloads that artifact,
checks both digests, and explicitly sets `SIMPLE_RUNTIME_PATH` to its
directory. Normal source-inventory cold initialization is enabled for the
fresh job. This runtime authority belongs to the produced compiler's Hello
link; the seed still builds Phase 2 with its core-C runtime. Qualification
does not depend on a successful or fresh optional Cargo-cache restore.
The package set follows the canonical Linux bootstrap recipe, without the
optional driver-compat feature. Unlike an already provisioned local build,
CI permits locked dependency downloads rather than requiring offline mode.

Static validation: the edited workflow parses with PyYAML 6.0.3; all three
changed shell blocks pass `bash -n`; `git diff --check` passes. These checks
do not execute the compiler or establish native qualification.
