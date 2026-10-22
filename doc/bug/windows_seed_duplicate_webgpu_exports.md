# Windows bootstrap seed links two owners of three WebGPU symbols

## Observed failure

The canonical Windows bootstrap at `380200890ff` stopped during the Rust seed
build with Cargo exit 101. Its `rust-seed-build.log` reports `lld-link`
duplicate definitions of `rt_webgpu_compute_draw`, `rt_webgpu_present`, and
`rt_webgpu_upload_pixels`, each in `libspl_hosted_runtime-*.rlib` and
`libsimple_runtime.rlib`.

The compiler's Windows dependency already links `spl_hosted_runtime` with
`win32-real`. The runtime's fail-closed WebGPU twins suppressed their unmangled
exports only under `native-all-provider`, which the compiler seed does not
select. This is export ownership, not an ABI signature mismatch.

## Repair

Select the narrow runtime feature `hosted-webgpu-provider` through the
compiler's Windows dependency. That feature suppresses only the three
overlapping twins and links the canonical hosted provider into the runtime
itself. The latter matters because the runtime also emits a cdylib with a
generated table of ABI addresses; relying only on a downstream compiler link
would leave its own DLL without the selected provider.

Standalone runtime builds retain the fail-closed exports. The existing
`native-all-provider` selection remains supported. Neither a duplicate-symbol
linker override nor a fake implementation is introduced.

## Verification

`scripts/check/check-webgpu-runtime-export-ownership.shs` compiles the actual
twins and hosted WebGPU sources into separate rlibs. One codegen unit places
each forced archive anchor alongside its exports, reproducing the original
archive extraction mechanism. The negative control must fail on all three
duplicate names. Positive controls execute the three ABIs for standalone,
Windows hosted ownership, and native-all ownership. A hosted runtime cdylib
also links a generated-table-style table of all three ABI addresses; a native
Windows loader opens that DLL and executes the table entrypoint.

On 2026-10-21 the fixture passed with Rust 1.93.1 and pinned LLVM 23.1.1
`lld-link` under `windows-msvc-bootstrap-env.shs`. Evidence is retained in
`build/session/webgpu-export-fix/webgpu-export-owner.eFkehg/`, with the command
in `build/session/webgpu-export-fix/run.sh` and verdict in `check.log`.
This proves the bounded provider/link mechanism, not a complete rebuilt seed
or a qualified compiler generation. The canonical bootstrap must consume the
new source identity and complete its normal build and sanity gates.
Offline locked Cargo metadata also confirms the Windows compiler feature edge
and the runtime's optional hosted-provider dependency. `Cargo.lock` includes
the new runtime-to-hosted edge; no package versions changed.

The guard is registered as automated `bootstrap` tier in
`config/check/must_check_gates.sdn`. Native fixture compilation requires a
configured Rust/linker environment and is outside the push/local fast-gate
budget. The outgoing-range shell hygiene check verifies this wiring without
executing the native fixture.
