# Vulkan last-error C-string return bypassed Rust backend conversion

Baseline: `b9e170933cdccbb9f5dfc7d7126fe7e97ae5378e`.
Scope: Rust Cranelift native call emission; no full provider/bootstrap rebuild.

## Cause and correction

`calls.rs::C_STRING_RETURNING_RUNTIME_FNS` already includes
`rt_vulkan_get_last_error`, whose runtime ABI is zero parameters returning
`*const c_char`. Its Simple declaration returns `text`. However, the shared
`runtime_sffi.rs::RUNTIME_FUNCS` table omitted this symbol. The call therefore
missed `ctx.runtime_funcs` and took generic external-call lowering, which
stores the raw pointer without `rt_cstring_to_text`. Other registered Vulkan
text-returning calls entered the shared conversion path.

Add the missing `RuntimeFuncSpec` with `&[]` parameters and `&[I64]` result.
Keep conversion in its existing shared owner. Do not change the public C ABI,
add per-symbol conversion logic, or decode all text-returning functions: most
runtime text functions already return boxed RuntimeValues.

## Reproduction and evidence scope

The original native Vulkan scalar fixture and emitted archive are retained in
`/Users/ormastes/simple-tmp/phase2-gpu-vulkan-scalar-20260923/build/evidence/phase2_gpu_vulkan_scalar-native1/`.
Its actual native execution exited 34 on the last-error string comparison.
Disassembly shows conversion after device type at `0x518`, but raw `x0` after
the last-error call at `0x55c`.

That fixture was invoked with `--entry` through admitted Stage2 compiler
SHA-256 `0c65162af9c89bdb9c6583ca91820f795231c9bf4c451b6a69ea66794c66c084`.
`bootstrap_main.spl` forwards this entry route to Rust `rt_native_build`
outside explicit Stage3/4 modes. It is therefore native ABI evidence for the
delegated Rust backend, not proof of the pure-Simple positional compiler route.

Focused tests in `codegen_instr_tests/cstring_returns.rs` build actual native
objects through the production MIR-to-Cranelift codegen. They independently
lock the eleven-name C-string census, check every exact runtime signature,
and check one source-call and one decoder-call relocation per consumed result.
Mach-O ARM64 GOT page/load relocation pairs count once; unexpected ARM64
relocation kinds fail the oracle. Negative cases cover boxed `rt_env_cwd`,
scalar driver hash, and discarded C-string results.

Private worktree:
`/Users/ormastes/simple-tmp/extern-cstring-return-metadata-20260923`.
Evidence: `build/native_probe/cstring-{red,red-oracle,green}/`.
Command: `cargo test --manifest-path src/compiler_rust/Cargo.toml
-p simple-compiler --lib cstring_returns -- --nocapture --test-threads=1`.
The green invocation skips the two unchanged negative checks already passed
by the corrected red run. The wrapper is
`build/native_probe/run-cstring-registry.sh`; private cache
`build/native_probe/cargo-target`, jobs 2, test optimization/debug 0,
incremental disabled, strict stub setting, pinned LLVM23 environment, and
Rust `1.100.0-nightly (215a8af4b 2026-09-15)`.

Three bounded cycles:

1. Initial red: missing registry signature reproduced, but raw relocation
   counting also failed on ARM64 pairs. 73.68s, sampled peak 3,519,936 KiB.
2. Corrected red: two intended failures (missing signature and zero last-error
   conversion calls); two negative tests passed. 27.66s, peak 3,516,960 KiB.
3. Green: both formerly failing tests passed across all eleven functions.
   35.97s, peak 3,512,464 KiB. Test execution itself was 0.03s.

Receipts show zero observer errors, quiescence, and sampled enforcement at
5,859,375 KiB. `hard_memory_limit=0`; no kernel containment claim. The extra
green source rebuild makes aggregate Cargo wall times non-comparable for
runtime performance. Compilation still exceeds the ordinary 1 GB target;
that limitation remains open. The fix adds a static registry entry and the
required string allocation/copy for the previously broken return.

Green test executable SHA-256:
`1bb27e056acb6eac8ce9a92aca18035a61c93889840a9251e603c9e944e37430`.
Direct-env working audit and executable-spec layout check passed (zero specs
under `doc/06_spec`). Native object emission is proven; execution of the
corrected full Vulkan fixture and compiler/core/MCP suite remains pending a
rebuilt qualified provider/runtime. No bootstrap, deployment, or push occurred.

Independent Astra-high review: PASS for the scoped registry change and native
object-emission evidence; no blocking findings. Runtime decoded-content and
pure-Simple compiler claims remain outside that approval.
