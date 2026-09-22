# CUDA signed byte-span and solver launch ABI correction

## Frozen contracts

Base: `36eb5709088`, with proposed loader additions owned separately by
`/root/stage2_after_backend_receiver` in
`/Users/ormastes/simple-tmp/phase2-runner-gpu-provider-20260923`.
The frozen 79-export manifest remains unchanged.

Authoritative signatures in
`src/compiler_rust/runtime/src/cuda_runtime.rs` and
`src/lib/nogc_sync_mut/cuda/sffi.spl`:

- Public `rt_cuda_module_load_data`: `(const uint8_t *, uint64_t) -> int64_t`.
- Provider `rt_cuda_module_load_data_bytes`: `(int64_t, int64_t) -> int64_t`.
- Simple `rt_cuda_launch_kernel`: `(module: i64, name: text, gx, gy, gz, bx,
  by, bz, args_ptr: i64) -> i64`; native text expands to pointer/unsigned64.
- Provider `rt_cuda_launch_kernel_name`: ten signed64 parameters returning
  signed64. Its final argument is a `void **` table of addresses of argument
  storage, not a Simple array handle or a table of argument values.

## Changes

The loader span adapter uses the provider's exact signed64 function type,
converts the pointer through `intptr_t`, and rejects lengths above `INT64_MAX`
before acquiring a call pin. Success/error calls preserve acquire/release
balance and provider return values. It adds no allocation or copy.

The solver's local nine-argument function-handle/bool declaration conflicts
with the canonical module/name/integer-status declaration. A narrow pure-Simple
helper in `nogc_sync_mut.cuda.launch_args` imports the canonical SFFI owner.
It writes at most 20 raw i64 values and 20 pointers into an exclusively owned
320-byte scratch block and makes one canonical launch call. The solver
provides module handles and kernel names; scratch is allocated once on demand,
reused across launches, and freed/reset in `destroy`. Invalid module, empty
work or failed allocation avoids launch; the helper preserves nonzero status.
The obsolete function-handle fields and redundant kernel lookups are removed;
the canonical launch owner resolves the supplied module/name pair.
The solver's pre-existing unit-return dispatch still ignores launch status.

This does not qualify the entire solver. Other legacy module/memory/sync
externs, float bit packing, whole-solver ownership, and actual GPU execution
remain outside this correction and need separate evidence.

## Evidence and current limits

Evidence root:
`/Users/ormastes/simple-tmp/phase2-cuda-abi-correction-20260923/build/evidence/cuda-abi-correction`.

`scripts/check/check-cuda-signed-span-abi.shs` extracts the actual old macro and
new adapter into a typed C-provider harness, then uses LLVM23 function-call
UBSan. The old pointer/u64 function type aborts with status 134 and
`call to function provider_bytes through pointer to incorrect function type`.
The corrected adapter exits 0: valid bytes, signed-length boundary, overflow,
null/zero input and provider absence; overflow invokes no provider/pin.
10000 warmed calls retain balanced leases, measured 0.000022s CPU; green maxRSS
3555328 bytes. This is synthetic ABI evidence, not a GPU/performance comparison.
The C harness was measured, not wrapped by the process-tree RSS guard.
The tested adapter SHA256 is
`cc1d1a81c641069ab79cf9ecf7a4092da3f08325a9b387503494b19ac58f37f7`.

Compiled-Simple boundary evidence is **PASS** for the scoped ABI fixture.
Producer is admitted Stage2 SHA256
`0c65162af9c89bdb9c6583ca91820f795231c9bf4c451b6a69ea66794c66c084`,
with matching verified runtime capsule and retained receipts. Exact canonical
declarations and helper source were extracted into a single-module fixture to
bound compilation. It includes literal/computed text, module/name/dimensions,
negative status, null scratch, empty/oversized arrays, max-20 canaries, and scratch
reuse. The first output used `.a` without `--emit-archive`, so the driver produced
a Mach-O executable despite printing `Archive`; it is rejected as evidence.
The corrected explicit archive build passed (97216 KiB sampled peak RSS,
quiescent 1, zero observer errors). Archive SHA256:
`f5e839eeacf494fe0e47c8cfbfb5ab6667ee720625ad54ec547146e650a43b9a`.

The first C link needed the emitted `caller__cuda_native_boundary_check` symbol.
After correcting that symbol, linking still failed because the helper loop
requires `rt_pool_safepoint`. Its canonical C owner is
`src/runtime/runtime_pool.c:763`. That lane stopped at its bounded attempt cap.
A host-slot coordination race allowed
the first tiny native build to overlap another probe; these runs are not
isolated performance evidence.

### Independent native qualification

The fresh, separately owned `native-pool-qualification1` lane linked the
unchanged retained caller archive with production `runtime_pool.o`,
`runtime_native.o`, and `runtime_legacy_core.o`, then passed on its first run.
`pool-owner.txt` and `link.map` identify exactly one `rt_pool_safepoint`, from
object index 5 (`runtime_pool.o`); no `runtime_thread.o` or stub is present.

- Pool source SHA256:
  `98e919b9bee7052b3f0e430fef18cb0c239a6295450f7829f1b5365063244524`.
- Pool object SHA256:
  `210ce8c9503c536391c1cfa4a5ed9b16e316f2c534b33ea474195c4dde886ea7`.
- Linked boundary SHA256:
  `70b79f167084c34ff5cb0669e3246fd5fa3e0f0b0f99149f4ff2769c19f8f7bb`.
- Exit 0, `compiled-simple-span-and-argument-boundary=PASS`, no function-call
  UBSan diagnostic. Literal/computed text, module/name, all six dimensions,
  3/max-20 values and pointer-table addresses, canaries, reuse, unavailable
  status and invalid/empty/oversized arguments have asserted outcomes.
- Source/artifact hashes before and after match. The production helper is
  compiled and exercised; the full solver is not compiled or executed here.
- Pool compile, link and execution receipts each report exit 0, quiescent 1,
  observer errors 0 and sampled enforcement at 5859375 KiB. Sampled peaks
  2560/2416/2400 KiB undersample these short processes and are not exact maxima.
  `/usr/bin/time -l` reports execution max RSS 3604480 bytes and 0.33s wall.
  `hard_memory_limit=0`; no kernel hard-containment claim is made.

The admitted Stage2 explicit-entry archive route delegates to Rust
`rt_native_build`. This is actual compiled Simple ABI interoperability, not
self-hosted frontend, physical GPU, full-solver, production launch forwarder,
full-loader lease, test-runner,
Phase2 or Stage3 acceptance. The provider and call-pin interface are synthetic.
Exact launch/link commands and the independent report are retained in
`qualify-native-pool.sh` and `native-pool-qualification1/RESULT.md`.

The SFFI source backlog audit passed its four assertions and emitted 11135 warning
rows (`source_only=true`, `admission=absent`). That is not ABI admission.
No full runner, bootstrap or push occurred. Independent Astra code/evidence
review accepted this scoped ABI correction; the updated report receives final
read-only confirmation before commit.
