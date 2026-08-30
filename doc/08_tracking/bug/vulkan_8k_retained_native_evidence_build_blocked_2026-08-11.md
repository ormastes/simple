# Vulkan 8K retained native evidence build blocked

Date: 2026-08-11

## Reproducer

```text
SIMPLE_TIMEOUT_SECONDS=600 bin/simple native-build --source src/compiler \
  --source src/lib --entry-closure \
  --entry test/05_perf/graphics_2d/bench_vulkan_8k_retained_damage.spl \
  --backend cranelift --release \
  -o build/vulkan_8k_retained_damage_bench
```

## Observed

The entry-closure build emitted dependency warnings, then produced no further
progress or output artifact for more than seven minutes and was terminated
under the session runaway guard. Direct execution also selected JIT and failed
before `main` because `rt_struct_receiver_valid` was missing from the JIT
runtime symbol table. A forced-interpreter 8K semantic run reached its 300
second watchdog without producing a benchmark record.

## Required closure

- Produce the benchmark executable within a bounded, reported build interval
  without stub fallback.
- Use the current Vulkan runtime containing exact range and packed-strided
  buffer downloads.
- Emit one `VULKAN_8K_RETAINED` record with viewport, binary/backend/device
  identity, p50/p95, RSS, transfer bytes/calls, fallback and completion state,
  readback mode, and checksum.
- Only a native row with p95 at or below 12.5 ms may satisfy 8K/80.

No 8K/80 claim is valid from the timed-out interpreter or incomplete build.

## 2026-08-12 isolated rebuild attempt

A non-deploying full bootstrap was started at
`build/bootstrap-vulkan-8k-20260812` with `--full-bootstrap --full-cli
--no-mcp`. It rebuilt the Rust seed, full native runtime, non-LTO runtime, and
compiler backfill over 17 minutes with bounded tree RSS. Before admitting a
candidate, the bootstrap detected that shared-worktree Rust inputs had changed
during the build and failed closed:

```text
error: Rust inputs changed during full bootstrap; refusing to publish a stale seed
```

No artifact was deployed and no retry was made. The repository concurrently
contained changes across compiler/runtime Vulkan, interpreter, parser, and
driver files, so bypassing the fingerprint gate would invalidate the benchmark
identity. The native packed-strided Vulkan round-trip remains independently
green, but the end-to-end 8K benchmark is still blocked until a stable Rust
input window permits one admitted candidate build.

## Narrowed evidence

The underlying native packed-strided transfer is independently green on the
pinned lavapipe host: 200 reads from an 8K buffer for a 64x64 region measured
p50 1,087,579 ns and p95 1,402,461 ns, with 16,384 bytes per frame and exact
checksum 1,474,560. The remaining blocker is producing and timing the complete
Simple backend executable, not the rectangle transfer primitive itself.

## 2026-08-12 strict-JIT refresh

The deployed runtime now registers `rt_struct_receiver_valid`. A second JIT
failure exposed two same-named `Engine2DReadback` classes with different field
layouts: the `gc_async_mut` declaration contained `device_identity`, while the
`nogc_async_mut` mirror did not. The mirror now has the same field and an
explicit identity constructor. Its focused ABI contract passes 2/2.

With `SIMPLE_JIT_STRICT=1` and the pinned lavapipe ICD, the benchmark now gets
through JIT compilation without interpreter fallback or the prior multi-GB
interpreter allocation. It stops later with:

```text
VULKAN_8K_RETAINED status=unavailable reason=Vulkan shared session initialization failed: availability
```

The current blocker is therefore Vulkan shared-session availability in the
strict-JIT process. No frame was executed and no 8K/80 claim is valid. The next
investigation must trace provider/runtime availability and device discovery;
repeating the benchmark without changing that state is not useful evidence.

## 2026-08-12 provider-precedence diagnosis

The availability failure was not a lavapipe failure. The deployed executable
exports zero-return Vulkan stubs, while the Vulkan-enabled dynamic runtime
exports a working provider. `default_runtime_provider()` nevertheless placed
the process provider first, so `SIMPLE_RUNTIME_PATH` could not override any
same-named stub. Explicit dynamic modes now precede the process provider; the
default static/process ordering is unchanged. Its focused precedence unit test
passes 1/1.

A uniquely staged Vulkan-enabled runtime and compiler were built without
overwriting shared artifacts. The next strict benchmark compilation exposed a
separate provider-closure gap:

```text
unresolved external symbol 'rt_process_run_owned_bounded_value'
```

That process owner is implemented in `src/runtime/runtime_process_owned.c` but
is absent from both the staged executable and Rust dynamic provider. Therefore
the benchmark again executed no frame. The next admitted runner must compose
the Vulkan Rust provider with the canonical C hosted-runtime provider (or link
the process owner into the executable) and prove the exact combined provider
hashes before performance evidence is accepted.

## 2026-08-12 execution closure

An isolated preload of the existing canonical process-owner source closed the
missing symbol without editing its concurrently owned build integration. The
Vulkan runner then initialized lavapipe and executed 8K compute work. Full
mirror seeding required bounded transfers: one 132.7 MB read failed, a 31.5 MB
packed strip crashed, and exact 1.97 MB strips completed the run with exit 0.

The remaining evidence blocker is now capture quality, not frame execution:
ordering trace flooded the bounded command output before the final timing row.
No numeric 8K/80 conclusion is permitted until a fresh session captures the
single receipt row with trace disabled. Do not rerun in this session; the
three-cycle verification cap has been reached.
