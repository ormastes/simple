# Stage 2 native generator: MIR `push` dispatch failure

Status: open; exact Simple call site unknown. No generated binary or test PASS.

## Reproduction evidence

- Frozen product source: `8a55884d4d22cbbe9690c1145a94a2c4bbe7b981`.
- Admitted AArch64 Stage 2 producer SHA-256: `4ddb1bab12de9496fa47eea161ec6b9254ae2853f9958a9da91e6c0cb422418f`.
- Entry: `src/app/compiler_subsystem_product_generator/main.spl`, LLVM native build with 10 threads under the existing memory and time cap.
- The compiler finished HIR 103/103 and entered MIR 0/103, then exited 70: `str.push was called on a receiver that is not text. This method has no compiled implementation for that receiver type -- a code-generation dispatch gap`.
- Durable copied evidence root: `/home/yoon/dev/simple-aggregate-products-integration-20261003/build/aggregate-products-integration/`. `generator-cycle1/native-build.log` is the outer log, `generator-cycle1/native-build-stderr-3537588-1.log` is the full worker stderr, and `generator-cycle1/STATUS.md`, `terminal.env`, and `run-generator-build.sh` record status and invocation. The original `/run/user/1000/simple-aggregate-generator-native-20261003/` files are temporary diagnostic artifacts, not permanent CI receipts.

The error comes from the producer runtime's `rt_push` in `src/compiler_rust/runtime/src/value/collections.rs:3476-3484`. It handles a typed array or text receiver and rejects other receiver kinds. `src/compiler_rust/compiler/src/codegen/instr/calls.rs:3713` selects `rt_push` by method name. These facts identify the failing runtime dispatch, **not** the Simple source expression or a proven repair. The generator's array `output_rows.push` cannot be named the culprit from this evidence.

## Bounded diagnostic attempts

1. Initial capped native build produced the failure above.
2. A GDB follow-fork attempt followed an incidental `/usr/bin/dash` child and detached from the compiler worker; it did not capture the failure call stack. The detached owned compiler was terminated. Durable copy: `generator-cycle2/gdb.log`, `terminal.env`, `failure.gdb`, and `run-gdb.sh` under the evidence root above. Its GDB process status 0 is not a compiler or product PASS.
3. A worker-wrapper GDB attempt stopped before worker execution with `bootstrap native-build producer mismatch: SIMPLE_BINARY`. Durable copy: `generator-cycle3/build.log`, `terminal.env`, `failure.gdb`, `gdb-worker-wrapper.sh`, and `run-debug-build.sh` under the evidence root above. `src/app/cli/bootstrap_main.spl:144-149` sets `SIMPLE_BOOTSTRAP_INTERNAL_NATIVE_BUILD_ROUTING=1` internally. `src/app/cli/native_build_main.spl:895-910` then validates the selected worker binary through `bootstrap_native_build_producer_binding`; `src/app/cli/native_build_producer_binding.spl:22-35` requires `SIMPLE_BINARY` and `SIMPLE_BIN` to resolve to the invoking compiler executable. The GDB wrapper violated that identity rule.

The three-cycle diagnostic cap is exhausted. **Do not run a fourth build under this investigation.** The MIR caller remains unknown; neither a compiler fix nor a product qualification PASS has been established.

## Future attribution route (design only)

If a new diagnostic candidate is authorized, an opt-in hook after producer identity validation could launch GDB directly on the validated compiler executable with the already assembled `worker_args` at `native_build_main.spl:1033`, preserving `SIMPLE_BINARY` as that executable and the existing policy, timeout, cache, source, and resource constraints. This requires a newly admitted producer; it is not an implemented fix. Attaching from a sibling process is restricted by this host's Yama `ptrace_scope=1`.
