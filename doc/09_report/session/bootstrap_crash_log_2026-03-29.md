# Bootstrap Repro Log 2026-03-29

## Command

```bash
./scripts/bootstrap/bootstrap-from-scratch.sh --output=build/bootstrap-crash-repro
```

## Result

- Exit status: `1`
- First failing stage: `stage2-native-build`
- Stage log:
  - `build/bootstrap-crash-repro/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`

## Bootstrap Script Logging

Bootstrap scripts now write per-stage logs under:

```text
<output>/logs/<platform>/
  rust-seed-build.log
  stage1-native-build.log        # Windows only
  stage2-native-build.log
  stage3-native-build.log
  stage4-native-build.log
```

On failure the script reports the failing stage, exit code, and log path.

## First Repro Finding

This repro did **not** hit the later self-hosted segfault path first.
It stopped earlier in stage 2 on parser incompatibilities while compiling
`src/app/cli/bootstrap_main.spl` transitive dependencies.

Tail of the stage2 log reports:

- `src/compiler/80.driver/build/installer.spl`
  - parse: unexpected comma in grouped `use ... (...)`
- `src/compiler/90.tools/__init__.spl`
  - parse: unexpected comma in export list / `export use`
- `src/compiler/driver/build/installer.spl`
  - parse: unexpected comma
- `src/compiler/tools/__init__.spl`
  - parse: unexpected comma
- `src/lib/nogc_sync_mut/package/installer/backend_fpm.spl`
  - parse: unexpected newline
- `src/lib/nogc_sync_mut/web_ui/dom_backend.spl`
  - parse: unexpected assign token

The final stage2 error summary is:

```text
Build failed: native-build aborted: 4 critical file(s) failed to compile
```

## Likely Meaning

- The stage2 bootstrap compiler/parser does not yet accept some newer source forms
  that the repository currently uses.
- Candidate unsupported forms seen in the failing files:
  - grouped `use module (...)` imports
  - long export lists
  - `export use ...`
  - newer expression/assignment forms in `dom_backend.spl`

## Relevant Source Notes

- Existing repo note for later self-hosted runtime crash:
  - `doc/08_tracking/bug/engine_2d_limitations.md`
  - LIM-010 says `bin/simple_native` / `bin/simple_stage4` can still segfault
    in generic run/check/test flow.

## Next Suggested Debug Order

1. Make stage2 parser-compatible with the current source tree.
2. Re-run bootstrap until stage3/stage4 execute.
3. Only then investigate any remaining self-hosted runtime segfault, using the
   per-stage logs added in this session.

## Progress Update After First Fixes

Applied source compatibility fixes in:

- `src/compiler/80.driver/build/installer.spl`
- `src/compiler/driver/build/installer.spl`
- `src/lib/nogc_sync_mut/package/installer/backend_fpm.spl`
- `src/lib/nogc_sync_mut/web_ui/dom_backend.spl`
- `src/compiler/90.tools/__init__.spl`
- `src/compiler/tools/__init__.spl`

Re-run command:

```bash
./scripts/bootstrap/bootstrap-from-scratch.sh --output=build/bootstrap-crash-repro3
```

Observed behavior:

- The original stage2 parser abort no longer reproduces.
- Stage2 now progresses into a much longer codegen phase.
- Bootstrap logs were further tightened so stage2/stage3/stage4 inherit
  `RUST_LOG=error`, preventing multi-hundred-megabyte Cranelift info logs.
- The `build/bootstrap-crash-repro3` run captured so far was terminated by the
  session timeout rather than a deterministic compiler crash, so the next step
  is a longer unattended run or a narrower stage2 repro around the emitted
  `[CODEGEN-WARN]` incompatibility warnings.

## Milestone Reached: Stage3 Verification Passes

Longer repro command:

```bash
./scripts/bootstrap/bootstrap-from-scratch.sh --output=build/bootstrap-crash-repro4
```

Observed output:

```text
stage2 sha256: b46dd1d226059d9dac9fb5e790ee7a424f9cb687eeddc84027a98bda48c6d74c
stage3 sha256: b46dd1d226059d9dac9fb5e790ee7a424f9cb687eeddc84027a98bda48c6d74c
Bootstrap verification passed.
Stage 4: compiling full CLI (main.spl) with bootstrap compiler...
```

Meaning:

- Stage2 completed successfully.
- Stage3 completed successfully.
- Stage2 and Stage3 hashes match exactly.
- The staged self-hosted bootstrap verifier now passes on this repro.
- Stage4 began successfully.

The remaining termination in this interactive session was:

- `stage4-native-build` exit `143`
- caused by session timeout / external `SIGTERM`, not by a compiler-reported
  internal failure in the captured log.

## Current Status

The original blocker has moved:

- **Resolved in this repro:** stage2 parser incompatibility abort
- **Resolved in this repro:** stage3 self-host verification barrier
- **Not yet proven complete:** full stage4 native build to final CLI binary

The most visible remaining technical signal is a large set of
`[CODEGEN-WARN] Failed to declare cross-module function ...` warnings during
stage2/stage3/stage4. They are not currently preventing stage3 verification,
but they may still affect stage4 completion or runtime correctness and should
be investigated next if a full unattended stage4 run still fails.

## Warning Reduction Pass

To isolate deterministic warning sources, a direct stage2 build was run with:

```bash
env RUST_LOG=error \
  src/compiler_rust/target/bootstrap/simple native-build \
  --entry src/app/cli/bootstrap_main.spl \
  --runtime-path /home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap \
  -o build/bootstrap-direct-stage2/simple
```

### Source changes applied

Low-risk symbol collision fixes:

- Renamed local coverage helpers:
  - `src/app/build/coverage.spl`
  - `src/compiler/80.driver/build/coverage.spl`
  - `split_whitespace(...)` -> `split_whitespace_tokens(...)`
- Renamed loader compatibility shim:
  - `src/compiler/99.loader/compiler_ffi.spl`
  - `code_len(...)` -> `code_bytes_len(...)`
  - updated local call sites in:
    - `src/compiler/99.loader/loader/module_loader.spl`
    - `src/compiler/99.loader/loader/smf_mmap_native.spl`
- Renamed Trace32 parser whitespace helper:
  - `src/app/debug/remote/protocol/trace32.spl`
  - `src/lib/nogc_sync_mut/debug/remote/protocol/trace32.spl`
  - `src/lib/nogc_sync_mut/debug/remote/protocol/t32_window_capture.spl`
  - `Trace32Parser.split_whitespace(...)` -> `Trace32Parser.tokenize_whitespace(...)`
- Renamed GDB/MI parser helpers:
  - `src/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi_parser.spl`
  - `parse_key_values(...)` -> `parse_kv_pairs(...)`
  - `parse_tuple_list(...)` -> `parse_tuple_records(...)`
  - updated call sites in:
    - `src/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi.spl`
    - `src/lib/nogc_sync_mut/debug/remote/frame_inspector.spl`
    - `src/lib/nogc_sync_mut/debug/remote/breakpoint_manager.spl`
    - `src/lib/nogc_async_mut_noalloc/qemu/debug_boot_runner.spl`

### Measured result

Before the `code_len` and coverage `split_whitespace` fixes, the completed
bootstrap logs showed:

- `cross_module` warnings: `2224`
- `load_warn` warnings: `314`

After those first collision fixes, a direct stage2 run showed:

- `cross_module` warnings: `2208`
- `load_warn` warnings: `314`

This confirms those two warning families were real collision sources and were
reduced by `16` warnings total.

### Important follow-up result

The later GDB/MI helper renames did **not** eliminate the parser warning family.
Live transcript capture via `script(1)` still showed warnings such as:

- `GdbMiParser.parse_tuple_records`
- `GdbMiParser.parse_kv_pairs`
- `GdbMiParser.parse_class_and_data`

Interpretation:

- `code_len` and `split_whitespace` were name-collision issues and were worth
  fixing.
- The GDB/MI warnings are not caused by the literal helper names.
- They appear to come from a deeper static-method declaration/lowering problem.

### Current best next step

Do not keep renaming static helper methods blindly.

Instead, investigate the compiler/codegen path that emits:

- `Failed to declare cross-module function '...': Incompatible declaration of identifier: ...`

especially for:

- static methods on parser/helper types
- constructor-like methods such as `.new`, `.zero`, `.ready`
- FFI/runtime families like `rt_torch_*`

That should be done in the Rust codegen declaration path rather than in
application/source-level symbol renames.

## Compiler-Side Fix

Applied a compiler change in:

- `src/compiler_rust/compiler/src/codegen/instr/calls.rs`

Change:

- before declaring a cross-module import with a guessed `i64 -> i64` style
  signature, the call path now first checks `ctx.func_ids` for the already
  declared resolved symbol and reuses that `FuncId` if present

Why this matters:

- `declare_functions(...)` already establishes canonical declarations for many
  functions
- the old cross-module fallback path in `calls.rs` ignored that and tried to
  redeclare the same symbol by current call arity
- that is exactly the shape that produces Cranelift
  `Incompatible declaration of identifier` warnings

Validation:

```bash
cargo check -p simple-compiler
```

passed successfully.

Short probe result:

- reran the direct stage2 entrypoint under PTY/script capture
- unlike the earlier probe, the first ~80 seconds did **not** emit the previous
  immediate cross-module warning burst
- the captured transcript contained only the script header/trailer and `^C`
  when the probe was stopped manually

Interpretation:

- this is not yet a full-bootstrap proof
- but it is strong evidence that the compiler-side `func_ids` reuse patch
  suppresses at least the early warning path that had remained after the
  source-level collision fixes

### Important Seed Detail

The first full bootstrap rerun after this compiler patch still showed the old:

- `cross_module = 2208`
- `load_warn = 314`

but that run was still using the stale bootstrap seed binary at:

- `src/compiler_rust/target/bootstrap/simple`

The seed had to be rebuilt explicitly with the same command the bootstrap
script expects:

```bash
cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-driver
```

After that rebuild, `src/compiler_rust/target/bootstrap/simple` updated to the
new timestamp and a fresh direct stage2 probe using the updated seed again ran
for ~75 seconds with:

- `cross_module = 0` in the captured transcript
- `load_warn = 0` in the captured transcript

for the sampled early execution window.

Interpretation:

- the compiler-side `calls.rs` fix was not exercised until the bootstrap-profile
  seed was rebuilt
- once exercised, the patched seed no longer reproduced the old immediate
  warning burst in the short stage2 probe
- the remaining work is to let a full bootstrap run far enough with the updated
  seed to measure the full-stage warning totals and final stage4 behavior

### Qualified Static Method Misresolution

While tracing the remaining repeated warning families, a second compiler-side
resolution bug became visible in the `repro9` stage2 log.

Concrete example:

- warning showed `Document.create`
- resolved symbol was `app__build__package__Package.create`

That can only happen if cross-module lookup prefers the bare method name
`create` over the qualified static method name `Document.create`.

Compiler fix:

- updated `src/compiler_rust/compiler/src/codegen/instr/calls.rs`
- updated `src/compiler_rust/compiler/src/codegen/instr/methods.rs`

Behavior change:

- when resolving dotted/static method calls, the compiler now prefers:
  - `Type.method`
  - `Type__method`
  - `type_method`
  - bare `method` only as the final fallback

Rationale:

- common factory/helper names like `create`, `new`, `zero`, `ready`, and
  parser helpers are reused across many modules
- resolving them by bare method name first can bind a call to an unrelated
  import, which then produces the repeated `Incompatible declaration of
  identifier` warnings seen in bootstrap logs

Validation:

```bash
cargo check --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler
```

passed successfully after the resolver-order change.

Status:

- `build/bootstrap-crash-repro9` is still running and has already reached the
  final stage4 native build
- a fresh bootstrap-profile seed rebuild is also running so the next short
  direct probe can measure the impact of this resolver-order fix separately

### `repro9` Completion

`build/bootstrap-crash-repro9` completed successfully all the way through the
final stage4 native build.

Result:

- final binary linked at
  `build/bootstrap-crash-repro9/full/x86_64-unknown-linux-gnu/simple`
- stage4 still showed the old warning baseline:
  - `cross_module = 2208`
  - `load_warn = 0`

Interpretation:

- `repro9` proves the bootstrap path now completes end-to-end in this repro
- but it is not the correct measurement for the resolver-order patch because
  the run was started before the new seed was rebuilt

### Fresh-Seed Direct Probe After Resolver-Order Fix

After the bootstrap-profile seed was rebuilt again, a direct stage2 probe was
run with:

```bash
env RUST_LOG=error src/compiler_rust/target/bootstrap/simple native-build \
  --source src/compiler \
  --source src/app \
  --source src/lib \
  --entry src/app/cli/bootstrap_main.spl \
  --runtime-path /home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap \
  -o build/bootstrap-direct-stage2-resolverfix-long/simple
```

The process was allowed to run for about 86 seconds before being stopped
manually. The captured PTY transcript contained:

- `cross_module = 0`
- no occurrences of the previously noisy families:
  - `Document.create`
  - `TEST_FUNCTIONS.merge`
  - `BaremetalBuilder.new`
  - `CompilerContext.create`
  - `GcConfig.from_module`
  - `Unifier.empty`
  - `LayerDef.new`
  - `DimensionDef.new`
  - `LayerViolation.new`
  - `NativeLinkConfig.default`
  - `SmfCache.new`
  - `GdbMiParser.parse_tuple_records`
  - `GdbMiParser.parse_kv_pairs`
  - `InputManager.create`
  - `AudioManager.create`
  - `Clock.create`
  - `Trace32Client.connect`

Interpretation:

- the qualified-method resolver fix is exercising correctly in the rebuilt seed
- the old repeated static/helper warning families are no longer appearing in
  the early-to-mid stage2 execution window
- the next required measurement is a full clean bootstrap run started after the
  rebuilt seed so the old `2208` baseline can be replaced with a real full-run
  count

### Full Clean Rebuild With Rebuilt Seed: `repro10`

A full clean bootstrap run was started after the rebuilt seed and resolver-order
patches:

```bash
./scripts/bootstrap/bootstrap-from-scratch.sh --output=build/bootstrap-crash-repro10
```

Result:

- `stage2` completed
- `stage3` completed
- `stage4` completed
- final binary linked successfully

Measured warning totals:

- `stage2-native-build.log`
  - `cross_module = 2189`
  - `load_warn = 0`
- `stage3-native-build.log`
  - `cross_module = 2208`
  - `load_warn = 0`
- `stage4-native-build.log`
  - `cross_module = 2208`
  - `load_warn = 0`

Interpretation:

- the resolver-order and import-reuse fixes are real: they reduced the first
  seed-driven stage by 19 warnings relative to the old `2208` baseline
- but the self-hosted path reintroduces those 19 warnings in `stage3` and keeps
  them in `stage4`

The exact `stage3 - stage2` delta is 19 warnings, all from the previously known
family:

- `is_little_endian` x2
- `MCP_T32_FIELD_DICT.set` x1
- `MCP_T32_FIELD_DICT.delete` x1
- `upgrade` x1
- `types.locale_equals` x1
- `types.is_valid_language_code` x1
- `types.is_valid_region_code` x1
- `types.is_valid_locale` x1
- `NativeTensor.rand` x1
- `TorchTensor.rand` x1
- `NativeTensor.eye` x1
- `TorchTensor.eye` x1
- `NativeTensor.arange` x1
- `TorchTensor.arange` x1
- `NativeTensor.linspace` x1
- `TorchTensor.linspace` x1
- `NativeTensor.logspace` x1
- `TorchTensor.logspace` x1

Important observation:

- the large repeated families such as `InlineAsm.new`, `GdbMiParser.parse_*`,
  `LayerViolation.new`, `CompilerContext.create`, `BaremetalBuilder.new`, and
  related static/helper calls are still present in both `stage2` and `stage3`
  at the same counts
- so the 19-warning improvement is narrow and specific; the broader repeated
  warning problem still remains

Current diagnosis:

- the Rust seed compiler path now contains fixes that remove the 19-warning
  family in `stage2`
- the self-hosted compiler path used by `stage3` is still missing the equivalent
  behavior, so those warnings return once the newly built compiler takes over
