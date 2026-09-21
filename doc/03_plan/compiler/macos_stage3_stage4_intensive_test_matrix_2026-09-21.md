# macOS Stage 3/Stage 4 intensive test matrix (2026-09-21)

## Authority and order

1. Run `sh scripts/check/check-bootstrap-preflight.shs` against an unchanged
   source checkout.
2. Produce Stage 2 and its typed Stage 3 receipt with the requested build
   concurrency:

   ```sh
   SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
     --full-bootstrap --stop-after-stage2 --strategy=full \
     --produce-stage3-receipt=verify-landed-compiler-fix --jobs=8 \
     --progress=build/bootstrap/macos-stage2.log
   ```

   Retain `selected-build-jobs.env`, the Stage 2 admission, runtime capsule,
   planner receipt, compiler SHA-256, log, wall time, and maximum RSS. The
   requested compile budget is less than 1 GiB maximum RSS; a higher value is a
   resource failure even when compilation exits zero.
3. Execute the exact `--resume-stage3-from-admitted=... --bootstrap-receipt=...`
   command printed by step 2. Do not pass `--jobs=8`: Stage 3 resume accepts
   only omitted `--jobs` or `--jobs=1` and pins the self-host recompile to one
   thread. Follow the emitted admitted continuation into Stage 4; Stage 4
   resume likewise accepts only omitted `--jobs` or `--jobs=1`. Do not mutate
   the checkout or output root while either lane is live.
4. Only after the bootstrap lane releases CPU and memory, run the false-pass
   contract checks, followed by phase verification. `jobs=8` applies to the
   Stage 2 producer. For the verification tool builds, set
   `BOOTSTRAP_VERIFY_BUILD_THREADS=8` only when resource monitoring shows the
   host can keep every compile below 1 GiB; otherwise use the default 4 while
   recording that the Stage 2 jobs requirement was already exercised.

## False-pass contract gates

Run these once, before trusting Phase 3/4 test output:

```sh
sh test/01_unit/scripts/bootstrap_compiler_inventory_discovery_test.shs
sh test/01_unit/scripts/bootstrap_compiler_unit_execution_count_test.shs
sh test/01_unit/scripts/bootstrap_phase_command_owner_test.shs
```

All must print `PASS`. They prove discovery failures cannot admit a partial
inventory, each discovered compiler spec is executed, Stage 3/4 command owners
are receipt bound, zero-output or zero-execution JSON fails, and Darwin uses
the portable loader oracle.

## Canonical phase verification

For both admitted Stage 3 and Stage 4 artifacts, run the following template in
order, substituting immutable paths and a freshly calculated SHA-256. Use a
distinct work root per phase and the admitted hosted runtime authority; never
use the Rust seed, an ambient `bin/simple`, or a mutable Cargo target.

```sh
BOOTSTRAP_VERIFY_BUILD_THREADS=8 \
sh scripts/bootstrap/bootstrap-phase-verification.shs \
  --phase=stage3 \
  --compiler="$STAGE3_COMPILER" \
  --compiler-sha256="$STAGE3_SHA256" \
  --strategy=full --hash-policy=canonical \
  --source-root="$REPO" --runtime-path="$HOSTED_RUNTIME_AUTHORITY" \
  --work-root="$STAGE3_VERIFY_ROOT" --timeout-seconds=7200

BOOTSTRAP_VERIFY_BUILD_THREADS=8 \
sh scripts/bootstrap/bootstrap-phase-verification.shs \
  --phase=stage4 \
  --compiler="$STAGE4_COMPILER" \
  --compiler-sha256="$STAGE4_SHA256" \
  --strategy=full --hash-policy=canonical \
  --source-root="$REPO" --runtime-path="$HOSTED_RUNTIME_AUTHORITY" \
  --work-root="$STAGE4_VERIFY_ROOT" --timeout-seconds=7200
```

The verifier snapshots and hashes the admitted compiler, validates the hosted
runtime authority, then builds SHA-bound full CLI, test runner, MCP, and LSP
binaries. Its frozen command-owner receipt binds the exact compiler snapshot,
runtime identity, CLI, runner, and MCP hashes. Stage 4 additionally requires a
frozen tooling receipt binding the Stage 4 snapshot, runtime, MCP, and LSP.

The `full` matrix covers, in order:

- full CLI/test runner/MCP/LSP native builds;
- `check src/compiler`, `check src/app/mcp`,
  `check src/app/simple_lsp_mcp`, and `check src/lib`;
- compiler bootstrap tests in interpreter and compile modes;
- on Darwin, `module_load_intent_spec.spl` in interpreter and compile modes;
- every `test/01_unit/compiler/**/*_spec.spl`, independently timed and
  terminalized in interpreter mode;
- for Stage 3 and Stage 4, every repository `*_spec.spl` and `*_test.spl` in
  interpreter mode;
- MCP integration in interpreter and compile modes, plus MCP/LSP help probes.

## Authoritative PASS evidence

A phase passes only when its `summary.env` ends with `terminal_failures=0` and
`overall=PASS`. Every focused JSON row must have `executed > 0`, `passed > 0`,
and `failed=0`. Inventory summaries must have nonzero `spec_count`,
`passed_count == spec_count`, and zero timeout/crash counts. All source/test
rows must show command-owner hashes valid before and after; Stage 4 MCP/tool
rows must also show Stage 4 tooling ownership valid before and after. Expected
native artifacts must be regular executable files with recorded SHA-256 values.

Retain each row log, inventory TSV, elapsed time, and `max_rss_kib`. Treat
`UNSUPPORTED`, `BLOCKED`, timeout, crash, absent/non-numeric RSS, missing
artifact, hash mismatch, malformed JSON, skipped-only/zero-execution output,
or an ABI diagnostic in a help probe as failure. Interpreter results are the
semantic ground truth because SMF/compiled modes have known false-green risks;
the compile-mode rows are required differential evidence and do not replace
the interpreter rows.
