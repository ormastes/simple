# Tracked self-hosted release artifact links a stale `rt_env_set` ABI

The tracked full pure-Simple CLI under `release/` crashes before parsing
`check` input and before `native-build` reaches user code. The defect is an
artifact/runtime ABI mismatch, not a dropped Simple call argument. It must not
be confused with a current shared `bin/simple` deployment that identifies
itself as the Rust bootstrap seed.

## Symptom

Both a tiny `check` and `native-build` reach glibc `setenv` with a small integer
as its value pointer and exit 139.

## Root cause

The tracked full CLI artifact at
`release/x86_64-unknown-linux-gnu/simple` is SHA-256
`04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`
(Build ID `545d912c...`). Its caller correctly expands both `text` arguments to
the current four-register ABI:

```text
rt_env_set(key_ptr, key_len, value_ptr, value_len)
```

Disassembly of the linked `rt_env_set`, however, shows the obsolete two-argument
implementation. It forwards `%rsi` directly as the second `setenv` argument.
For `SIMPLE_BOOTSTRAP_EXPR_COUNT`, `%rsi` is the key length, 27 (`0x1b`), so
glibc calls `strlen(0x1b)` and faults:

```text
__strlen_avx2
  <- __add_to_environ(name="SIMPLE_BOOTSTRAP_EXPR_COUNT", value=0x1b)
  <- rt_env_set
  <- frontend__core___AstExpr__nodes__expr_count_set
  <- frontend__core___Ast__module_state__ast_reset
  <- cli__check___check_path
```

Current `src/runtime/runtime_native.c`, `src/runtime/runtime.h`, and the current
Rust bootstrap runtime all use the correct four-argument ABI. Do not patch
`expr_count_set`, `env_set`, or font code around this stale deployed artifact.

## Rebuild findings

A 2026-07-14 cache-isolated rebuild from current pure-Simple sources established
two later, separate blockers:

1. Stage 2 rejected `src/compiler/50.mir/mir_instructions.spl:588` while using
   the older bootstrap parser (`unexpected token in class body`).
2. Direct Stage 4 reached the linker, then failed because the corrected full-CLI
   closure and selected runtime archive disagreed on both optional integrations
   (SQLite, HTTP, ROCm, oneAPI, OpenGL, SDL2, memtrack, and Cranelift SFFI) and
   core/generated symbols (`rt_file_create_excl`, `rt_file_sync`,
   `rt_crc32_text`, `rt_write_u32s_to_raw`, DirectX constant conversion, and
   `DoubleEndedIterator.rfind`).

The existing focused `src/app/cli/test_entry.spl` shard was also attempted once
with an isolated cache. It remained at one full CPU for 20 minutes after
emitting advisory diagnostics, produced no object/cache artifact, and was
stopped by the session budget guard. Its retained log is a local build artifact,
not release evidence.

Static dependency review then found that the supposedly lightweight entry
imported broad command, CLI utility, and I/O hubs. It now imports only the
zero-import CLI/environment SFFI owners, calls the runtime fault controls
directly, and `run_commands` no longer imports its own re-export hub.

Three bounded follow-up build cycles produced no executable. The first was
stopped before object output after the remaining broad imports were identified.
The next two reached MIR setup and failed loudly with `bootstrap entry HIR
module was not set before MIR lowering`, including after normalized value-based
map selection. The entry HIR is now retained explicitly in `CompileContext` at
the point where HIR lowering already knows the entry, avoiding rediscovery
through the seed-fragile HIR dictionary. This source fix and its regression have
bounded static review, but the three-cycle cap was reached before native proof.

A later one-shot proof used the newest available pure-Simple stage-55 driver,
the repaired narrow test entry, an isolated cache, one worker, and a 30-minute
hard timeout. It stayed CPU-active, reached about 31.8 GiB RSS, emitted no log,
cache file, object, or candidate, and exited 124 at the outer timeout. Therefore
the explicit entry-HIR repair remains statically approved but runtime-unproven;
this attempt was not retried.

## Current strict-stage result

A fresh 2026-07-14 `--full-bootstrap --backend=cranelift` cycle rebuilt the
bootstrap producer and runtime from current inputs, then completed both strict
pure-Simple stages with no seed fallback:

- Stage 2: `a6fbc3948a06f87ea098444a292017e66b19cfe16363a5f82afb86e2f37b3cf8`
- Stage 3: `e71f8065f817a13cfb1bc52f02ace974005747d0a036fc2524452931e0b712b5`

Both executables are retained under `build/font-req015-bootstrap/`. The first
Stage 4 attempt then failed before codegen because `std.env.platform` locally
redeclared `rt_process_run` already owned by `std.env.types`. `platform.spl`
now imports the canonical owner instead; the focused regression locks that
single-owner contract. The next Stage 4 attempt passed package discovery and
object generation, proving that ambiguity fixed.

The final allowed retry reached the full-CLI linker and failed on the broader
runtime-provider closure. The module closure contains hosted SQLite/HTTP,
CUDA/ROCm/oneAPI/OpenCL/OpenGL/SDL2, Engine2D SIMD/host-queue, font rasterizer,
memtrack, database durability, and related extern surfaces without a matching
provider set. No full CLI was produced. The three-cycle session cap was reached,
so the retained Stage 2/3 compilers and object cache are the recovery point for
the next focused runtime-provider/entry-reachability fix.

## Source regeneration hazard fixed

The SFFI workspace generates its `sffi_io` crate from
`compiler.tools.sffi_gen.specs.io_full`. That canonical spec and its app mirror
still described `rt_env_get` and `rt_env_set` as NUL-terminated pointer-only
calls. Regenerating the crate could therefore reintroduce the same obsolete ABI
even though `simple_sffi.h` and the current Rust runtime use length-delimited
text.

Both specs now generate `(ptr, len)` text parameters, validate the same 4,095
byte key and 65,535 byte value ceilings as the runtime, accept the canonical
zero-length value, and reject invalid names, null non-empty values, embedded
NUL, or invalid UTF-8. `io_env_text_abi_spec.spl` locks the generated signatures
and mirror contract.
This closes the regeneration path; it does not make any retained full CLI a
valid candidate or resolve the separate full-entry runtime-provider closure.

## Required fix and gate

Use a retained strict Stage 2 or Stage 3 pure-Simple compiler, make the full CLI
entry closure and selected runtime bundle agree on their reachable SFFI
surface, then build one full pure-Simple CLI. The bootstrap wrapper must refuse
a Rust-seed fallback for this Stage 4/deploy lane. Before replacement, the
candidate must pass:

1. disassembly or an executable probe proving four-argument `rt_env_set`;
2. `check` on the tiny existing `p2_add.spl` redeploy fixture;
3. `scripts/check/cert/redeploy_gate/redeploy_gate.shs`;
4. the normal deployed `test` and `native-build` smoke gates.

The Rust seed remains bootstrap-only and is not verification evidence.

## 2026-07-15 source-matched admission result

A fresh strict Cranelift bootstrap completed Stage 2 and self-hosted Stage 3
without a SIGSEGV or seed fallback. The first candidate exposed a separate
bootstrap CLI contract bug: explicit-entry native builds forwarded an invalid
`--mode` into the provider instead of returning the full CLI's bounded
diagnostic. `bootstrap_main.spl` now validates that shared command contract.
The rebuilt Stage 3 candidate
`1764d74b2ff77f558b07cdf27a041d5e3e96824a7ef4b563151a6c29ba7a6816`
passed `simple_binary_is_valid`, including the isolated Cranelift `p2_add`
build/run and five-second invalid-mode probe. This resolves the focused
candidate-admission crash; it does not deploy a full CLI or close the separate
Stage 4 provider-composition work.

## 2026-07-16 test-runner admission result

At repository revision `0bfc5c9c22e2fa2e6cdaa1d65f89efc3fc5e2702`, the
tracked release artifact still has SHA-256
`04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`.
This focused command exited 139 before runner discovery:

```text
bin/release/simple test --help
```

GDB recorded `__strlen_avx2 -> __add_to_environ -> rt_env_set ->
io.env_ops.env_set -> cli main`, with key `SIMPLE_TEST_DEPTH` and value pointer
`0x11`. The value is the 17-byte key length forwarded by the obsolete
two-argument implementation; it is not evidence of broken string interpolation.

The retained pure-Simple candidate
`build/pure-cli-current/full-seed-refresh/x86_64-unknown-linux-gnu/simple`
(SHA-256 `dbf2718a6c12a0020649de5b6b2df395a10beefc7cd4e67705d8c59f7b070a34`)
did not crash on the distinct one-file `--list --no-session-daemon
--no-session-share --no-cache --no-cover-check` probe, but exited 1 through the
recursion guard before runner output. Its symbol table contains the CLI main but
no `test_runner_new` main symbol, so it is not an admitted runner either.

One canonical recovery attempt ran:

```text
env SIMPLE_NO_STUB_FALLBACK=1 scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy --no-mcp --jobs=min
```

The Rust bootstrap refresh completed, then strict Stage 2 failed on 39 LLVM
codegen files (primarily incorrect call arity and undeclared lowered symbols),
recorded in
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`.
Strict fallback refusal worked and no replacement was deployed.

## 2026-07-16 unique test-runner entry repair

The recursion-guard candidate contained the CLI `main` symbol but no
`test_runner_new` entry symbol. The CLI imported the runner's generic `main`
under an alias, and the self-hosted entry closure rebound that call to the CLI
entrypoint after `SIMPLE_TEST_DEPTH=1` was set. The runner now exposes the
unique `run_test_cli` entry, used by both the unified CLI and the standalone
runner wrapper; the focused source contract rejects the ambiguous alias.

The current pure-Simple compiler semantically accepted all three production
files. A bootstrap-native link also resolved
`test_runner_new__test_runner_main__run_test_cli`, confirming that the runner
entry is retained. Runtime calibration remains pending: the self-hosted
standalone build reached its ten-minute cap without an artifact, while the
bootstrap link cannot provide the hosted-only runner symbols because current
native-build accepts only `simple-core` or `core-c-bootstrap`. No binary was
deployed and no runner PASS is claimed.

The focused `font_evidence_runner.spl` no longer embeds `interpret_file` and its
full compiler closure. It builds only the shared result wrapper and invokes the
explicitly selected pure-Simple child binary with `run`, preserving the same
fail/empty calibration markers while making a small standalone runner build
possible. The process owner preserves argv boundaries on Windows through the
existing runtime API; the runner preserves stderr and distinguishes launch
failure from an explicit timeout marker.

## 2026-07-16 focused runner closure reduction

The focused runner now requires `<pure-simple-bin> <spec.spl>` and uses the
app-owned process facade. Its native entry closure resolved only the CLI, file,
result-wrapper, and process owner modules; it no longer imports the compiler or
full test orchestrator. The current retained self-hosted compiler nevertheless
remained CPU-bound for five minutes without a diagnostic or output binary, so
the third bounded build cycle was stopped. No runner artifact or fail/empty
calibration PASS is claimed; resume only with a newer admitted pure-Simple
compiler/runtime.

## 2026-07-17 test-runner crash and bounded recovery

The retained release binary still exits 139 even for `test --help` because its
linked `rt_env_set` is the stale two-argument implementation described above;
no test-runner or daemon process remains afterward. Current source ABI remains
correct, so the fix is rebuild/redeploy rather than a caller workaround.

Two Rust process owners also violated the pure runner's polling contract: a
live child must return `-2`, remain tracked, and be reaped after kill. Rust
native returned `-1` at deadline, while the Rust interpreter ignored the
deadline and blocked. Both owners now share `-2` timeout semantics and focused
spawn/wait/kill tests. Until redeploy, the seed's existing
`SIMPLE_TEST_RUNNER_RUST=1` path is explicitly available only as bounded,
redirected repair evidence; normal `simple test` remains pure-Simple.

The next bounded bootstrap exposed Stage 4 parsing of unparenthesized custom
literal dictionary iteration in `UnifiedRegistry`. Commit `0dcb8e7a397`
replaced that tuple form with the compiled-safe `.keys()` plus indexed lookup
already used by compiler dictionaries and added a focused source regression.
An isolated Stage 2 native build parsed and linked the registry, but this is
source-only repair evidence: it produced no admitted full CLI, runner
calibration, or font acceptance PASS.

## 2026-07-23 candidate admission hardening

The retained release artifact still exits 139 on the first `simple test`
environment write; no redeploy was attempted. Candidate admission now executes
a bounded, self-pinned `-c` probe that calls `rt_env_set(text, text)` and requires `true`
before native-build admission. This directly rejects the obsolete two-argument
runtime owner without depending on test discovery or a platform disassembler.
The probe runs through the shared Stage4 admission helper on Linux, macOS,
Windows shell jobs, and FreeBSD. Its shell self-test includes a stale-ABI fake
that passes `--version` but exits 139 on the environment call. A fresh full CLI
and the existing redeploy gates are still required before replacement. The
macOS matrix now installs the helper's `gtimeout` provider, and both admission
and portability changes trigger the canonical FreeBSD workflow. This is a
hosted ABI gate; ARM32/RV32/Windows-ARM64 object receipts are not runtime
environment evidence.
