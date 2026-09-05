# Tracked self-hosted release artifact links a stale `rt_env_set` ABI

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

> **STATUS 2026-08-06: still OPEN — re-confirmed by disassembly and probe.**
> The `04a38e21…` artifact is still present at
> `release/x86_64-unknown-linux-gnu/simple` and still SIGSEGVs on `check` and
> `test --help`. Do NOT confuse it with
> `bin/release/x86_64-unknown-linux-gnu/simple` — a *different* file (`c026a806…`)
> holding a Rust bootstrap seed copy, tracked in
> `deployed_bin_simple_still_seed_2026-08-05.md`.
> The 2026-08-06 lane D1 sections at the end contain a **RETRACTION** of an
> earlier, incorrect "closed by supersession" claim, plus a new hazard: this
> binary exits 0 on `--help`-shaped capability probes.

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

### Bootstrap-candidate scope correction

`bootstrap_main.spl` deliberately has no inline `-c` command. Placing the ABI
probe in generic `candidate_frontend_smoke` made every valid Stage2/3 sanity
check fail after its native fixture had already passed. The unchanged `-c`
probe now runs only in `simple_binary_is_valid`, which admits full CLI
candidates. Generic Stage2/3 smoke remains version plus the bounded native p2
build/execute path; that path uses the bootstrap entry-closure environment
owner and therefore still fails if its own environment ABI is unusable.
`check-bootstrap-portability.shs` passes with this corrected scope. The broad
host-GPU self-test was killed before its aggregate marker and is not claimed as
evidence.

## 2026-07-23 isolated incremental rebuild blocker

A strict isolated `--pure-simple --full-cli --no-mcp --backend=cranelift`
attempt stopped before Stage 2 because the available Rust seed/runtime stamp
does not match current Rust inputs. Full-CLI bootstrap correctly refuses the
stale compiler-backfill archive; three bounded cycles established missing
local prerequisites first, then the genuine stamp mismatch. No cache or
candidate was admitted.

The scoped run explicitly forbids `--full-bootstrap`, so do not bypass or
rewrite the stamp. A fresh seed/runtime/backfill build outside this pure-Simple
lane is required before the incremental Stage 2–4 pipeline can produce the
candidate needed for the existing `rt_env_set` admission probe.

## 2026-07-25 release-wrapper trust guard

A concurrent/manual artifact placed a Rust bootstrap seed at the release
launcher's preferred executable path. The full candidate admission helper
would reject its identity, but the launcher previously trusted any executable
at that path and dispatched normal tooling to the seed.

`bin/release/simple` now runs a five-second identity probe and rejects empty,
failed, Rust-seed, or debug identities before normal dispatch. The explicit
re-entry seed delegation used by the VHDL recursion guard remains unchanged.
The wrapper integration test covers pure argument forwarding, seed rejection
without payload execution, and a missing runtime.

This prevents an invalid artifact from masquerading as production tooling. It
does not repair the tracked stale `rt_env_set` ABI or replace the required
fresh Stage4 build, full candidate admission, and atomic deployment.

## 2026-07-29 browser verification blocker confirmation

The browser-hardening lane reconfirmed the tracked artifact identity without a
bootstrap or Rust-seed fallback:

- SHA-256: `04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`
- Build ID: `545d912cac46001892de0d9959e6b0b92497f2b9`
- focused GDB path:
  `__strlen_avx2 -> __add_to_environ -> rt_env_set -> expr_count_set ->
  expr_reset -> ast_reset -> _check_path`
- valid call registers immediately before `rt_env_set`:
  key pointer, key length `27`, value pointer, value length `1`

The linked provider still forwards the second register as the `setenv` value,
while both retained pure-Simple Stage 2/3 binaries under
`build/browser-full-refresh/` contain the current four-argument Rust provider.
Current source already has the four-argument native, simple-core, generated
SFFI, and admission contracts, so no caller/compiler workaround is justified.

Do not rerun the crashing release check. Resume only after a new full
pure-Simple candidate exists, then run the existing four-argument environment
admission probe followed by the tiny `p2_add.spl` check and canonical redeploy
gate listed above. The separate retained Stage-3 streaming-surface crash must
first gain a focused failing regression and a proven owner fix; do not retry
the full entry build merely to rediscover its first-surface SIGSEGV.

## 2026-08-06 lane D1 re-measurement: the stale artifact is GONE

Positive capability probes on every candidate compiler on disk:

| path | sha256 (16) | `--version` | `native-build --target ... --help` |
|---|---|---|---|
| `bin/release/x86_64-unknown-linux-gnu/simple` | `c026a806af3cf0a9` | **"bootstrap seed only"** | rc=0, full banner |
| `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple` | `bed40ba33a43347a` | `simple-bootstrap 1.0.0-beta` | **rc=0, full banner** |
| `bootstrap/stage{1,2,3}/…/simple` (all four the SAME file) | `48a12b4f8fe2208e` | `simple-bootstrap 1.0.0-beta` | **rc=139 (core dump)** |
| `bin/release/x86_64-unknown-simpleos/simple` | (payload) | n/a | rc=139 |

**RETRACTION.** An earlier draft of this section claimed the `04a38e21…`
artifact was "no longer on disk anywhere" and that this bug was closed by
supersession. **That was wrong, and it was wrong because the ground-truth table
above enumerated only `bin/release/…` and missed the top-level `release/`
directory this bug is actually titled after.** `release/` is a real directory,
not a symlink to `bin/release/`. Corrected row:

| path | sha256 | `--version` | `check` / `test --help` |
|---|---|---|---|
| `release/x86_64-unknown-linux-gnu/simple` | **`04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`** | `Simple v1.0.0-beta` | **rc=139 (SIGSEGV), both** |

Re-disassembled 2026-08-06 — the obsolete two-argument implementation is still
linked, forwarding `%rsi` (the key LENGTH) straight into `setenv`'s value slot:

```text
0000000002af5a47 <rt_env_set>:
  test %rdi,%rdi ; je ...
  test %rsi,%rsi
  cmovne %rsi,%rax
  mov  %rax,%rsi          <-- key length becomes setenv() value pointer
  mov  $0x1,%edx
  call setenv@plt
```

**This bug remains OPEN.** The correct verdict is: a stale ARTIFACT, still
present, not a source defect.

1. Two different artifacts exist and must not be conflated.
   `release/x86_64-unknown-linux-gnu/simple` is the original `04a38e21…`
   stale-ABI binary, still SEGVing today.
   `bin/release/x86_64-unknown-linux-gnu/simple` is a *different* file,
   `c026a806…`, a Rust bootstrap **seed** copy — the separate problem tracked in
   `deployed_bin_simple_still_seed_2026-08-05.md`.
2. Source is already correct on both sides of the ABI.
   `src/runtime/runtime.h:649` and `runtime_native.c:7957` declare the
   four-argument `(key_ptr, key_len, value_ptr, value_len)` form. The `.spl`
   callers use either the explicit four-argument extern
   (`70.backend/sffi_minimal.spl:128`, `backend/interpreter_calls.spl:25`) or
   the two-`text` form (`10.frontend/core/_Ast/module_state.spl:24`,
   `decl_nodes.spl:24`) — and this bug's own disassembly already recorded that
   the two-`text` form expands to the same four registers at the call site. So
   no caller or compiler workaround is warranted, and none was made.
3. The live crasher, `bootstrap/stage3/x86_64-unknown-linux-gnu/simple`, is
   **not** this defect: it is stripped and contains **no `rt_env_set` symbol at
   all**. It is also 3.4 MB and byte-identical across `bootstrap/stage1`,
   `stage2` and `stage3` — a tracked placeholder, not three staged compilers.
   Its crash needs its own record; do not attribute it here.

This bug therefore stays OPEN: the fix is still a rebuild/redeploy of
`release/x86_64-unknown-linux-gnu/simple`, gated by the admission checks listed
under "Required fix and gate". Lane D1 did **not** attempt that redeploy — it is
the circular whole-compiler redeploy, and D1's acceptance never required it.

**New hazard this measurement exposed.** The stale `04a38e21…` binary exits **0**
on `native-build --target <triple> --help`, because `--help` returns before any
environment write. So a `--help`-shaped capability probe **cannot** distinguish
it from a healthy compiler; only a command that actually writes an env var (any
`check`, `test`, or real build) faults. Any tool that selects a compiler by
`--help` probe alone can still pick this binary. See the discovery hardening
below.

## 2026-08-06 discovery defect fixed in `scripts/os/simpleos-native-build.shs`

Blocking lane D1 was not the ABI at all but the builder-discovery loop, which
had two independent defects:

1. It took the **first executable** in the glob and then *rejected* it, aborting
   the whole run instead of continuing to the next candidate. Because
   `bin/release/*/simple` is a seed copy today, auto-discovery could never reach
   a working compiler — every legitimate build was forced through the
   `SIMPLE_BUILD_COMPILER` seed route-around, which is exactly what the two
   install-image provenance guards then refuse.
2. Its remaining checks were **fail-open**: only `rc>=128` or output naming
   `--target` was rejected. `bin/release/x86_64-unknown-simpleos/simple` — the
   SimpleOS *payload*, a cross-target ELF — matches the same glob and is
   executable, so it was a live candidate for being selected as the BUILDER.

Discovery is now a **positive capability search**: a candidate is admitted only
by exiting 0 on `native-build --target <triple> --help` *and* printing the
native-build banner including `--runtime-bundle`. Seed identity is skipped and
the loop continues rather than aborting; `build/bootstrap/stage3` and
`stage2` are searched ahead of `release/`. An explicit `SIMPLE_BUILD_COMPILER`
must pass the same capability probe. Measured: stage2 PASS, both `rc=139`
candidates FAIL, seed skipped.

## 2026-08-06 lane D1 result: self-hosted SimpleOS payload produced

With discovery repaired, `sh scripts/os/simpleos-native-build.shs` was run with
`SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1` and **no** `SIMPLE_BUILD_COMPILER`
override. Auto-discovery selected the pure-Simple stage2 by capability probe:

```text
Compiler:  build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple
Build complete: 723 compiled, 0 cached, 0 failed
Time: 91.5s compile + 46.6s link = 138.1s total
Linked (freestanding): bin/release/x86_64-unknown-simpleos/simple (2246 KB)
  via clang --target=x86_64-unknown-elf
```

Independently verified (`readelf -h`, not the script's weaker `file` check):

```text
Class:               ELF64
Data:                2's complement, little endian
Type:                EXEC (Executable file)
Machine:             Advanced Micro Devices X86-64
Entry point address: 0x40000000
```

New stamp, produced by the build (never hand-written):

```text
target=x86_64-unknown-simpleos
entry=src/app/simpleos_tool/main.spl
entry_closure=true
backend=cranelift
compiler=build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple
artifact_sha256=666c19750e7be618f4b18d93413b6ae44c0a5f846b3b5e3d501db96f9148df80
```

`sha256sum` on the artifact matches the stamped digest, and the stamp is newer
than the binary. The previous stamp read
`compiler=/home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap/simple`
(seed), which is exactly what both guards refuse.

Guard status:

- `scripts/os/make_os_disk.shs` `validate_simple_payload_provenance`: **PASS**
  (executed against the real payload; the script's own `--self-test` also
  passes, so the guard is not vacuous).
- `src/os/installer/image_builder.spl` `_validate_simple_binary`: all five
  conditions satisfied — `target=`, `entry=`, `entry_closure=true`, no
  `compiler_rust`/`simple_seed` substring, `backend=cranelift`, ELF class 2 and
  machine 62.

**Scope of the claim.** The builder was **stage2** — the compiler compiled from
Simple sources, non-seed, admitted by positive capability probe. There is no
`build/bootstrap/stage3/*/simple` on disk, so this is *not* a fixpoint-proven
self-host; it is a legitimately non-seed build, which is what the two provenance
guards actually require. Do not read the passing guards as a stage3 fixpoint.

## 2026-08-06 discovery probe hardened against the stale-ABI binary

The first version of the D1 capability probe used only
`native-build --target <triple> --help`. Measured: the stale `04a38e21…` binary
**passes** that probe at rc=0. Discovery therefore now also requires the
candidate to survive a command that actually writes the environment — `check`
on a trivial two-line fixture, which reaches `rt_env_set` via `ast_reset`. Only
a *signal* death (rc>=128) rejects; a non-zero `check` exit is a verdict about
the fixture, not about the compiler's ABI.

Measured discrimination with the final probe:

| candidate | `--help` probe | env-write probe | verdict |
|---|---|---|---|
| `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple` | rc=0 | rc=0 | **PASS** |
| `release/x86_64-unknown-linux-gnu/simple` | rc=0 | **rc=139** | **FAIL** |
| `bin/release/x86_64-unknown-linux-gnu/simple` | rc=0 | rc=0 | PASS probe, rejected by seed identity |

Note the middle row: `--help` alone would have admitted the stale-ABI binary as
a builder. That is the fail-open this hardening closes.

### Payload undefined-symbol check (not covered by either provenance guard)

Neither provenance guard looks past the ELF header, and a SimpleOS target binary
cannot be executed on the host, so a green link is not proof of a complete link.
`nm -u` on the new payload reports exactly three symbols, **all weak** (`w`):
`simpleos_entropy_seed_u64`, `_Z4mainiPPc`, `_Z4mainv`. Weak undefined symbols
resolve to 0 and do not prevent a static link from being well-formed; there are
**no strong undefined symbols**. The build log's `511 unexpected symbol(s)` /
`505 deferred to linker` lines are the freestanding precheck being conservative,
and the linker resolved them.

### End-to-end rerun with the final hardened script

The payload was rebuilt a second time after the env-write probe was added, so
the receipt below reflects the script exactly as it now stands (not an earlier
revision). Discovery again selected stage2 with no `SIMPLE_BUILD_COMPILER`:

```text
Build complete: 723 compiled, 0 cached, 0 failed
Time: 90.0s compile + 48.3s link = 138.3s total
```

Final artifact: `artifact_sha256=58b65147dfff4810a8cf74f674aa8ddf18f977bfe7745957e4122e8421583186`
(matches `sha256sum`; stamp newer than binary). `readelf -h`: ELF64, EXEC,
x86-64, entry `0x40000000`. `nm -u`: 3 weak symbols, 0 strong. Real shell guard:
**PASS**. The build is reproducible in structure (723/0/0 both runs) though the
digest differs between runs, so the payload is not bit-reproducible — worth its
own investigation, not a D1 blocker.

### Family enumeration — sibling scripts still carry the unhardened discovery

D1 fixed `scripts/os/simpleos-native-build.shs` only. The same
compiler-discovery shape exists elsewhere and is **not** fixed; recorded here so
the sweep is not left half-done (these files are owned by other lanes and were
deliberately not edited by D1):

- Same `for candidate in … release/*/simple` glob, so the stale `04a38e21…`
  binary is a live candidate for them:
  - `scripts/check/check-electron-mdi-evidence.shs`
  - `scripts/check/check-simpleos-hardening-evidence-matrix.shs`
  - `scripts/check/check-simpleos-wm-visible-display-evidence.shs`
  - `scripts/check/check-tauri-mobile-mdi-evidence.shs`
- `scripts/os/simpleos-native-build-riscv64.shs:23` is weaker still —
  `COMPILER="${SIMPLE_BUILD_COMPILER:-bin/release/simple}"` with **no** seed
  check and **no** capability probe, so it will silently build its riscv64
  payload with whatever sits at that path, including the Rust seed. Its payload
  would then fail the same two provenance guards.

Follow-up: factor the hardened `is_bootstrap_seed` + `compiler_can_build_target`
pair (identity skip, banner check, and the env-write probe that is the only
check which actually rejects the stale ABI) into one shared helper these scripts
source, rather than re-implementing the fail-open glob in each.

---

## 2026-08-17 re-verification (wave_01 lane H3) — REPRODUCED, still OPEN

Artifact identity confirmed unchanged — same SHA-256 the report names:

```
$ ls -la release/x86_64-unknown-linux-gnu/simple
-rwxrwxr-x 1 ormastes ormastes 42477824 Aug 11 22:10 simple
$ sha256sum release/x86_64-unknown-linux-gnu/simple
04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0  release/x86_64-unknown-linux-gnu/simple
```

Crash reproduced directly (rc read on the line AFTER the command, never through
a pipe):

```
$ nice -n 19 timeout 120 release/x86_64-unknown-linux-gnu/simple test --help ; echo rc=$?
Segmentation fault (core dumped)
rc=139
```

The 2026-08-06 hazard note is also re-confirmed: a `--help`-shaped capability
probe can still exit 0 on this artifact, so exit status alone does not detect it.

```
$ nice -n 19 timeout 120 release/x86_64-unknown-linux-gnu/simple --version ; echo rc=$?
rc=0
Simple v1.0.0-beta
```

That asymmetry is the trap worth restating: `--version` succeeds, `test --help`
dumps core. Anything that probes this binary with `--version` and concludes
"healthy" is wrong.

**Root cause locus: none in current source.** This is a stale *binary artifact*
carrying an obsolete two-argument `rt_env_set` ABI, not a defect reachable by
editing a `.spl` or `.rs` file today. Current source is not implicated by the
crash, and no source edit can clear it.

**Why no fix landed here:** the only remedy is rebuilding and redeploying the
tracked `release/` artifact against the current four-register `rt_env_set` ABI.
This lane is explicitly forbidden to rebuild or redeploy any binary, and a
bootstrap owning the box was live throughout. Recorded as reproduced-and-blocked
rather than fixed. Status remains OPEN (P1).

**Not proven by this lane:** that a fresh build of current source produces a
correct four-argument `rt_env_set` call sequence. That claim needs the redeploy
this lane could not perform, and must not be assumed from the source-side
`rt_env_set` signature alone.
