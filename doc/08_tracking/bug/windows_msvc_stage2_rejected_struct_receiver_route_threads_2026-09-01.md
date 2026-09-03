# Windows MSVC Stage 2 builds and links, then is REJECTED by the struct-receiver probe

**Date:** 2026-09-01
**Status:** Open — Stage 2 candidate rejected; admission not achieved
**Lane:** `x86_64-pc-windows-msvc`, output `/d/simple_build/bootstrap-msvc`

**Command:**

```
. scripts/setup/windows-msvc-bootstrap-env.shs
sh scripts/bootstrap/bootstrap-windows.sh --msvc --full-bootstrap \
   --stop-after-stage2 --output=/d/simple_build/bootstrap-msvc
```

**Result:** `BOOTSTRAP_EXIT=1`, milestone `exit-1`, elapsed ~2200 s.

## How far it got — further than any recorded Windows MSVC run

Everything up to and including the Stage 2 native build succeeded:

```
Build complete: 818 compiled, 0 cached, 0 failed
  Binary: D:/simple_build/bootstrap-msvc/stage2/x86_64-pc-windows-msvc/simple.exe (105676 KB)
  Time: 651.8s compile + 30.1s link = 681.9s total
```

(`logs/x86_64-pc-windows-msvc/stage2-native-build.log`; linked via `clang-cl`.)

`Stage 2: running bootstrap compiler sanity` also passed, and inside the
capability probe the struct-receiver check itself passed:

```
bootstrap_stage2_struct_receiver=PASS
```

## The failing gate

`bootstrap-from-scratch.sh:2593-2626`, "Stage 2: proving struct receiver/runtime
capability", exit **3**. The probe
(`scripts/check/check-bootstrap-stage2-struct-receiver.shs`) has a *second* half
after the struct-receiver check — the positional pure-Simple Stage-3 route at
lines 150-168 — and that is what failed:

```
error: stage2 failed the positional pure-Simple Stage-3 route (status 2)
Error: --threads requires a positive integer

error: native-build worker exited with code 2.
  interpreter: D:/simple_build/bootstrap-msvc/stage2/x86_64-pc-windows-msvc/simple.exe (exit code 2)
```

(`stage3/x86_64-pc-windows-msvc/stage2-receiver.log`, last lines.)

Evidence written by the pipeline itself:

```
# stage3/x86_64-pc-windows-msvc/stage2-receiver.env
schema=simple-bootstrap-stage2-receiver-evidence-v1
status=fail
probe_exit=1
candidate_sha256_before=66bbe02685bb54eb1a4b90506acde08d0321818c5030d83f106af5bae6219123
candidate_sha256_after=66bbe02685bb54eb1a4b90506acde08d0321818c5030d83f106af5bae6219123
runtime_snapshot_sha256=ad79bc36bfb8ac0803c3dd2e795dbb0707bb902d432429b7e24f692b89e9b844

# stage2-rejected/x86_64-pc-windows-msvc/rejection.env
schema=simple-bootstrap-rejected-stage2-v1
status=rejected
reason=stage2-struct-receiver-failed
candidate=/d/simple_build/bootstrap-msvc/stage2-rejected/x86_64-pc-windows-msvc/simple.exe
candidate_sha256=66bbe02685bb54eb1a4b90506acde08d0321818c5030d83f106af5bae6219123
```

The candidate binary sha256 is **unchanged** across the probe and the frozen
runtime snapshot compared equal, so the rejection is purely the probe exit
status — not a mutated artifact and not a disturbed runtime authority.

## Lead: the Stage 2 bootstrap CLI has no `run` command, but the worker spawn uses one

`run_native_build_worker` (`src/app/cli/native_build_main.spl:584`) builds

```
var worker_args = ["run", "src/app/cli/native_build_worker.spl"]
... then appends every native-build arg verbatim ...
```

and spawns `simple_bin` with it. Stage 2 is built from
`src/app/cli/bootstrap_main.spl`, the BOOTSTRAP cli, which exposes only
`compile` and `native-build`. Measured directly against the rejected candidate:

```
$ /d/simple-tmp/stage2-probe.exe run src/app/cli/native_build_worker.spl --threads 1 -o out hi.spl
error: unknown command 'run'
rc=1
```

So on this route the parent hands its own binary a subcommand that binary does
not have. The observed `Error: --threads requires a positive integer` is
consistent with the argv being re-dispatched through a path where `--threads`
lands without its following value (`src/app/io/_CliCompile/compile_targets.spl:670-677`
emits exactly that text when `j + 1 >= args.len()`), but the precise re-dispatch
has **not** been pinned and this hypothesis is **not** confirmed. A plain
`native-build --threads 1 ...` against the same binary does **not** reproduce it
— it proceeds to build — so the trigger involves the direct-Stage-3 route
environment (`SIMPLE_BOOTSTRAP_STAGE3_REQUESTED_ROUTE=direct`,
`SIMPLE_BOOTSTRAP_STAGE3_FALLBACK_ROUTE=none`), not the flag alone.

**Instrumentation lever:** the worker runs from SOURCE under the interpreter, so
probes can be added to `src/app/cli/native_build_worker.spl` and
`src/app/io/_CliCompile/compile_targets.spl` with no rebuild — a `src/lib`/`src/app`
edit needs no build step. Dumping the received argv at worker entry settles the
hypothesis in one run.

## Second, separate defect: the failure was reported as UNDIAGNOSABLE

The main log says:

```
  diagnosis: the log has content (81573 bytes) but NOT ONE line matching
             any diagnostic pattern. Counts and progress without a reason.
  UNDIAGNOSABLE: the stage failed with no error message of any kind.
FAIL — 1 check(s), stage stage2 failed (exit 3) with NO diagnostic text
```

This is wrong, and dangerously so: the reason **was** written, to
`stage2-receiver.log`. `check-stage-log-diagnosable.shs` is handed only
`--log <stage2-native-build.log>` (`bootstrap-from-scratch.sh:2738-2741`), and
that log legitimately ends in a clean `Build complete: 818 compiled, 0 failed`
because the build genuinely succeeded — the failure happened afterwards, in the
probe. The stage-3 exit path must point the diagnosability check at the probe
log that actually holds the error, or it will keep declaring diagnosable
failures undiagnosable and send the next investigator hunting a phantom.

## Unblock condition

1. Confirm the argv the worker actually receives on the direct Stage-3 route
   (source-level print; no rebuild needed).
2. Fix whichever side is wrong — the `["run", worker.spl]` spawn against a
   bootstrap CLI that has no `run`, or the arg re-dispatch that loses the
   `--threads` value.
3. Re-run the same command. The success verdict is the literal line
   `Stage 2 admitted; stopping before Stage 3 as requested.` with exit 0 and an
   existing `stage3/<platform>/stage2-admitted/admission.env`.

Phase 3 (W2) cannot start until then: there is no admitted Stage 2 to produce it.

## Cross-platform impact

None from this record — it is a diagnosis, not a change. The environment fixes it
depended on live in the Windows-only `scripts/setup/windows-msvc-bootstrap-env.shs`
(see `windows_msvc_stage3_tool_authority_path_missing_shasum_2026-09-01.md`); no
Unix branch was touched.

## Narrowed by direct experiment (2026-09-01, after the first filing)

The hypothesis in the section above is now **partly confirmed and partly
refuted**. All measurements below use the rejected candidate itself, copied to
`/d/simple-tmp/stage2-probe.exe` (sha256 `66bbe026…`), and take seconds — this
blocker no longer needs a 37-minute bootstrap to reproduce.

### Standalone reproduction

```
sh scripts/check/check-bootstrap-stage2-struct-receiver.shs \
   /d/simple-tmp/stage2-probe.exe <lane>/stage2-runtime-authority \
   x86_64-pc-windows-msvc llvm
-> PROBE_RC=1, same two lines: struct receiver PASS, then
   "error: stage2 failed the positional pure-Simple Stage-3 route (status 2)"
   "Error: --threads requires a positive integer"
```

### Minimal reproduction — one command, ~1 second

```
env SIMPLE_NATIVE_BUILD_WORKER=1 /d/simple-tmp/stage2-probe.exe \
    run src/app/cli/native_build_worker.spl --threads 1 hi.spl
-> Error: --threads requires a positive integer
```

### What the route actually is — the `run` lead is REFUTED as the cause

`bootstrap_main.spl:590-596` deliberately accepts `run <internal entrypoint>`
when `SIMPLE_NATIVE_BUILD_WORKER=1`, and dispatches
`cli_native_build(all_args[3..])` **without** executing
`native_build_worker.spl` at all. So the earlier `unknown command 'run'` result
was measured without that env marker and does not describe the failing route;
argv slicing is correct and an argv trace added to `native_build_worker.spl`
never fires. That instrumentation was reverted.

### The discriminating matrix

Same binary, same internal route, only the flag varies:

| args | result |
|---|---|
| `--threads 1` | **Error: --threads requires a positive integer** |
| `--threads=1` | **Error: --threads requires a positive integer** |
| `--threads 2` | **Error: --threads requires a positive integer** |
| `-j 1` | **Error: -j requires a positive integer** |
| `--timeout 5` | proceeds to build |
| `--backend llvm` | proceeds to build |
| `--mode dynload` | proceeds to build |
| no flags | proceeds to build |

And on the ORDINARY route the same binary accepts the same flag:

```
/d/simple-tmp/stage2-probe.exe native-build --threads 1 hi.spl -o out
-> proceeds to build (no error)
```

### What this rules in and out

- **Not argv slicing / off-by-one.** The inline form `--threads=1` needs no
  following token and fails identically.
- **Not `text.to_i64()` in general, and not `cli_native_build_is_positive_decimal`
  in general.** `--timeout 5` runs the *same* validator branch
  (`cli_native_build_option_error`, `compile_targets.spl:166`, with
  `positive_integer = true`) and passes.
- **Not the probe, the env, or the lane.** One command outside any bootstrap
  reproduces it.
- **Specific to `--threads`/`--jobs`/`-j` on the internal-worker route.** The
  surviving candidates are the main parse loop at
  `compile_targets.spl:670-677` / `:689-693` (which, unlike `--timeout`, guards
  its parsed value with `<= 0` and so is the only site that can *report* a bad
  parse), and the four-way `or` chain at `:166`. Note `bootstrap_main.spl:60-65`
  documents a native-codegen miscompile in exactly this shape — an invalid
  `bitcast i64 to i1` when a `bool`-returning function merges more than one
  branch — and `bootstrap_native_build_thread_count`/`native_build_flag_needs_value`
  in that file already return `i64` to dodge it. That remains the leading
  hypothesis and is still **unconfirmed**.

### Next step for whoever picks this up

The remaining discriminator needs the fix candidate compiled INTO a Stage 2
(source instrumentation cannot reach the compiled parent). Change
`cli_native_build_is_positive_decimal` — and, if needed, the `:166` predicate —
to the `-> i64` shape used in `bootstrap_main.spl`, rebuild Stage 2, and re-run
the one-second reproduction above. The rust phases will fast-path: an
`src/app` edit does not change the seed content key
(`src/compiler_rust` + `src/runtime` + `Cargo.lock`), and the Stage 2 native
cache is preserved unless `--fresh-cache` is passed.

## ROOT CAUSE FOUND — white-box, from the rejected candidate's own object code (2026-09-01, second investigator)

The predecessor's `--timeout 5` datum is **REFUTED for this artifact**. Re-measured
against the identical binary (`/d/simple-tmp/stage2-probe.exe`, sha256
`66bbe02685bb54eb1a4b90506acde08d0321818c5030d83f106af5bae6219123` — byte-identical
to `rejection.env`'s `candidate_sha256`, md5 `e027d61462601021333efbf0f3743bf5`),
`--timeout 5` and `--timeout 1` both FAIL with
`Error: --timeout requires a positive integer`, rc=2.

### Measured matrix (rc read directly into a variable, never through a pipe)

`env SIMPLE_NATIVE_BUILD_WORKER=1 stage2-probe.exe run src/app/cli/native_build_worker.spl --threads <V> hi.spl`

| V | verdict | | V | verdict |
|---|---|---|---|---|
| 0 | **ACCEPT** (must reject!) | | 9 | **ACCEPT** |
| 1 | REJECT | | 10 | REJECT |
| 2..8 | REJECT | | 11 | **ACCEPT** |
| 00 | **ACCEPT** (must reject!) | | 19,90,91,99,09 | REJECT |
| 123, 999 | REJECT | | a, A, x | REJECT |

The validator is broken in BOTH directions — `0` and `00` are ACCEPTED. rc=2
places the failure in `cli_native_build_option_error` (`compile_targets.spl:471-473`
returns 2), i.e. `cli_native_build_value_error(..., positive_integer=true)` ->
`cli_native_build_is_positive_decimal`.

### The disassembly

`objdump -d` of the preserved Stage 2 native cache object
(`stage3/x86_64-pc-windows-msvc/stage2-native-cache/scope-c91065cff047d4d9/objects/00f0f130de2be37d.o`,
symbol `app__io___CliCompile__compile_targets__cli_native_build_is_positive_decimal`,
offset 0x590) ends the function with:

```
647:  xor    %eax,%eax
649:  test   %rsi,%rsi        # %rsi = the `value` TEXT handle, unmodified
64c:  setle  %al
64f:  lea    0xb(,%rax,8),%rax  # 0x0b = true, 0x13 = false
```

`(value.to_i64() ?? 0) > 0` compiled to **`value > 0` on the raw tagged text
handle**. There is no call to any integer-parse routine: the object's symbol
table contains `rt_string_new_literal`, `rt_string_rfind`, `rt_string_concat`,
`rt_string_chars` — and **no `rt_string_to_int` at all**. The answer therefore
depends on the string's heap/tag word, which is why it varies with the flag name
and the digit text.

### Where the compiler drops the call

`src/compiler_rust/compiler/src/codegen/llvm/functions.rs:2567-2582`
(`MirInst::MethodCallStatic`) matches
`"to_u8"|"to_i8"|…|"to_u64"|"to_i64"|"to_int"` and `return`s a plain
`coerce_value_to_type(recv, i64)` — an IDENTITY for the already-i64 tagged
value. It runs BEFORE the bare-method redirect table in the same function at
`:2772`, which maps `"to_int" | "to_i64" => Some("rt_string_to_int")`. That
entry is therefore **dead code**: the cast block shadows it.

`pipeline/native_project/mangle.rs:820-838` deliberately leaves `to_i64` BARE
when the receiver type is erased, on the documented contract that codegen routes
bare string builtins through that redirect table. The contract is broken for
`to_i64`/`to_int` by the ordering above. `codegen/llvm/emitter.rs:1493-1520`
carries the identical block and the identical defect.

This is an **ordering defect in the LLVM lane, not the `bitcast i64 to i1`
bool-merge** hypothesised earlier — that hypothesis is refuted: the returned
bool is materialised correctly as 0x0b/0x13, the INPUT to the comparison is
wrong.

### Blast radius

Every erased-receiver `text.to_i64()` / `.to_int()` in a native LLVM build
silently evaluates to the receiver's tagged word. Stage 2 is built exactly that
way, so this is not specific to `--threads`; `--threads`/`--jobs`/`-j`/`--timeout`
are merely the first call sites whose result is validated and reported.
`bootstrap_native_build_thread_count` (`bootstrap_main.spl:114-130`) and
`compile_targets.spl:670-698` use the same builtin.

## The fix (2026-09-01)

Five changes, each committed separately on `refs/wip/windows-msvc-lane-fix`:

1. **`src/runtime/runtime_native.c` + `src/runtime/runtime.h`** — new
   `rt_to_int_dynamic(int64_t)`: `rt_string_to_int` for a registry-validated
   heap string, **identity otherwise**. The identity fallback is what makes this
   regression-free by construction — every non-string receiver keeps exactly the
   behaviour the cast block gave it.
2. **`src/compiler_rust/runtime/src/value/collections.rs`** — the Rust twin, for
   parity with the seed's own JIT lane.
3. **`src/compiler_rust/compiler/src/codegen/llvm/functions.rs`** — carve
   `to_i64`/`to_int` out of the integer-cast `matches!` into an explicit
   `rt_to_int_dynamic` dispatch; the narrower widths (`to_u8`..`to_u64`) keep the
   cast, since they have no redirect entry and are genuine numeric narrowings.
   Redirect-table entry updated to `rt_to_int_dynamic`.
4. **`src/compiler_rust/compiler/src/codegen/llvm/emitter.rs`** — same removal
   from its cast `matches!` plus the same table update. Verified structurally:
   `emit_method_call_static` (`:1484`) consults `runtime_method_name` at `:1624`,
   AFTER the cast block, so the fall-through genuinely reaches the table. Pinned
   by a unit assertion in that file's test module.
5. **`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`** — the
   pure-Simple twin. Its Unresolved (erased-receiver) arm returned the receiver
   local unchanged for `to_i64`, i.e. the identical defect, which would reappear
   the moment Stage 3 recompiled the compiler with itself. There is **no
   `to_int` arm** in that file, only `to_i64`.

Plus **`scripts/bootstrap/bootstrap-from-scratch.sh`**: point
`check-stage-log-diagnosable.shs` at `stage2-receiver.log` for status 3 and the
sanity evidence for status 2, and echo which log was diagnosed. That
misdirection is what made this failure read as UNDIAGNOSABLE.

### Specs

- `test/01_unit/app/cli/bootstrap_threads_one_worker_route_spec.spl` (3/3)
- `test/01_unit/app/compile/cli_native_build_positive_integer_flags_spec.spl` (4/4)

Both assert the accept AND reject halves; `--threads 0`/`00`/`x` must stay
rejected. Their limitation is stated in their own headers: they run under the
interpreter, where `to_i64` was never broken, so they pin the CONTRACT rather
than reproduce the miscompile. The native oracle is the reproduction above plus
`check-bootstrap-stage2-struct-receiver.shs`.

### Cross-platform impact

The LLVM native lane on every platform, from miscompiled to correct for text
receivers and provably unchanged for everything else (identity fallback).
Cranelift/JIT and the tree-walk interpreter are untouched. Linux's 2026-08-09
admission is consistent with this: the old result was heap-layout dependent
(measured here as "9" accepted and "99" rejected), so a Linux lane that happened
to land on an accepting layout would pass — luck, not a different code path. No
green path can have depended on the broken answer, because the new non-string
behaviour is bit-for-bit the old one.

## Verification on the rebuilt Stage 2 (2026-09-01)

Rebuilt via `bootstrap-windows.sh --msvc --full-bootstrap --stop-after-stage2`.
Stage 2 built clean: **818 compiled, 0 cached, 0 failed**, 105,879 KB via
clang-cl, 670.4s compile + 28.8s link. Candidate md5 `d39eba227d228455727c324c372f960a`.

### A SECOND miscompile, found by disassembling the rebuilt object

After the `to_i64` fix the tail of `cli_native_build_is_positive_decimal` was
correct (`call rt_to_int_dynamic; test %rax,%rax; setle`) — but the flag was
still rejected when `-o <path>` was added to the same command line. The digit
loop was the reason:

```
620:  call rt_string_new_literal   # "0"
628:  cmp  %rax,%r12               # r12 = the CHARACTER value
62b:  jl   ...
```

`ch < "0"` and `ch > "9"` compiled to a raw `icmp` **on the tagged value
words**, i.e. a comparison of allocation ADDRESSES. `Eq`/`NotEq` had routed
through `rt_native_eq`/`rt_native_neq` for exactly this reason since long
before; `Lt`/`LtEq`/`Gt`/`GtEq` had no such guard
(`codegen/llvm/instructions.rs`). Fixed by mirroring the `Eq` arms through the
already-existing `rt_native_cmp`, which is present in BOTH runtimes and
value-compares when both sides are TAG_HEAP. No new runtime symbol; the
native-scalar path is unchanged.

### Measured matrix on the rebuilt binary — correct in BOTH directions

`env SIMPLE_NATIVE_BUILD_WORKER=1 <stage2> run src/app/cli/native_build_worker.spl --threads <V> hi.spl`

| V | verdict |
|---|---|
| 1,2,3,4,5,6,7,8,9,10,11,19,99,123,999 | **ACCEPT** (all 15) |
| 0, 00, -1, x, A, "" | **REJECT**, rc=2 (all 6) |

`grep -c "positive integer"` over the whole receiver probe log: **0**.
`bootstrap_stage2_struct_receiver=PASS`.

### Admission: NOT achieved — two remaining blockers, neither is this bug

1. **Probe-stage C toolchain**: the struct-receiver probe's route-guard link
   fails inside the probe's restricted `PATH`. First observed as
   `Bootstrap LLVM link failed ...: No C compiler found. Install clang or gcc.`,
   then after a PATH change as
   `vcruntime_c11_stdatomic.h(16): fatal error C1189: "C atomics require C11 or
   later"` — an MSVC `/std:c11` flag gap. Environmental, not a compiler defect.
2. **Hello-world `native-build` fails with no diagnostic** on this host
   (`error: build failed: 1 failed ... of 1 unit(s)` and nothing else). This
   **predates every change in this record** — it reproduces on the unmodified
   Rust seed `bin/simple.exe` for a three-line program, measured before any fix
   was written. It is why the repro cannot reach rc=0 here.

No `stage2-admitted/admission.env` exists, so **no admission is claimed**.

### The diagnosability fix is confirmed working

The same failure that previously printed
`UNDIAGNOSABLE: the stage failed with no error message of any kind` now prints
`PASS — 1 check(s), stage stage2 failed (exit 3) and said why`.

### Shared-checkout note

Three bootstrap attempts aborted at
`error: Rust inputs changed during full bootstrap; refusing to publish a stale
seed`. That guard hashes every file under `src/compiler_rust` and `src/runtime`.
One abort was self-inflicted (an edit committed mid-run); another was caused by
a concurrent session editing
`src/compiler_rust/compiler/src/linker/object_parser.rs` at 20:31:55, inside the
build window. Anyone running a full bootstrap in this shared checkout must
expect this and re-run.
