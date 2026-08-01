# `--native` silent empty-binary emit — scope, root cause, and evidence retraction (2026-08-01)

**Status:** root cause identified and already fixed at origin
`e1150d003b7c4e39f170ce40626b7155e087faa6`; hardening added here so the failure
mode can never again be silent. **Scope of the original report was WRONG** — see
"What does NOT reproduce".

---

## THE HEADLINE: which native-path evidence is unreliable

Read this section before citing any `--native` measurement.

**Unreliable — a Success verdict with no binary, exit 0:** any `--native` or
`native-build` measurement taken through a **compiled stage2/stage3 pure-Simple
CLI** (`bin/simple`, i.e. `src/app/cli/bootstrap_main.spl`) **before** origin
`e1150d003b7c4e39f170ce40626b7155e087faa6`. On that lane the compiler reported
Success, wrote no binary (or a stub), and **exited 0**. Any probe run there
observed an empty/absent binary, not the behaviour under test. Treat every such
result as VACUOUS — including "the defect reproduced identically on the native
AOT path" in
`doc/08_tracking/bug/for_in_text_iterates_bytes_not_chars_2026-08-01.md`, which
is already flagged unproven and stays unproven until re-measured.

**RELIABLE — do not retract:** measurements taken through the canonical Rust
bootstrap seed `src/compiler_rust/target/bootstrap/simple` (154 MB, built
`cargo build --profile bootstrap --features llvm`). That lane was verified
working today across every variant tried (below). Native-path evidence produced
by the seed is sound.

So the blast radius is **the pure-Simple CLI lane only**, not "all native
evidence". Audit a doc by asking *which binary produced it*.

---

## What does NOT reproduce (the original report is wrong on scope)

The report said `compile <f>.spl --native -o out` emits a binary that runs,
prints nothing and exits 0 **including for a trivial hello-world**, citing a
3768-byte stripped ELF with no symbols. On the canonical seed, at
`e1150d003b7c4e39f170ce40626b7155e087faa6`, **the hello-world control PASSES.**

Control source (repo-relative, `tmp_native_probe/ctl.spl`):

```
fn main():
    print("HELLO_CONTROL")
```

| # | invocation (seed = `src/compiler_rust/target/bootstrap/simple`) | exit | size | stdout |
|---|---|---|---|---|
| 1 | `seed compile ctl.spl --native -o f1` (flags AFTER positional, exactly as reported) | 0 | 2 642 760 | `HELLO_CONTROL` |
| 2 | `seed compile --native ctl.spl -o f2` | 0 | 2 642 760 | `HELLO_CONTROL` |
| 3 | absolute path INSIDE repo | 0 | 3 043 256 | `HELLO_NATIVE_PROBE` |
| 4 | absolute path OUTSIDE repo (scratchpad) | 0 | 2 642 760 | `HELLO_CONTROL` |
| 5 | `--backend=cranelift` | 0 | 2 642 776 | `HELLO_CONTROL` |
| 6 | `--opt-level none` | 0 | 2 642 824 | `HELLO_CONTROL` |
| 7 | `seed native-build ctl.spl -o nb1` (bare positional) | 0 | 23 160 | `HELLO_NATIVE_PROBE` |
| 8 | `seed native-build --entry ... --entry-closure --runtime-bundle auto` | 0 | 23 160 | `HELLO_NATIVE_PROBE` |
| 9 | `seed compile ... --native --linker ld` | 1 | — | loud: `error: codegen: undefined symbol: __dso_handle` |
| 10 | no-LLVM 57 MB `target/release/simple`, same args | 0 | 3 123 104 | `HELLO_CONTROL` |

Two sub-claims in the original report are also refuted:

- **"`nm -g` reports no symbols" carries no signal.** Host `--native` output is
  auto-stripped by default (`--no-strip` exists to defeat it). Every *working*
  binary in the table above is likewise stripped with no symbols. This was a red
  herring, not corroboration.
- **The absolute-path trap did not fire** (rows 3 and 4). Absolute paths
  compiled and ran correctly, both inside and outside the repo root. The
  standing warning about absolute paths was not the mechanism here.

I could not reproduce a 3768-byte ELF from any seed invocation. The reported
artifact is consistent with the pure-Simple lane below, not the seed.

## What DOES reproduce — the pure-Simple CLI lane

`bin/simple` (deployed pure-Simple, `bootstrap_main.spl`) genuinely cannot emit
native at HEAD, but today it fails **loudly**, so it is no longer a false-green:

- `bin/simple compile ctl.spl --native -o out` → exit 1,
  `error: bootstrap compile supports --format=smf only`, no artifact.
- `bin/simple native-build ctl.spl -o out` → `runtime error: field access on nil
  receiver`, then SIGILL / core dump (exit 132), no artifact.
- `bin/simple native-build --entry ctl.spl -o out` → hangs (killed at 200 s).

The last two are separate live defects in the deployed pure-Simple CLI and are
**not** fixed by this change. They are loud, so they cannot fabricate evidence.

## Root cause

`src/app/cli/bootstrap_main.spl`, `run_native_build_bootstrap`. In a **compiled**
stage2/stage3, the enum field `options.mode = CompileMode.Aot` does not survive
struct transport into the driver: `mode.to_text()` comes back matching none of
`aot`/`jit`/`interpret`, `compile()` logs `[WARN] no mode matched, falling
through`, and then **returns Success having emitted nothing, exiting 0**. That is
precisely the reported signature — runs, prints nothing, exit 0.

Emission therefore did not die in object emission, the link step, entry-point
wiring, or runtime init. It died **before codegen was ever selected**, in option
transport. Nothing was emitted at all; a leftover or stub file was what got
measured.

Fixed at origin `e1150d003b7c4e39f170ce40626b7155e087faa6` by adding the text
override channel `compile()` consults first:

```
options.cli_mode_text = "aot"
```

**Landing hazard:** the shared working copy was STALE on this exact file and
would have reverted that fix. Restore from origin before touching
`bootstrap_main.spl`. See the staleness report referenced in the session notes.

## Changes in this commit

`src/app/cli/bootstrap_main.spl` (applied on top of restored origin content):

1. **Positive-artifact assertion on the native lane.** `run_native_build_bootstrap`
   returned `0` on `compile_result_is_success(result)` with no check that a file
   was ever written — the asymmetry that let this bug be silent, since the
   sibling SMF path in `run_compile_bootstrap` already asserted `file_exists` and
   `file_size > 300`. The native lane now makes the same assertion and fails
   loudly with `reported success without creating '<out>'` or
   `produced a stub artifact (N bytes)`.
2. **Sibling fix on the SMF lane.** `run_compile_bootstrap` set
   `options.mode = CompileMode.Aot` with no `cli_mode_text` override — the same
   broken transport, one enumeration step away. Added `options.cli_mode_text =
   "aot"` there too. Its stub guard already prevented a false green; this makes
   the lane actually work rather than merely fail honestly.

## Verification standard for re-measuring native evidence

Exit 0 is not evidence. Assert a **positive artifact**: non-trivial byte size,
plus expected stdout from a live control compiled in the same run. Do not infer
success from a clean exit, and do not use symbol presence as a health signal on
this path — host `--native` strips by default.

## Follow-ups — the three CLI defects, resolved 2026-08-01

### 1. nil-receiver SIGILL — ROOT CAUSE FOUND AND FIXED

It was never native-specific. `bin/simple compile ctl.spl --format=smf` SIGILLs
**identically**, so the deployed pure-Simple compiler could not compile *any*
program by *any* route. Exact site, via gdb on the deployed stage3:

```
#0 compiler.mir.synthetic_driver_registration.plan_synthetic_driver_registration+300
#1 compiler.mir.synthetic_driver_codegen.apply_synthetic_driver_codegen
#2 MirLowering.lower_function  #3 lower_module  #4 lower_to_mir  #5 aot_compile
```

Deliberate trap, not a null jump: `guard_nonnull_receiver`
(`src/compiler_rust/compiler/src/codegen/instr/fields.rs:23`) emits
`rt_eprintln_str` + `ud2`. The receiver is `fn_.driver_manifest_attr` in
`fn_.driver_manifest_attr.kind`, guarded one line earlier by
`if not fn_.has_driver_manifest_attr`.

**Why the guard passed.** Dumping the HirFunction at the trap:
`[fn_+0x90]` — the `has_driver_manifest_attr` **bool** slot — held **`0x03`, the
nil sentinel**, which `test/je` reads as TRUE. The paired value at `[fn_+0x98]`
was also `3`; `3 & ~7 == 0`, so the receiver masked to null.

Source: `declaration_lowering.spl` computed the flag as `driver_manifest.?`.
`.?` is the **TryOperator** and has **no native lowering** — on the normal path
the seed rejects it (`constructs that require the interpreter: [TryOperator]`),
but under `SIMPLE_BOOTSTRAP=1`, which is exactly how this compiler is built,
that hard error is downgraded to a warning and `opt.?` yields the nil sentinel
instead of a bool. Every function then looked manifest-carrying with a nil
manifest. `check-extern-registration.shs` is clean (`ok=true`); the weak-stub
mechanism was **not** involved.

Fixed by replacing `.?`-into-`bool` with `if val`-based presence checks (all 5
non-test sites: 2 in `declaration_lowering.spl`, 3 in `compiler_sffi.spl`), plus
a defence-in-depth guard in `plan_synthetic_driver_registration` that names the
function and the desynced field instead of trapping.

### 2. `--entry` "hang" — NOT A HANG, by-design delegation

`--entry` without `SIMPLE_BOOTSTRAP_STAGE4=1` delegates to the Rust
`rt_native_build` FFI by design. With **no `--source`** it scans the DEFAULT
source roots (whole project) and loads that import graph before any codegen,
printing nothing. Measured: `--entry ctl.spl --source tmp_nativecli` finishes in
**2.1 s** and yields a working 23 KB binary that prints `HELLO_CONTROL`; the
same command without `--source` produces no output at all after 45 s. Not a
defect — an unbounded silent default. Now prints a note naming the cost and the
fix. **Do not "fix" this by changing the delegation.**

### 3. `compile` usage text — FIXED

Usage and `--help` now state `--format=smf` (the only form `compile` accepts)
and list `native-build` separately, instead of advertising the `--native` that
`run_compile_bootstrap` rejects.

### Verification status

Constructs verified by execution on the canonical seed's real native path
(hello-world control passing in the same session): the `if val` presence check
returns a true bool for `Some` and false for nil, and the desync case that used
to SIGILL now prints its named diagnostic and returns cleanly. **The full
bootstrap redeploy (T3) that would put these fixes into `bin/simple` has NOT
been run** — `bin/simple` still SIGILLs until it is rebuilt.

**Measurement trap found while probing (record this):** `SIMPLE_BOOTSTRAP=1`
makes seed `--native` emit **vacuous** binaries — the hello-world control built
with it is 5,648 bytes, prints nothing, and exits 0, versus ~3 MB and correct
output without it. Any `--native` probe run under that env measures nothing.

### Still open

- Re-measure the native AOT row in
  `doc/08_tracking/bug/for_in_text_iterates_bytes_not_chars_2026-08-01.md` on the
  canonical seed; it is currently inference, not measurement.

---

## T3 redeploy attempt 2026-08-01 14:44 — BLOCKED (task #18 stays open)

SIGILL baseline re-confirmed on the deployed binary immediately before the
attempt, so the bug is live and unchanged:

```
$ bin/simple compile hello.spl --format=smf -o hello.smf
runtime error: field access on nil receiver
Illegal instruction (core dumped)          # exit 132
```

`bin/simple --help` still prints only the banner — no `run`/`test`/`lint`/`check`.

**The deploy is gated shut, and the gate is correct.** Attempt:
`scripts/bootstrap/bootstrap-from-scratch.sh --deploy --output=<scratch> --jobs=8`
(deliberately no `--full-bootstrap`, to leave the shared Rust seed alone). It
exited after ~3 min:

```
WARNING: Seed/runtime stale, but this is not --full-bootstrap; reusing the existing Rust seed.
error: full CLI bootstrap refuses a stale compiler backfill; re-run with --full-bootstrap
```

Chain, verified in the script:

1. `--deploy` forces `full_cli=1` (bootstrap-from-scratch.sh:163-165).
2. `full_cli=1 && seed_stale=1` is a hard refusal (:908-911).
3. `seed_stale` is **genuinely** set, not a bookkeeping artifact. The stamp
   `src/compiler_rust/target/bootstrap/simple.inputs.sha256` (written 14:04)
   records `inputs_fingerprint=c2c8364a0829…`, but recomputing it now via
   `bootstrap_stage3_seed_inputs_fingerprint` yields `816e7212aeb2…`. Rust
   source content changed after the stamp, so the 14:04 backfill archive
   (`libsimple_compiler_backfill.a`) really is out of sync with the seed binary
   (relinked 14:44 by a parallel lane, `da702cc5…` vs the stamped `d1c66eb1…`).

So a correct redeploy **requires `--full-bootstrap`, i.e. rebuilding the shared
Rust seed.** There is no partial path: the missing `run`/`test`/`lint`/`check`
subcommands are exactly what the full-CLI relink supplies (":1591" —
`use --full-cli, --deploy, or --mode=one-binary to relink`), so a
non-full-CLI stage3 build cannot clear the acceptance bar either.

**Why the seed rebuild was not forced.** At the decision point the shared tree
was heavily contended:

- **six** live processes were executing the shared seed
  `src/compiler_rust/target/bootstrap/simple` (other lanes' `test` and `lint`
  runs) — a relink swaps the binary out from under them mid-measurement;
- a parallel lane was already running `cargo build --profile bootstrap` against
  the same `target/bootstrap` directory;
- load average had climbed 14.7 → **23.5**, available RAM 53 GB → **48 GB**, with
  **swap fully exhausted** — the condition under which the OOM killer fires
  before the 64 GB monitor cap.

This is not hypothetical: **L7 Stage-4 Pass A died today of exactly this race**,
with `error: Rust runtime authority changed during private admission` — that
check (:1126) compares the runtime authority before/after private admission and
aborts when another lane rebuilds the seed mid-run.

**What would make it safe** (all four, then re-run *with* `--full-bootstrap`):

1. no processes executing `src/compiler_rust/target/bootstrap/simple`;
2. no other `cargo build --profile bootstrap` touching that target dir;
3. load average back near idle and swap no longer exhausted;
4. no concurrent bootstrap lane in its private-admission window.

Use `cargo build --profile bootstrap --features llvm` from `src/compiler_rust/`
if the seed is rebuilt by hand — omitting `--features llvm` yields a no-LLVM
seed.

**Verified good, and reusable next window:** the fix commit `2cb9636309cf` is
intact in the working tree (`git diff 2cb9636309c` over the three touched files
is empty), and the current seed is LLVM-capable *by positive test* — it compiled
the hello-world control to a 3,043,288-byte binary that printed
`HELLO_FROM_DEPLOYED_SIMPLE_42`. Note this seed is **32 MB**, which independently
re-confirms that the 57 MB/154 MB "has LLVM" size heuristic is worthless; test
capability, never size.

---

## Native-evidence audit across `doc/08_tracking/bug/` + `doc/03_plan/` (2026-08-01)

Audit of every doc claiming a defect was observed/reproduced/verified on the
native path, against the two facts established today (the enum-`match` native
gate, and the `SIMPLE_BOOTSTRAP=1` vacuous emit). Read-only; nothing was built.

**Headline: almost nothing needed retracting, and two of the invalidating facts
were themselves over-scoped.** Applying them as stated would have wrongly voided
several sound bug docs. Corrections below.

### Method and funnel

`/usr/bin/grep` (pinned — default here is ugrep) + a classifier over both trees:
854 docs mention "native" → 520 make some native-flavoured claim → **155 claim a
native *execution outcome*** (a binary ran and misbehaved — the only class the
two facts can touch) → **14** of those show an enum `match` / `Option`-`Result`
construct in the measured code → after reading each, **1** needed a substantive
caveat. Build-*failure* claims ("native build failed with X") are excluded
throughout: those are loud failures, and neither fact can manufacture one.

### CORRECTION 1 — the native enum gate is DATED; "impossible" holds only after 2026-07-19

The refusal is not a constant of history. `git log -S` on
`src/compiler_rust/compiler/src/pipeline/execution.rs` dates the fail-closed gate
to **`7adbe1359ca` (2026-07-19)**. At `7adbe1359ca^` there is no
`allow_interp_calls` and no refusal at all — only three unconditional
`apply_hybrid_transform(&mut mir_module, &non_compilable, &boxed_returns)` sites.
The compiler's own help text names the pre-gate behaviour: build anyway, and
calls to flagged functions **"will silently return nil in this standalone native
binary"** (exit 3). Hence three eras, not two:

| Era | `compile --native` on enum-matching code | Evidence verdict |
|---|---|---|
| **before 2026-07-19** | **builds**; flagged fns hybrid-stubbed → calls silently return **nil** | **CONFOUNDED**, not impossible |
| **2026-07-19 → 2026-08-01** | refused, fail-closed, per compilation unit | **IMPOSSIBLE** — no binary existed to observe |
| after `3b9eb0a` (2026-08-01) | payload-free arms allowed (591 fns); payload/guard/bare-ident still refused | scope per Stage 1 |

The pre-gate era is the more dangerous one and was not on the original list. A
refusal is self-announcing; a nil-stub is not — and it **fabricates exactly the
symptom vocabulary these bug docs use**: "returns nil", "returns zero", "prints
nothing", "silent wrong value". Any pre-07-19 native measurement of a function
the gate deemed non-compilable was measuring the stub, not the defect. So
`native_pattern_match_staging.md` §3.1's "treat pre-2026-08-01 'verified on
native' statements as unsubstantiated" is right in outcome but wrong in
mechanism for the pre-07-19 majority — corrected in place there.

### CORRECTION 2 — the `SIMPLE_BOOTSTRAP=1` vacuity is `compile --native` ONLY, not `native-build`

The measurement recorded above (5,648 bytes, prints nothing) was taken on
`compile --native`. It does **not** generalise to `native-build`, and there is
direct counter-evidence already in the tree:
`cranelift_direct_string_constant_null_pointer_2026-07-12.md` (lines 516-522)
records that under `SIMPLE_BOOTSTRAP=1`, `native-build` **reroutes to the
LLVM/`llc` backend** (confirmed by `[bootstrap-real-llvm]` log lines) and
`fn main(): print("hello")` **builds and runs correctly, printing `hello`**. A
vacuous binary cannot print. Do not void bootstrap-env `native-build`
measurements wholesale — check the subcommand.

### CORRECTION 3 — `native-build` in a repro usually measures the INTERPRETER

The single largest source of false positives in this audit. The `native-build`
worker executes the LLVM-IR-generating Simple code **interpreted**
(`run_file_interpreted_with_args`). `bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`
states it outright in its own header — "**Backend:** native-build LLVM IR
generation, run **interpreted**" — with a 184-frame interpreter stack. So
"native-build" in a command line is *not* evidence of native execution, and such
docs are untouched by both facts. The audit question stays: **which binary,
which construct, which env.**

### Verdicts — docs examined in full

**SOUND, explicitly NOT retracted** (seed-produced, positive artifact, or the
construct/engine is not the gated one):

| Doc | Why it stands |
|---|---|
| `array_at_returns_nil_for_every_index_2026-08-01.md` | Rust-seed `compile --native --backend llvm`, "CONFIRMED by running a real ELF". `arr.at(i)` needs no enum `match`. |
| `jit_run_file_pipeline_gaps_2026-07-30.md` §13 | Post-gate but clean: `compile --native --backend cranelift`, real stripped PIE ELF (11,496 bytes — not the 5,648 vacuity signature), verified with `file`, run directly. Two-line cross-module-global repro, no enum match. |
| `hosted_native_option_try_unwrap_payload_leak_2026-07-19.md` | Seed `native-build`, rebuilt+run executable returning a specific wrong **84** — neither the nil-stub nor the vacuity signature. |
| `local_mir_type_of_option_bare_mismatch_2026-07-19.md` | `native-smoke-matrix.shs` `array_index_rw`, positive PASS (rc=71). |
| `bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md` | Interpreter-FFI defect per Correction 3. |
| `hir_stmt_expr_payload_extraction_nil_2026-07-17.md` | Despite `SIMPLE_BOOTSTRAP=1` + `native-build` + a nil symptom, root-caused and fixed **inside the seed interpreter**; the native-build worker is the harness, not the engine under test. |
| `hir_get_symbol_id_zero_returns_nil_2026-07-29.md` | Says plainly it reproduces under the tree-walk interpreter, "not native codegen". |
| `cranelift_direct_string_constant_null_pointer_2026-07-12.md` | Source of Correction 2's counter-evidence; its own bootstrap-env result is a *success* with correct output. |

**Conclusion changed — 1 doc, annotated in place:**

- `bootstrap_mir_interpolation_literal_braces_2026-07-11.md` — the fix (removing
  the branch that wiped `hir_interps` under `SIMPLE_BOOTSTRAP=1`) **survives**,
  and its non-bootstrap confirmation (`native-smoke-matrix.shs` 15/15 including
  `string_interp`) is untouched. What falls is one specific line of evidence: the
  guard is `interps.?`, confirmed by debug trace *under `SIMPLE_BOOTSTRAP=1`* —
  and this doc establishes that under exactly that env `.?` yields the nil
  sentinel `3`, which tests as TRUE. So that trace cannot discriminate "the fix
  works" from "`.?` was unconditionally true". The conclusion stands on the
  non-bootstrap evidence alone.

**Also corrected in place:** `doc/03_plan/compiler/native_pattern_match_staging.md`
§3.1 — era framing per Correction 1.

### Standing rule for future native claims

State all three or the claim is UNKNOWN, not SOUND: **which binary** (canonical
Rust seed vs. deployed pure-Simple `bin/simple`), **which subcommand**
(`compile --native` vs. `native-build` — they differ under `SIMPLE_BOOTSTRAP=1`,
and the latter often runs interpreted), and **which env**. Then assert a positive
artifact: non-trivial byte size plus expected stdout from a live control compiled
in the same run.
