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

## Follow-ups (not fixed here)

- `bin/simple native-build <f>.spl` nil-receiver crash → SIGILL.
- `bin/simple native-build --entry <f>.spl` hang.
- `bootstrap_main.spl` usage text still advertises `[--native]` for `compile`
  while the implementation rejects everything but `--format=smf`.
- Re-measure the native AOT row in
  `doc/08_tracking/bug/for_in_text_iterates_bytes_not_chars_2026-08-01.md` on the
  canonical seed; it is currently inference, not measurement.
