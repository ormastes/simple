# `native-build` fails on this aarch64 Linux host for two independent reasons

- **Date:** 2026-09-07, found while bootstrapping for the `1.0.1-beta.1` cut.
- **Host:** `aarch64-unknown-linux-gnu`, clang/LLD 23.1.0, 20 CPUs.
- **Status:** cause 1 FIXED (host package installed); cause 2 OPEN and blocking
  Stage 2 admission.

Both hid behind the same useless symptom — `native_compile` fails and the unit
carries `reason: (none recorded — BUG in the producer: a non-OK unit must carry a
diagnostic)`. Neither cause is visible from that line, and one masked the other.

## Cause 1 (FIXED): SDL2 was not installed, so every link failed

`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:351` pushes
`-lSDL2` **unconditionally** on Linux. `--as-needed` controls whether it lands in
`DT_NEEDED`; it does not make the library optional at link time — `ld.lld` still
has to find it. This host had no SDL2 at all (`ldconfig -p | grep -i sdl2` empty,
no `libSDL2*` under `/usr/lib/aarch64-linux-gnu`, no dpkg entry), so every
`native-build` died at:

```
ld.lld: error: unable to find library -lSDL2
```

Windows deliberately avoids this: `native_linking.spl:963-966` records that
`SDL2.lib` is absent by design because `src/runtime/runtime_sdl2.c` binds every
SDL symbol through `spl_dlopen`. Linux has no equivalent, so a host without the
SDL2 development package cannot build anything at all — including a three-line
hello world with no UI code in it.

Fixed here by installing `libsdl2-dev`. After that, `native-build` of a hello
world completes and the binary runs.

**Worth fixing properly:** the Linux path should either dlopen SDL like Windows
does, or drop `-lSDL2` when the program references no SDL symbol. A UI-less
program should not need a UI library present to link.

## Cause 2 (OPEN): the AOT path only works with `SIMPLE_BOOTSTRAP=1`

With SDL2 present, the Stage-2 candidate still fails its own frontend smoke. The
discriminating variable is `SIMPLE_BOOTSTRAP`, and nothing else. Measured with
the Stage-2 binary from `build/bootstrap-b3`, same fixture, same flags
(`--runtime-bundle core-c-bootstrap --entry-closure --mode one-binary`),
one variable changed at a time:

| `SIMPLE_BOOTSTRAP` | backend | result |
|---|---|---|
| `1` | cranelift | rc=0, executable produced, runs and prints `hello` |
| `0` | cranelift | rc=1, no output, `reason: (none recorded)` |
| `0` | llvm | rc=1, no output, `reason: (none recorded)` |

The backend is not the variable — both backends fail at `0` and cranelift passes
at `1`. `driver_aot_pipeline.spl:62,96,156` switch to a `bootstrap_flat_aot`
path when `SIMPLE_BOOTSTRAP=1` and `SIMPLE_BOOTSTRAP_STAGE4 != 1`; the ordinary
path is the one that fails.

This is the same wall as
`doc/08_tracking/bug/windows_native_capsule_receipt_invalid_blocks_every_native_build_2026-09-03.md`
and its sibling `native_build_requires_simple_bootstrap_env_windows_2026-09-03.md`,
which were filed as Windows-specific. **They are not.** It reproduces on aarch64
Linux, and the `SIMPLE_BOOTSTRAP` discriminator isolates it to one variable,
which those records left open.

## Why it blocks Stage 2 admission

`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs:99` defaults
`CANDIDATE_FRONTEND_BOOTSTRAP=0`, so the gate certifies exactly the configuration
that cannot work. Its own comment (`:89-96`) says this value "must be swept, not
fixed", because Stage 3 invokes the admitted Stage-2 binary with
`SIMPLE_BOOTSTRAP=1` while the gate only ever ran `0` — so the gate certifies a
configuration Stage 3 never uses. Today the sweep cannot pass: the `0` leg is
broken in the compiler.

## The diagnostic gap is a third defect

Every failure above reports an empty reason. `build_outcome.spl:420,426` prints
the "(none recorded — BUG in the producer)" text, and it is correct: the error
text produced by `_compile_selected_module`
(`driver_aot_native_output.spl:1648,1672`) does not survive into
`build_result.errors`, so `unit_err[1]` is empty. `build/build_diagnostics.log`
is never created. Until a real message reaches the summary, every instance of
this class costs a bisect. Fix this first — it is what makes cause 2 tractable.

## Where the message is destroyed (added after the first filing)

`_finish_selected_module_compile` (`driver_aot_native_output.spl:1665-1672`):

```
match compiled:
    case Err(err):
        Err("AOT compile error in {name}: {err.to_text()}")
```

`err` is a `CompileError`. That interpolation is the whole diagnostic, and it
does not survive native codegen:

- the Stage-2 binary built 2026-09-05 renders it
  `AOT compile error in ...: <invalid-heap:0x9d48501>` — the exact fingerprint
  documented in
  `native_struct_interpolation_renders_invalid_heap_2026-09-02.md`;
- the Stage-2 binary built today from `origin/main` renders it as nothing at
  all, which is how the unit reaches the summary with an empty reason.

Both binaries fail the identical fixture at `SIMPLE_BOOTSTRAP=0` with SDL2
installed, so this is long-standing, not a regression in the window between
them. The `case Ok(module)` arm is ruled out: it would produce
`Backend produced no object code for {name}`, plain text that would have
printed.

Fix order: make this one call site carry a real message (read the field, do not
interpolate the struct), rebuild Stage 2, and only then chase why the backend
returns `Err` at `SIMPLE_BOOTSTRAP=0`. Until then every instance of this class
costs a bisect, which is what both the Windows records and this one paid.

## The real message, recovered — and the actual cause

The empty reason is a **message-loss defect, not a missing message**. The
interpreted Rust seed and the natively-compiled Stage-2 binary run the same
`.spl` driver on the same fixture and disagree about whether the diagnostic
survives:

```
seed,    SIMPLE_BOOTSTRAP=0, --backend cranelift:
  reason: AOT compile error in ...hello_world:
          scalar object-path AOT is available only for builtin LLVM
stage2,  SIMPLE_BOOTSTRAP=0, --backend cranelift:
  reason: (none recorded — BUG in the producer ...)
```

So the producer does record a reason; it is destroyed somewhere between
`_compile_selected_module`'s `Err(...)` and `build_result.errors` when that path
is itself natively compiled. `parallel.spl:474` pushes it as
`errors.push((build_unit.path, msg))` into a `[(text, text)]` — a text word
inside a tuple inside an array, which is exactly the borrowed-payload hazard the
surrounding code comments keep warning about
(`driver_aot_native_output.spl:1626-1628`, `backend_types.spl:385-392`). That is
the first thing to check.

Trying `compileerror_to_text(err)` bound to a `val` at
`_finish_selected_module_compile` (`:1672`) does **not** fix it — measured, then
reverted. That arm is not on this path: the failure comes from the
`backend_session` branch above it.

### Why the gate fails: cranelift cannot do object-path AOT

The recovered message names the cause outright. `candidate_frontend_admission.shs:98`
defaults `CANDIDATE_FRONTEND_BACKEND=cranelift`, and the scalar object-path AOT
route is builtin-LLVM-only. Backend sweep on the seed at `SIMPLE_BOOTSTRAP=0`:

| backend | result |
|---|---|
| `llvm` | rc=0, executable runs, prints `hello` |
| `cranelift` | rc=1, "scalar object-path AOT is available only for builtin LLVM" |
| `llvm-lib` | rc=1 |

`--backend llvm` at `SIMPLE_BOOTSTRAP=0` **works on the seed**. It does not work
on the Stage-2 binary, which fails at `0` on both backends — so the Stage-2
artifact appears to carry no builtin-LLVM provider even though Stage 2 was built
with `--backend=llvm`. That is the next thing to establish, and it is what
actually blocks admission.

This supersedes the earlier framing above: `SIMPLE_BOOTSTRAP` is the
*discriminator* because the `=1` path routes around the object-path AOT route
entirely, not because the env var is itself meaningful.
