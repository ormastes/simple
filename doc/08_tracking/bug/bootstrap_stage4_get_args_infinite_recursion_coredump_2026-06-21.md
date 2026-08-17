# Bootstrap Stage 4 binary SIGSEGVs at startup — `io.cli_ops.get_args` infinite recursion

- **Id:** bootstrap_stage4_get_args_infinite_recursion_coredump_2026-06-21
- Status: RESOLVED (source) — P1
- Status re-verified 2026-08-17 (wave W4) by source inspection + a family census.
  The earlier "re-verified 2026-08-17 ... (triage shard 00)" OPEN stamp was wrong;
  see the two dated sections at the end of this file. Acceptance of a *binary*
  still requires `scripts/check/check-bootstrap-stage4-selfverify.shs`.
- **Severity:** P1 — a fresh `bootstrap-from-scratch.sh --pure-simple` produces a
  Stage 4 `build/bootstrap/full/<triple>/simple` that **segfaults on every
  invocation** (even `print(1)`), in both interpret and JIT mode. There is no
  working build→run loop from this path, which blocks validating/deploying any
  self-hosted compiler change (e.g. the self-hosted f64 codegen port, see
  `f64_self_hosted_call_result_codegen_2026-06-21.md`).
- **Found:** 2026-06-21
- **Component:** `app.io.cli_ops.get_args` (argv accessor) + seed native codegen
  (`src/compiler_rust`) that compiled it; Stage 4 build path in
  `scripts/bootstrap/bootstrap-from-scratch.sh`.

## OBSERVED

```
$ sh scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple   # Stage 3 self-host fails, Stage 4 built by seed
$ printf 'fn main():\n    print(1)\n' > /tmp/triv.spl
$ build/bootstrap/full/x86_64-unknown-linux-gnu/simple run /tmp/triv.spl
Segmentation fault (core dumped)            # rc=139
$ SIMPLE_EXECUTION_MODE=interpret build/.../simple run /tmp/triv.spl
Segmentation fault (core dumped)            # rc=139  (crashes in BOTH modes)
```

gdb backtrace — unbounded self-recursion (same return address repeating →
stack overflow):

```
Program received signal SIGSEGV, Segmentation fault.
0x00000000004d686c in io.cli_ops.get_args ()
#0  0x...4d686c in io.cli_ops.get_args ()
#1  0x...4d6871 in io.cli_ops.get_args ()
#2  0x...4d6871 in io.cli_ops.get_args ()
...                                         # identical frame repeats to stack exhaustion
```

The crash is at argv parsing during CLI startup, **before** any program runs —
which is why both execution modes die identically.

## ANALYSIS

- `io.cli_ops.get_args` is compiled into infinite self-recursion by the seed
  native-build that produces Stage 4. The likely shape is a wrapper/forwarding
  function the seed lowers as a call to itself (missing tail/leaf resolution, or
  a same-name self-dispatch) instead of the runtime argv primitive. Definition
  lives under `src/app/io/cli_ops` (re-exported via `src/app/io/mod.spl`); the
  pure-Simple argv source is `src/lib/nogc_sync_mut/io_runtime.spl:172`.
- **The deployed `bin/simple` does NOT crash** (`run /tmp/triv.spl` → `1`,
  rc=0), so a runnable Stage 4 is producible by some path; this specific
  `--pure-simple` seed-build path miscompiles `get_args`. The seed used was
  `src/compiler_rust/target/bootstrap/simple`.

## CONTRADICTS EXISTING DOC

`bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17.md` states the
Stage-4 fallback "still produces working binaries (Stage 4 uses the seed, which
is valid)" and is "Not a runtime-correctness bug." This repro shows that
assumption no longer holds for `--pure-simple`: the seed-built Stage 4 binary is
not runnable. That doc's severity downgrade should be revisited.

## IMPACT

- Blocks self-host verification AND any "build self-hosted from source → test"
  loop. Directly blocks the self-hosted f64 codegen port.

## REPRO / FIX CHECKLIST

1. Reproduce: `sh scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple`
   then run the fresh `build/bootstrap/full/<triple>/simple` on any program.
2. Disassemble `get_args` (gdb `disas`) to confirm the self-call, and diff its
   MIR/codegen vs the deployed (working) `bin/simple`.
3. Determine why this seed build lowers `get_args` to self-recursion (seed
   version? a forwarding alias resolving to itself?); fix in the seed codegen or
   the `cli_ops.get_args` definition.
4. Add a Stage-4 smoke gate to `bootstrap-from-scratch.sh`: run
   `<stage4> -c "print(1+1)"` and fail the build if it does not print `2`.
   - Done 2026-06-22: `scripts/bootstrap/bootstrap-from-scratch.sh` now smokes
     `${full_bin}` immediately after Stage 4 and exits before deploy/MCP work if
     the new binary cannot execute code. Guarded by
     `test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl`.

## REFERENCES

- `doc/08_tracking/bug/bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17.md`
- `doc/08_tracking/bug/f64_self_hosted_call_result_codegen_2026-06-21.md` (blocked by this)
- `doc/09_report/bootstrap_crash_report_2026_04_01.md` (LIM-010 history)

## 2026-08-17 (wave W3) — RETIRED: fixed in current source

The "re-verified 2026-08-17 by source inspection (triage shard 00)" stamp at the
top of this file is **wrong**. The defect is fixed in current source, and the fix
carries this bug's own id in its comment.

`src/app/io/cli_ops.spl` no longer imports `get_args`/`exit` from
`std.io_runtime`. It declares the runtime primitives as externs
(`extern fn rt_cli_get_args() -> [text]`, `extern fn rt_exit(code: i64)`, lines
15-16) and the wrappers call those directly:

- `src/app/io/cli_ops.spl:331 fn get_args()` -> `rt_cli_get_args() ?? []`
- `src/app/io/cli_ops.spl:342 fn exit(code)` -> `rt_exit(code)`
- `src/app/io/cli_ops.spl:345 fn cli_get_args()` -> `rt_cli_get_args()`

The in-file comment at lines 8-14 names the mechanism and this bug id: importing
`get_args` under its own name made the wrapper body bind to *itself* rather than
the import, giving the unbounded self-recursion in the gdb backtrace above.
`grep -n io_runtime src/app/io/cli_ops.spl` now returns only that comment line.

Caveat, stated rather than papered over: W3 was barred from rebuilding or
redeploying, so this is a **source** retirement — the historical Stage 4 binary
was never re-run. The invariant is now pinned by
`test/01_unit/app/cli/silent_success_fail_closed_source_spec.spl` ("reads argv
through the runtime extern, never through a same-named import"), which fails if
either import is reintroduced.

Status: RESOLVED (source). Reopen only with a fresh Stage 4 backtrace.

## 2026-08-17 (wave W4) — the exact cycle, plus a whole-tree census of the shape

**The cycle, stated precisely.** It is a one-frame direct self-call created by a
*self-shadowing import*, not a dispatch/trait/mixin path:

```
use std.io_runtime.{get_args}      # binds name `get_args` in cli_ops' file scope
fn get_args() -> [text]:           # ALSO binds name `get_args` in the same scope
    get_args() ?? []               # resolves to the LOCAL fn, not the import
```

The local definition wins the name over the import, so the wrapper body's call is
`io.cli_ops.get_args -> io.cli_ops.get_args`. That is exactly the gdb backtrace in
OBSERVED: a single frame at a constant return address (`0x…4d6871`) repeating to
stack exhaustion. Arity is identical (0 -> 0), so nothing disambiguates the two
bindings. `exit` had the same shape. This is *not* a seed-codegen miscompile — the
ANALYSIS section's guess that the seed "lowers `get_args` to self-recursion" was
wrong; the seed lowered the source faithfully, and the source said "call myself".
It is an instance of the repo's unqualified-import-vs-local-definition resolution
family: `tierless_std_import_ambiguity_resolves_by_registration_order_2026-07-29.md`,
`metal_session_variant_unqualified_import_resolves_wrong_2026-07-08.md`.

**Fix confirmed present** in `src/app/io/cli_ops.spl`: `extern fn
rt_cli_get_args()` / `extern fn rt_exit(code: i64)` at lines 14-15, wrappers at
331/342/345 calling the externs, and `grep -n io_runtime` returns only the
explanatory comment at line 10. An extern cannot be shadowed by a same-named
local wrapper, so the fix removes the ambiguity rather than merely reordering it.

**Census — is the shape live anywhere else?** Scanned all owned `.spl` under
`src/` (vendor excluded) for files that both import a name and define a function
of that name whose own body calls that name:

| filter | count |
|---|---|
| imports name + defines same name (any) | 51 files |
| ...and the definition's body calls its own name | 17 sites |
| ...and top-level (not a method) **and** same arity — the exact bug shape | 3 sites |
| ...and genuinely reachable as self-recursion | **0** |

All three finalists are safe, and each was checked individually rather than
counted:
- `src/lib/nogc_sync_mut/gpu/context.spl` and `src/lib/nogc_async_mut/gpu/context.spl`
  (`create_context_from_config`) — the `use` and the recursive-looking call are
  inside a docstring `Example:` block (lines 229/232), not code.
- `src/os/crypto/xsalsa20.spl` (`hsalsa20`, arity 2 -> 2, a real
  import-plus-definition collision at lines 17/19) — dodges the trap the same way
  `cli_ops` now does, by qualifying the forward explicitly at line 34:
  `os.crypto.salsa20.hsalsa20(key, nonce16)`.

The 14 method-level hits are a different shape: a class method `fn is_dir()`
(arity 0) calling a free `is_dir(self.path)` (arity 1), so arity disambiguates.
Five collector methods in `src/compiler_rust/lib/std/src/tooling/dashboard/collector.spl`
are same-arity method-vs-import and are the closest remaining relatives; they are
in the Rust seed's bundled std, not the self-hosted startup path, so they cannot
reproduce this bug's Stage-4 SIGSEGV. Recorded here rather than fixed — no
evidence they misbehave, and changing them is out of this row's scope.

**Guard hole closed.** `test/01_unit/app/cli/silent_success_fail_closed_source_spec.spl`
pinned the invariant but only rejected the two `std.`-prefixed spellings of the
import, so `use nogc_sync_mut.io_runtime.{get_args}` — the same module by another
path — would have reintroduced the defect past a green guard. The spec now
rejects all four spellings.

**What is still NOT proven, and cannot be from here.** No Stage 4 binary was
built or run. `bin/simple` on this host is the Rust seed, and stage 4 sits behind
a stage-3 blocker, so there is no runnable oracle for the crash itself. The
binary-level acceptance bar is
`scripts/check/check-bootstrap-stage4-selfverify.shs`: a trivial program must
print its sentinel (compared by CONTENT, never exit code) and the binary must
recognise `run`/`test`/`lint`/`duplicate-check`, with the stage-3 parent
rejecting `lint` as a negative control that voids the run if it passes. Note that
`scripts/check/check-post-bootstrap-stage4-sspec.shs` is a PAPER gate — it echoes
literal `=true` capability lines and never spawns a binary — so its green is not
evidence for this row and must not be cited as such.
