# Stage 2 sanity fails: secure_temp_dir returns "" during AOT diagnostic staging

- **Status:** OPEN
- **Severity:** P1 — last known blocker for Windows/MSVC Stage 2 admission
- **Discovered:** 2026-09-12
- **Lane:** `sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --mode=dynload`

## What now works (context for whoever picks this up)

The Stage 2 **link resolves completely** — `LNK1120` is gone, unresolved
externals are **0** (were 33). The Stage 2 compiler is **built and runs**: the
sanity harness records `version_status=0` and
`version_output=simple-bootstrap 1.0.1-beta.1`.

## Symptom

Stage 2 then fails its frontend smoke test (exit 2):

```
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1
                        unsupported_status=1 frontend_status=1 candidate_unchanged=true
error: AOT compile error -- unit, reason and lengths follow on the next lines
error:   unit (bare):
error:   reason (bare):
error:   name-len=53 reason-len=30
[native-compile-failed] scripts.check.cert.redeploy_gate.fixtures.hello_world:
    AOT compile error ...: diagnostic staging unavailable
```

## Located

`src/compiler/80.driver/driver_aot_native_output.spl:2267`:

```
val diagnostic_dir = secure_temp_dir_raw(dirname(obj_path), "simple-aot-diagnostic")
if diagnostic_dir == "":
    return _aot_compile_failure(name, "diagnostic staging unavailable")
```

`secure_temp_dir_raw` -> `rt_secure_temp_dir`, defined identically in three C
translation units (`runtime.c:2651`, `runtime_native.c:13216`,
`runtime_secure_staging.c:95`), each with a complete `_WIN32` branch.

## Ruled out, with evidence

- **Not a missing extern registration in the Stage 2 lane.** The smoke log
  contains no `unknown extern function`. (A probe on the *deployed* seed DOES
  report `unknown extern function: rt_secure_temp_dir` — but that binary is
  dated 2026-09-02 and the registration landed 2026-09-07 in `82098baaa45`, so
  that is stale-seed noise, not this failure.)
- **Not MAX_PATH.** Measured: output base 87 chars, unit name 53, resulting
  diagnostic dir 164 — well under 260. (The separately filed
  `windows_bootstrap_max_path_262_2026-08-30` is a different situation.)
- **Not the Win32 sequence itself.** A standalone C probe replicating the
  Windows branch verbatim succeeds at every step on this host:
  `bcrypt.dll` loads, `BCryptGenRandom` returns 0,
  `ConvertStringSecurityDescriptorToSecurityDescriptorA` returns 1,
  `CreateDirectoryA` with the protected DACL `D:P(A;;FA;;;SY)(A;;FA;;;OW)`
  returns 1.

## Remaining hypotheses, untested

1. `dirname(obj_path)` does not exist at call time, so `CreateDirectoryA` fails
   with `ERROR_PATH_NOT_FOUND` — the function returns an empty string for every
   failure mode, so the caller cannot tell which.
2. The stage runs under `env -i` with a restricted environment and a different
   working directory; a relative `parent` would then resolve elsewhere.
3. The DACL grants SYSTEM and OWNER only; if the stage's effective token differs
   from an interactive shell's, creation could be denied.

## First thing to do

`rt_secure_temp_dir` collapses every failure into `""`. Give it a diagnosable
failure path — at minimum log `GetLastError()` and the attempted path on the
Windows branch — and rerun. That one change should identify which of the three
hypotheses is correct, and it is the same "fail closed WITH a reason" principle
that located the Stage 2 env-name and CC-path defects earlier today.

---

## Update 2026-09-12, later: the Stage 2 compiler WORKS. The harness is the problem.

A rejected Stage 2 binary is now preserved at
`.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe.rejected`,
which makes this directly testable instead of only reachable through a ~40
minute bootstrap. Results:

| probe | result |
|---|---|
| `simple.exe.rejected --version` | `simple-bootstrap 1.0.1-beta.1`, rc=0 |
| `native-build` hello world, MSVC env, shallow out dir | **rc=0, exe produced** |
| same, into the deep stage3 output dir | **rc=0** |
| same, into a parent directory that does not exist | **rc=0** |
| same, under `env -i` WITH SystemRoot/SystemDrive | **rc=0** |
| same, under `env -i` WITHOUT SystemRoot/SystemDrive | **rc=0** |

So the Stage 2 compiler natively builds a hello world successfully, including in
a stripped environment. `diagnostic staging unavailable` could not be reproduced
outside the sanity harness at all.

### Hypotheses now disproven

- **NOT MAX_PATH** (measured 164 vs 260, previously).
- **NOT a missing parent directory** — explicitly tested above.
- **NOT missing `SystemRoot`/`SystemDrive`** in the `env -i` allowlist. This
  looked compelling: `LoadLibraryA("bcrypt.dll")` needs them to resolve system
  DLLs, they ARE passed at `authority.shs:716-717` for other invocations, and
  they are NOT in `bootstrap_stage3_stage2_canonical_env_names`. Tested both
  ways anyway: both rc=0. Recorded because it is the obvious next guess and
  someone else will otherwise spend the same time on it.
- **NOT the Win32 call sequence** — a standalone C probe succeeds at every step.

### Operational trap for whoever continues

The `rt_secure_temp_dir` diagnostic landed in this session (PR #672, in BOTH
`runtime.c` and `runtime_native.c`) **did not appear in the rejected Stage 2
binary**: `strings simple.exe.rejected | grep rt_secure_temp_dir:` returns 0.
The core-c archive it linked predates the change, so the instrumentation never
ran. Bust that archive cache before concluding the diagnostic is silent — a
silent diagnostic here means "not linked", not "did not fire".

### Where to look next

The difference is in how the sanity harness *invokes* the compiler, not in the
compiler. Compare the harness's exact argv and environment
(`bootstrap_stage_sanity` in `scripts/bootstrap/bootstrap-from-scratch.sh`, and
the frontend smoke driver it runs) against the working invocations tabled above.
The unit it compiles is `scripts.check.cert.redeploy_gate.fixtures.hello_world`,
reached through `--entry-closure`, which none of the probes above used.
