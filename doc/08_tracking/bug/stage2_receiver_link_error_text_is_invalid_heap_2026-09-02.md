# Stage 2 receiver probe: the MSVC link error message is a corrupted heap handle

**Date:** 2026-09-02
**Status:** ROOT-CAUSED 2026-09-02; fix authored, verification build running
**Severity:** HIGH — destroys the diagnostic for the only gate blocking Windows Stage 2 admission

## Symptom

Stage 2 **builds cleanly** — 818 compiled, 0 cached, 0 failed, 105,879 KB `simple.exe`
via clang-cl, 624.7s compile + 33.3s link = 658.0s — and is then **rejected**:

```
reason=stage2-struct-receiver-failed
probe_exit=1
```

The receiver probe log (`stage3/x86_64-pc-windows-msvc/stage2-receiver.log`, 85,010 B,
line 902) ends with:

```
error: in-process native-build: Bootstrap LLVM link failed
  (input=.../bootstrap-stage3-route-guard.app.cli.bootstrap_main.o
   output=.../bootstrap-stage3-route-guard):
  Linking failed: Windows MSVC linking failed: <invalid-heap:0x1e9548829b1>
```

## The defect

**`<invalid-heap:0x1e9548829b1>` is not a linker message.** It is what the runtime
prints when a `text` handle does not reference a valid heap string. The linker's actual
error text — the one fact needed to fix this gate — is **destroyed** before it is
printed.

So the reported reason for the rejection is unknowable from the log. Every prior
investigation of `stage2-struct-receiver-failed` has been reasoning about an error
message that was never real.

## Why this matters beyond the bootstrap

This is the same corruption family as the two miscompiles fixed on
`session/text-compare-and-toint-miscompile-2026-09-01` (PR #269), where a tagged word
was consumed as if it were a value:

- `.to_i64()` / `.to_int()` on a text receiver compiled to a compare on the raw handle;
- text `<` / `>` / `<=` / `>=` compiled to `icmp` on allocation addresses.

Here the same class shows up in **error-message construction on a failure path**, which
is the worst place for it: the defect only manifests when something else has already
gone wrong, so it converts every such failure into an undiagnosable one.

## Evidence

- `stage2-rejected/x86_64-pc-windows-msvc/rejection.env`
  — `status=rejected`, `reason=stage2-struct-receiver-failed`,
  `candidate_sha256=3ed5dbf6db8bc215f09de85bb174c455b2aab452283c11bd66ad6e10c6abe66e`
- `stage3/x86_64-pc-windows-msvc/stage2-receiver.env`
  — `status=fail`, `probe_exit=1`,
  `candidate_sha256_before == candidate_sha256_after` (the probe did not mutate the
  candidate), `probe_log_sha256=ec28d72c699fc20ed1775b353f243b8e82d8bf3cfeb95b8e41bf121d476c418a`
- `stage2-native-build.log` tail confirms the build itself succeeded.

Note the probe reached the link stage normally: `[bootstrap-real-llvm] count 4`,
`[llvm-tools] llc-done`, `llc-object`, `read-bytes` all completed. Only the final link
failed, and only its message is corrupt.

## What must happen next, in order

1. **Recover the real linker error.** Do not attempt to fix the link until its actual
   text is visible — the current message carries no information. Options: capture the
   linker's stderr/stdout directly at the call site rather than routing it through the
   corrupted `text`, or print the raw bytes before they are wrapped.
2. **Then** diagnose the underlying link failure with a real message in hand.
3. **Fix the message corruption itself** as a separate change — an error path that
   destroys its own diagnostic will keep doing so for every future failure.

## Related

- PR #269 — the two text-handle miscompiles (`.to_i64()`, relational compares).
- `check-stage-log-diagnosable.shs` previously pointed at `stage2-native-build.log`
  instead of `stage2-receiver.log`, which is why this failure was reported as
  UNDIAGNOSABLE; that misdirection is fixed, and it is what made this log readable at
  all. The guard now correctly reports the stage said why — but *what* it said is this
  corrupted string.
- Same family as the four diagnostic-swallowing defects found 2026-09-01
  (phase-3 discarded diagnostics; `head -c` truncating failure logs to their useless
  first bytes; `2>nul` in the MCP wrapper; MIR errors dropping spans).

## Not yet established

- Whether the corruption is in the linker-invocation wrapper, in the error propagation,
  or is a further instance of the tagged-word class fixed in PR #269.
- Whether a binary built **with** PR #269's fixes still shows it. The candidate here
  (`3ed5dbf6…`) predates that verification.

## ROOT CAUSE (2026-09-02) — it was never the linker's text

`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:877` read:

```
Err("Windows MSVC linking failed: {e}")
```

`e` is a **`LinkError` struct** (`70.backend/linker/link.spl:108` — `kind`,
`message`, `symbol`, `location`), and it has no Display. The interpolation
therefore rendered the STRUCT VALUE, not `e.message`.

`runtime/src/value/heap.rs:8` has no `Struct` variant at all (String 0x01,
Array 0x02, Dict 0x03, Tuple 0x04, Object 0x05, Closure 0x06, Enum 0x07, ...),
so a native-codegen struct pointer carries no recognised heap header;
`heap_value_to_display_string` (`value/sffi/io_print.rs:474`) hits its
`let Some(object_type) = v.heap_type() else` arm and emits exactly
`<invalid-heap:0x{ptr:x}>`. Had it been a class instance it would have printed
`<object@0x...>` (`io_print.rs:562`) — the *`invalid-heap`* spelling is the
fingerprint of the headerless struct.

**Consequence:** `LinkError.message` was never read on this path. The linker's
real text was not corrupted in transit — it was never fetched. Every prior
investigation reasoned about a message the code never asked for. This is
therefore **not** a further instance of the PR #269 tagged-word miscompile
class; that hypothesis in "Not yet established" is refuted.

Same defect, same shape, second site:
`_LinkerWrapper/shared_linking.spl:293` (`"Windows MSVC DLL linking failed: {e}"`).

## Fix (`refs/wip/windows-msvc-lane-fix`)

1. Both wrapper sites interpolate `{e.message}`.
2. `msvc.spl` `MsvcLinker.link` and `LldLinkLinker.link` now redirect the
   linker with `> "<output>.link.log" 2>&1` **inside the `cmd /C` string**, so
   the linker's bytes are written to disk by cmd.exe and never travel through a
   captured `text` handle at all; the file is read back and dumped immediately
   as `[msvc-link] output-begin` / `output-end` before the `Err` is built, so
   the diagnostic survives even if the returned message is mangled downstream.
   The `Err` additionally carries exit code, full command, and the log path.

Cross-platform impact: none. `msvc.spl` is on no Unix link route; both wrapper
sites are inside MSVC branches. Lints clean on the deployed seed.

## Still open

- The **underlying link failure** — unknown until a stage2 built from this fix
  runs the receiver probe. That build is in progress.
- **Generalised defect:** interpolating any struct in native codegen yields
  `<invalid-heap:0x...>` with no diagnostic. Either give structs a display
  rendering or make it a compile-time error to interpolate one. There is no
  guard for this class today; the same silent-diagnostic-destruction can occur
  at any `"{some_struct}"` in the tree.

## Progress 2026-09-02 — five defects fixed, gate still red, next step identified

Each fix made the NEXT real error visible; none was visible before it. Runs are
`--msvc --full-bootstrap --stop-after-stage2`, LLVM 18 lane
(`windows-msvc-bootstrap-env.shs`; LLVM 23 deliberately NOT used — `llvm-sys 180`
reads the first `llvm-config` on PATH). Seed `src/compiler_rust/target/release/simple.exe`
md5 `286f66b8615dce0e0da788f0550c4008`, 39,120,896 B, `cmp` clean vs `deps/simple.exe`.

| run | receiver-probe error | fix |
|---|---|---|
| baseline | `<invalid-heap:0x1e9548829b1>` | `{e}` -> `{e.message}` (struct render) |
| 1 | `No C compiler found. Install clang or gcc.` | `_get_temp_dir()` MSYS `/d/` -> `d:/` |
| 2 | `MSVC link.exe not found` | `find_link_exe()` split `where`'s 3 lines |
| 3 | `linker exited 1`, log unreadable | cmd.exe redirect target -> backslashes |
| 4 | `No C compiler found` again (nondeterministic) | made cc detection self-reporting |
| 5 | `No C compiler found (hosted native link, target '')` | — |

Run 4 got furthest: `link.exe` was located and invoked with the full command line
(recorded in the log as `[msvc-link] command: "C:\Program Files\...\link.exe" /OUT:... /FORCE:MULTIPLE`).

**Run 5's diagnostic is the lead to follow.** The log shows:

```
[cc-detect] no C compiler verified on Windows.
[cc-detect] temp dir: D:\simple_build\...\stage2-tmp
[cc-detect] tried: clang-cl, cl.exe, clang, gcc (each `where` + a real compile)
```

and **zero `[CC-VERIFY] ... REJECTED` lines**. `_cc_verify_compiles` is called only
after `where <cc>` returns 0, so its total absence proves **every `where` probe
failed** — no candidate compiler is visible to the receiver probe at all. This is
a PATH/environment problem in the probe, not a compiler problem: clang-cl 18.1.8,
cl.exe 19.44 and link.exe all exist on this host and were exercised by hand.

`stage2-command.transcript` records **no `OS=` entry** in the stage-2 environment,
which matters because both `_is_windows()` (`runtime_compiler.spl:25`) and
`backend_shell_tuple()` (`io_compat.spl:5`) branch on `env_get("OS")` and fall
back to the **Unix** path when it is absent. The `[cc-detect]` prints did appear,
so `OS` was set for that call — but the two predicates are one scrubbed env away
from silently routing a Windows build through `/bin/sh`.

**Next:** find where `check-bootstrap-stage2-struct-receiver.shs` / the stage-2
runner constructs the probe environment, and give it the toolchain bin dirs (or
pass an absolute compiler via `SIMPLE_CC`) rather than widening PATH globally.
Then re-run. Also consider replacing the `OS`-env-var Windows test with a
host-derived predicate.
