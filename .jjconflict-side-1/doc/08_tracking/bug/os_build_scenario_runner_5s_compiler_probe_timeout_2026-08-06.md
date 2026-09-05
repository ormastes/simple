# Bug: `bin/simple os build/test --scenario=...` compiler-discovery probe times out at 5s, fails ALL scenarios — FIXED

**ID:** os-build-scenario-runner-5s-compiler-probe-timeout-2026-08-06
**Domain:** os/simpleos build tooling (`src/os/_QemuRunner/os_build_run.spl`)
**Severity:** blocker (for every `bin/simple os build`/`os test --scenario=...` invocation
in this environment)
**Filed:** 2026-08-06
**Status:** FIXED 2026-08-06 — see "Fix — FIXED 2026-08-06" below. A separate,
pre-existing, orthogonal blocker was discovered during verification and filed
as `doc/08_tracking/bug/simpleos_scenario_runner_no_selfhosted_binary_deployed_2026-08-06.md`.

## Summary

While pushing the riscv64 SimpleOS boot campaign forward, `bin/simple os test
--scenario=riscv64-hosted` and `--scenario=riscv64-smoke` both failed
immediately with:

```
[build][riscv64] phase=tooling FAILED: no runnable pure-Simple compiler
Error: build failed for scenario riscv64-hosted
```

This is not riscv64-specific — it is a compiler-discovery bug that fails the
scenario runner for every target in this environment.

## Root cause

`_simple_binary_has_native_build_contract` (`src/os/_QemuRunner/os_build_run.spl:436-449`)
probes each compiler candidate with:

```
_run_candidate_admission_pinned(candidate, probe_args, 5000)   # 5000ms hard timeout
```

The self-hosted `bin/simple` binary in this environment takes materially
longer than 5s to even reach its own argument-validation error path. Direct
reproduction:

```
$ time timeout 5 bin/simple native-build --backend cranelift \
    --entry src/app/cli/main.spl --mode definitely-invalid-mode
Terminated
real 0m5.005s   # killed by the probe's own timeout, produced no output

$ time timeout 60 bin/simple native-build --backend cranelift \
    --entry src/app/cli/main.spl --mode definitely-invalid-mode
[STDERR] error: native-build worker exited with code 1. ...
real 0m16.370s  # the actual diagnostic the probe is looking for
```

Every candidate in `_find_simple_binary_for_target`'s candidate list
(`release/x86_64-unknown-linux-gnu/simple`, `bin/simple`, etc.) is subject to
the same 5000ms bound, so all of them silently fail the probe and
`_find_simple_binary_for_target` returns `""`, which the caller
(`build_os_with_backend`, line 205-209) reports as "no runnable pure-Simple
compiler" — a misleading message; the compiler is runnable, just slower than
the probe allows.

## Impact

`bin/simple os build --scenario=<any>` and `bin/simple os test
--scenario=<any>` are currently unusable in this environment. Direct
`native-build` invocation (bypassing the scenario runner, mirroring the
pattern in `scripts/os/ssh_simple_hello_uefi.shs`) still works and is the only
way today to build any SimpleOS kernel target.

## Fix — FIXED 2026-08-06

Raised the probe timeout and made it configurable, matching the
`SIMPLE_OS_BUILD_TIMEOUT_MS` pattern already used elsewhere in the same file:

- `src/os/_QemuRunner/runner_targets.spl`: added `_OS_PROBE_DEFAULT_TIMEOUT_MS
  = 45000` (45s) and `_os_probe_timeout_ms()`, honoring a new
  `SIMPLE_OS_PROBE_TIMEOUT_MS` env override, next to the existing
  `_OS_BUILD_DEFAULT_TIMEOUT_MS` / `_os_build_timeout_ms()` / `_parse_timeout_ms`
  machinery (reused as-is).
- `src/os/_QemuRunner/os_build_run.spl:447-449`:
  `_simple_binary_has_native_build_contract`'s call to
  `_run_candidate_admission_pinned` now passes `_os_probe_timeout_ms()`
  instead of the hardcoded `5000`.

**Root-cause attribution correction:** the original write-up above inferred
"the 5s bound is what's failing every candidate" from a *direct* `native-build`
repro that bypassed `_simple_binary_is_valid`. In this environment's actual
current deployment state, every real candidate is rejected one gate earlier —
`_simple_binary_is_valid` (`os_build_run.spl:423-434`) rejects on `--version`
output containing `"bootstrap seed only"` in ~26ms, before the 5s-bound probe
at line 447 is ever reached (see the new companion bug doc below). So the 5s
bound was a genuine latent defect — confirmed independently, see Verification
— but it was **not** the operative cause of the specific failures observed
today; it is fixed here regardless because it is real and was going to bite
the moment a genuine self-hosted binary is deployed again.

45s was chosen (not a much larger fixed bound, and not something
adaptive/measured-per-run) primarily for internal consistency: the *preceding,
more expensive* step in the same validation chain — `_candidate_frontend_smoke`
(`os_build_run.spl:412-414`), which runs a real `native-build` of a trivial
program — already gets a 60000ms bound. A 5s bound on this *cheaper* follow-up
probe (an invalid-arg rejection, no actual codegen) was internally
inconsistent with the 60s already budgeted one step earlier in the same chain;
45s restores that consistency while staying under it. Secondarily, direct
timed runs of the exact probed command
(`native-build --backend cranelift --entry src/app/cli/main.spl --mode
definitely-invalid-mode`) were measured for corroboration — 3 runs, ~16.8–17.2s
consistently — but note this measured the **seed** binary currently deployed
at every candidate path in this environment (see companion doc), not a
genuine self-hosted binary; it is a real, executable path that answers the
same command, but not proof of self-hosted cold-start cost specifically. It is
used here only as a data point that a modest fixed bound (well under 60s) is
plausible, not as the primary justification. It is a bounded CLI liveness
probe run once per candidate at scenario-runner startup, not a hot loop, so a
modest fixed constant is simplest and sufficient — no caching/warm-reuse
complexity needed.

### Verification

**1. Mechanism, isolated from the deployment-state confound above.** The
timeout constant flows through unchanged code
(`_run_candidate_admission_pinned` → `_run_candidate_with_env` →
`process_run_timeout`), so `process_run_timeout` was exercised directly with a
synthetic 16s-latency candidate and a synthetic 60s-hung candidate:

```
--- OLD bound (5000ms) against a 16s-latency candidate ---
exit_code=-1 stdout=[] stderr=[[TIMEOUT: Process killed after 5s]]
--- NEW bound (45000ms, _OS_PROBE_DEFAULT_TIMEOUT_MS) against same candidate ---
exit_code=0 stdout=[DIAGNOSTIC_REACHED] stderr=[]
--- NEW bound (45000ms) against a truly hung candidate (60s) still bounded, not infinite ---
exit_code=-1 stdout=[] stderr=[[TIMEOUT: Process killed after 45s]]
```

This confirms: (a) a 5000ms bound does kill a probe against a candidate slower
than 5s, before any diagnostic is reached (matching the latent-defect claim
above, independent of what's actually deployed today); (b) a 45000ms bound
lets a ~16s-latency candidate answer successfully; (c) a genuinely hung/broken
candidate still fails fast (bounded at 45s, not infinite) — the "fail fast on
truly broken binaries" property is preserved.

**2. The new symbol and env override actually resolve and are honored** — not
just parses-as-valid-syntax. `runner_targets.spl` and `os_build_run.spl` are
both part of the `os.qemu_runner` module (both start with `use
os.qemu_runner.*`), the same pattern `_os_build_timeout_ms()` already relies
on being called unqualified from `os_build_run.spl:166,202`. Confirmed
directly with a scratch script (`use os.qemu_runner.*; print
_os_probe_timeout_ms()`):

```
$ bin/simple run probe_timeout_fn_check.spl
_os_probe_timeout_ms()=45000
$ SIMPLE_OS_PROBE_TIMEOUT_MS=12345 bin/simple run probe_timeout_fn_check.spl
_os_probe_timeout_ms()=12345
```

**3. End-to-end, blocked by a separate gate — not proof against this fix.**
`bin/simple os test --scenario=riscv64-smoke` re-run after the fix still
prints `phase=tooling FAILED: no runnable pure-Simple compiler`, because (per
point 1 above and the companion doc) no candidate binary in
`_find_simple_binary_for_target`'s search list is currently a genuine
self-hosted build in this environment — every one of
`release/x86_64-unknown-linux-gnu/simple`, `bin/simple`, and
`bin/release/x86_64-unknown-linux-gnu/simple` prints "this Rust-built Simple
binary is a bootstrap seed only" on `--version`, which `_simple_binary_is_valid`
correctly rejects *before* the timeout-bound probe this fix touches is ever
reached. That earlier gate masks this fix from an end-to-end run today; it
does not indicate the fix is wrong (see verification 1 and 2, which exercise
the changed code directly). Filed separately as
`doc/08_tracking/bug/simpleos_scenario_runner_no_selfhosted_binary_deployed_2026-08-06.md`,
which also owns confirming this fix end-to-end once a genuine self-hosted
binary is deployed, plus two smaller findings surfaced along the way: the
probe's exact-string match (`Error: invalid --mode '...' (expected dynload or
one-binary)`) doesn't match the seed's wording (`error: invalid --mode
'...'. Expected dynload or one-binary`, wrapped in a "native-build worker
exited" message) — harmless for a genuine self-hosted candidate since the
`.spl` diagnostic sites match, but only ever tested against the seed here; and
`bin/release/x86_64-unknown-linux-gnu/simple` exists on disk but is absent
from `_find_simple_binary`/`_find_simple_binary_for_target`'s candidate list.

## Related

- `doc/08_tracking/bug/riscv64_kernel_codegen_blocker_2026-07-20.md` (update
  2026-08-06) — the actual riscv64 kernel build blocker once this probe is
  bypassed.
