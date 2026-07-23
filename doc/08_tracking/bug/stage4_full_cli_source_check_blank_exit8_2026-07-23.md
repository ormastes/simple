# Stage 4 full CLI delegated exit/stream corruption

- **Status:** DELEGATION FIXED ON LINUX / STAGE 4 STILL REJECTED.
- **Source revision:** `f2b493ec656007b1132e284221e1f68f7891e4d8`.
- **Candidate SHA-256:**
  `765acfa3dceac4c7d28d2c8974a224bef4815dfb017fd2a3ca23134e6ebfc503`.
- **Seed sibling SHA-256:**
  `c89358abfecd63d92e7470a46afd167a03e317287d35fe2112555ba816fed6a9`.

## Evidence

The isolated two-thread native build completed in 190.2 seconds with 4 modules
compiled, 1,373 cache hits, and 0 failures. The official layout's adjacent
`simple_seed` makes `simple -c 'print(1+1)'` print `2`.

The next required bootstrap admission command fails silently:

```text
SIMPLE_BINARY=<candidate> <candidate> check src/app/cli/bootstrap_main.spl
exit=8, stdout/stderr empty
```

The candidate was therefore rejected before frontend admission, redeploy, or
essential-tools smoke. An earlier 0/11 redeploy result was invalid evidence
because the manually assembled layout lacked `simple_seed`; it must not be
interpreted as eleven independent compiler regressions.

## 2026-07-23 bounded repair

A clean current temporary seed was built from Rust tree
`6a708335753559777a7b766d4e3cffe40ac731a6`:

```text
seed sha256=f1276430c99e7ba3f82107e4157a76f3a13537cf1b15289b403662b5fd004a30
rt_process_spawn_guarded=present
```

The first rebuilt candidate preserved the stdout marker but dropped stderr and
returned `136` for a child exit of `17`. That proved two independent defects:
the temporary Rust bootstrap path exposed tagged tuple fields, and the core C
`rt_process_run` owner returns an empty stderr slot. Frontend delegation is
foreground work, so `_cli_run_frontend_delegate` now uses the existing scalar
`rt_process_run_inherit` owner instead of capturing and replaying a tuple.

The corrected pure-Simple candidate
`00431ce52f940722f52746a802011f7d33f35d4931738facee26c5c7b7917b31`
passes the retained admission probe: distinct stdout and stderr markers survive
and exit `17` remains `17`. The probe covers POSIX and emits a `.cmd` delegate
for Windows; Windows remains unqualified because its core C process-wait owner
is incomplete, so the gate intentionally fails rather than claiming parity.

## Remaining blockers

The one official source-check no longer fails blank with exit 8. It now reports
a distinct isolated-layout bug and exits 127:

```text
timeout: failed to run command 'bin/simple': No such file or directory
```

`src/app/cli/check_entry.spl::resolve_worker_binary` ignores the supplied
`SIMPLE_BINARY` before falling back to `bin/simple`. Fix that owner and add an
isolated-layout regression before running the official source-check again.

The remaining candidate frontend smoke also rejects this candidate with
SIGILL while native-building the tiny `p2_add.spl` fixture. The attempted
pure-Simple incremental relink was terminated after sustained single-core work
with no phase output; the final temporary-seed relink reused the cache correctly
(`5 compiled, 1372 cached, 0 failed`, 174.5 seconds). Diagnose the SIGILL and
the pure relink cache/parallelism regression as separate bounded lanes.

Do not deploy this candidate until those blockers pass. Do not remap exits,
fall back to the Rust seed for normal tooling, or rerun already-green delegation
evidence.
