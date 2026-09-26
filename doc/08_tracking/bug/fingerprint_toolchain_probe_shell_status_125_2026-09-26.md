# Phase-1 fingerprint aborts intermittently: toolchain probes return shell-status=125 under the probe's `env -i`

Filed: 2026-09-26
Host: DESKTOP-5A4V03J (Windows 11, Git Bash / MSYS2, `x86_64-pc-windows-gnu`)
Severity: Blocking intermittently — roughly half of phase-1 attempts abort in the
first minutes. Each failure is fast and leaves a clean tree, so it costs time
rather than state.

## Symptom

`sh scripts/bootstrap/run-phase1-local.shs` aborts with one of three messages,
all from the same underlying probe failure:

```
error: could not resolve canonical Rust toolchain          (fingerprint, pre)
error: failed to fingerprint Rust seed inputs              (fingerprint, pre)
error: failed to re-fingerprint Rust seed inputs after Cargo (post-cargo)
VERDICT — ABORTED: stage=fingerprint | stage=rust-rust-compiler-backfill-build
```

`.simple/storage/build/bootstrap/rust-authority-fingerprint-error.log` names the
actual failure. Observed variants, all on this host within one afternoon:

```
bootstrap-native-metadata-probe=rustc-version attempt=1 shell-status=125
bootstrap-native-metadata-probe=rustc-version attempt=2 shell-status=125
rust-toolchain-check=rustc-version-command=fail
```

```
rust-toolchain-check=cargo-version-command=pass        <-- plain cargo passes
bootstrap-native-metadata-probe=cargo-fingerprint-version attempt=1 shell-status=125
bootstrap-native-metadata-probe=cargo-fingerprint-version attempt=2 shell-status=125
```

Note the second: a plain `cargo` check passes in the same run, moments before the
probe-wrapped invocation of the same binary fails twice.

## Where it fails

`bootstrap_stage3_native_metadata_probe`
(`scripts/check/lib/bootstrap-stage3/authority.shs:1260-1280`) runs each
toolchain probe as:

```sh
env -i PATH="$PATH" LC_ALL=C LANG=C "$@" \
    >"$tmp/stdout" 2>"$tmp/stderr" || status=$?
```

It retries once (`for attempt in 1 2`) and reports `shell-status`. Both attempts
returned 125 in every observed case. 125 is the "command could not be executed"
class, not a rustc/cargo diagnostic — and `head -c 4096 "$tmp/stderr"` printed
nothing, so the child produced no error output of its own.

## What was ruled out

- **Not a missing toolchain.** `rustup show active-toolchain` →
  `nightly-x86_64-pc-windows-gnu (default)`; `rustc --version` →
  `rustc 1.100.0-nightly (215a8af4b 2026-09-15)`, exit 0, immediately after a
  failing run.
- **Not the `env -i` stripping of `RUSTUP_HOME`/`CARGO_HOME` by itself.** That
  does happen, and `config/host/DESKTOP-5A4V03J.sdn` documents it via
  `rustup_fallback_home: C:\Users\User\.rustup` ("the %USERPROFILE%\.rustup
  fallback that `env -i` resolvers land on when RUSTUP_HOME is dropped"). The
  fallback exists and carries both toolchains, and the probe command reproduced
  BY HAND succeeds:

  ```
  $ env -i PATH="$PATH" LC_ALL=C LANG=C \
      /c/Users/User/scoop/apps/rustup/current/.cargo/bin/cargo -V
  cargo 1.98.1 (797e8a9bc 2026-08-05)
  exit=0
  ```

  Worth recording even so: under `env -i` the proxy resolves through the
  fallback home and answers **1.98.1**, while the configured home answers
  **1.100.0-nightly**. The bootstrap tolerates that split today, but it means
  these probes measure a different toolchain than the build uses.
- **Not the tree.** Every failing run had `gitlink` clean (see the sibling
  gitlink record), no orphans, and no stale locks; preflight's five checks passed
  in the runs that got further.
- **Not the console-kill class.** A separate defect in the *launcher* (not the
  repo) caused silent mid-run deaths with Task Scheduler `Last Result:
  -1073741510` = `0xC000013A STATUS_CONTROL_C_EXIT`, because a task whose action
  is `bash.exe` inherits the invoking console and dies when it closes. Fixed by
  having the task action `Start-Process` bash hidden and exit. The 125 failures
  are distinct: they print a real error and a VERDICT.

## Not reproduced on demand

The probe succeeds every time it is run by hand. The failures appear only inside
a full bootstrap run, roughly every other attempt, and at different probe sites
(`rustc-version` pre, `cargo-fingerprint-version` pre, `rustc-version` post).
That pattern — a spawn that works interactively and intermittently cannot
execute under load, with no child stderr — fits process-creation pressure
(handle/desktop-heap exhaustion, or an AV/filter-driver interaction) rather than
a toolchain or configuration fault. It has NOT been proven; stating it as a
hypothesis, not a cause.

## Why it matters beyond the flakiness

The probe already retries twice and gives up. Because the failure is
indistinguishable from a real toolchain problem in the top-level message
("could not resolve canonical Rust toolchain"), an operator reasonably starts
debugging rustup — which is healthy. The error log has the real signal
(`shell-status=125`, empty child stderr) but the top-level message does not
point at it.

Suggestions for whoever owns this, in increasing cost:

1. **Name the class in the top-level error.** If every attempt failed with a
   status in the "could not execute" range and the child wrote no stderr, say so
   and point at `rust-authority-fingerprint-error.log`, rather than reporting an
   unresolvable toolchain.
2. **Widen the retry.** Two immediate attempts do not survive a transient
   spawn failure; a short backoff (e.g. 3 attempts, 1s/3s) would likely absorb
   it, and is cheap because the probe is milliseconds when it works.
3. **Preserve `RUSTUP_HOME`/`CARGO_HOME` through the probe** (allowlist them
   alongside `PATH`) so the probe measures the same toolchain the build uses,
   removing the 1.98.1-vs-1.100.0 split noted above. This is a behavioural
   change to what the fingerprint binds, so it needs the authority owner's
   judgement, not a drive-by edit.

## Related

- `stage3_walk_retains_handle_per_entry_2026-09-25.md` — the Stage-2 memory
  ceiling; Stage 2 reaches `[850/901] compiled` then aborts with
  `memory allocation of 239616 bytes failed` at ~5 GB free.
- `quarantined_generation_exceeds_max_path_blocks_preflight_2026-09-25.md`
- `bootstrap_publish_blocked_windows_native_symlink_privilege_2026-09-07.md`
