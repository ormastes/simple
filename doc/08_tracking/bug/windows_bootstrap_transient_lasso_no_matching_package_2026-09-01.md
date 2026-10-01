# Transient "no matching package named `lasso`" during Windows MSVC full bootstrap

Date: 2026-09-01
Status: TRANSIENT — not a repo defect. No `Cargo.toml`/`Cargo.lock`/`.cargo/config.toml`
change was made or needed.

## Symptom

`scripts/bootstrap/bootstrap-windows.sh --msvc --full-bootstrap --stop-after-stage2`
(via `run_s2final.sh`, PID 3012) failed the `rust-native-all-build` cargo step with:

```
error: no matching package named `lasso` found
location searched: crates.io index
required by package `simple-parser v1.0.0-rc.1 (.../src/compiler_rust/parser)`
As a reminder, you're using offline mode (--offline) ...
```

captured in `build/w/logs/x86_64-pc-windows-msvc/rust-native-all-build.log`, inside the
sandboxed `CARGO_HOME=build/w/rust-authority-<fingerprint>/cargo-home` that
`prepare_rust_authority_workspace` (bootstrap-from-scratch.sh:1829) generates by
rewriting `src/compiler_rust/.cargo/config.toml`'s `directory = "vendor"` line to an
absolute path. The immediately preceding step in the SAME run, SAME sandbox
(`rust-seed-build`, `cargo build -p simple-driver`), had just finished clean
(`Finished bootstrap profile ... in 8m 41s`).

## Why this is NOT a repo defect (verified, not assumed)

- `lasso.workspace = true` is declared at `src/compiler_rust/Cargo.toml:60`
  (`[workspace.dependencies]`) and consumed by `parser/Cargo.toml:16` and
  `compiler/Cargo.toml:114`. Only one `lasso` entry in `Cargo.lock`
  (`version = "0.7.3"`).
- `vendor/lasso/.cargo-checksum.json` `"package"` checksum
  (`6e14eda50a3494b3bf7b9ce51c52434a761e383d7238ce1dd5dcec2fbc13e9fb`) is
  byte-identical to `Cargo.lock`'s `checksum` for lasso.
- The `.cargo/config.toml` -> private `CARGO_HOME/config.toml` rewrite (the awk
  script at bootstrap-from-scratch.sh:1851-1863) was reproduced by hand and
  produces a correct `[source.vendored-sources] directory = "<absolute vendor
  path>"`.
- The EXACT failing command, reproduced by hand in an isolated fresh sandbox
  (`env -i HOME=... CARGO_HOME=<generated config> ... cargo build --locked
  --offline --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap
  --target x86_64-pc-windows-msvc -p simple-native-all --features llvm`),
  **succeeds** (`Compiling ...` proceeds past `lasso`/`proc-macro2`/etc. once
  `TEMP`/`TMPDIR` are forwarded correctly).
- The same live process (PID 3012, unchanged), immediately after the failure,
  tore down and regenerated the identical `rust-authority-9b82cb07...`
  directory (evidenced by a transient
  `build/w/rust-authority-fingerprint-error.log.raw.3012` artifact that
  appeared and then disappeared) and re-ran `rust-seed-build` /
  `rust-native-all-build` again with **zero code changes**, and it proceeded
  cleanly (no `lasso` string in the resulting log).

## Most likely mechanism (not fully pinned down)

`bootstrap-from-scratch.sh` has an "authority publication transaction" recovery
path (`bootstrap_acquire_rust_authority` /
`bootstrap_authority_recover_or_refuse`, ~line 1663-1680) gated on a
`${rust_authority_current_marker}.transaction` marker file, plus a fingerprint
step (`bootstrap_authority_seed_inputs_fingerprint`) that writes
`rust-authority-fingerprint-error.*` artifacts on a transient failure. The
observed sequence (one failed cargo invocation citing a vendored-but-genuinely-
present crate, immediately followed by the SAME process cleanly rebuilding the
identical content from scratch with no intervention) is consistent with a
transient filesystem/timing hiccup around that recovery path — e.g. disk
contention on this shared, 100%-full 2.3 TB volume (21 GB free) with other
agent sessions concurrently active in the same repo — rather than a resolver
or vendoring bug. Not conclusively root-caused; recorded so the next person
who hits this exact error text does not re-litigate the vendor/lockfile
consistency (already proven fine above) and instead just retries the build.

## What to do if you hit this

Just re-run the bootstrap. Do not touch `Cargo.lock`/`vendor/lasso`/
`.cargo/config.toml` — they are correct. If it recurs deterministically
(not just once), that would upgrade this from transient to a real bug and
warrants re-opening with a fresh investigation.

## Update 2026-09-01: second, later failure in the SAME run — confirmed cause

The same run (PID 3012) got past the `lasso` hiccup and all four cargo steps
(`rust-seed-build`, `rust-native-all-build`, `rust-runtime-nolto-build`,
`rust-compiler-backfill-build`) completed clean. It then failed later, at the
Rust-authority publish step, with:

```
error: could not prepare immutable Rust authority generation
```

(`bootstrap-from-scratch.sh:2039`, wrapping
`bootstrap_stage3_prepare_seed_generation` in
`scripts/check/lib/bootstrap-stage3/authority.shs:1457`, which fails silently
on any internal `|| return 1` — copy, stamp-write, or verify — with no detail
surfaced).

**Root cause identified this time, not just suspected:** a SEPARATE, live,
concurrently-running bootstrap session was confirmed actively running against
the exact same `build/.simple-bootstrap-locks/` and (implicitly)
`build/w` output directory while this investigation's own run was in flight:

```
build/.simple-bootstrap-locks/.output-4c5cb...ba.claim.cf1b80c80064d3e7138282df60bab922:
  owner_pid=15911 owner_pgid=15911 lock_name=output-4c5cb...ba
```

`ps` showed PID-15911's tree (root bash PID 15893, started 10:05:04 — a fully
independent lineage from this investigation's PID 3012, started 09:48:06)
still alive and spawning new children as late as 10:07:24, i.e. actively
running *right now*, holding the output lock this run needed.

`run_s2final.sh` (this investigation's launcher, not itself tracked in git)
runs an UNLOCKED GC sweep before invoking the bootstrap:

```sh
find build/w -maxdepth 1 -type d -name 'rust-authority-*' \
  ! -name 'rust-authority-fingerprint-tmp' -exec rm -rf {} + 2>/dev/null
```

with a comment in the same script admitting the danger: "This MUST stay after
lock acquisition ideally -- it is pre-lock today and would delete a
concurrent run's tree; safe only because this launcher is the sole runner."
That assumption is false in this environment — multiple agent sessions run
concurrently in this repo. Either this investigation's own GC sweep (at its
own start) or the other live session's equivalent sweep is the most likely
explanation for the transient `lasso` failure too: `cargo`'s vendored-source
config lives under `build/w/rust-authority-<fingerprint>/cargo-home`, which a
`rm -rf build/w/rust-authority-*` glob run by ANY concurrent session would
delete mid-build regardless of whose fingerprint directory it is.

**Action taken:** none against the other session's lock or directories —
killing/removing another live session's lock or in-progress `rust-authority-*`
tree would be destructive to that session's work and is exactly what this
investigation is warning against. No admission verdict (ADMITTED/rejected) was
obtainable from this investigation's own run for this reason; re-run once no
other session holds `build/.simple-bootstrap-locks/`.

**Recommendation (not implemented here — flagging only):** either serialize
bootstrap runs across sessions in this repo, or give concurrent sessions
disjoint `--output=` directories, or make `run_s2final.sh`'s GC sweep
lock-aware (acquire the same output lock before globbing/deleting) as its own
comment already says it should.
