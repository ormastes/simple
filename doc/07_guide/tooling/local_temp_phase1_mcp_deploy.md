# Local temp deployment: bootstrap phase 1 + `simple-mcp` + `spipe` MCP

Runnable guide for producing the bootstrap **phase-1** compiler on a local host
and deploying it, together with the `simple-mcp` and `spipe` MCP servers, into a
**throwaway temp root** that can be verified end to end.

Everything below was executed on a Windows 10 / Git Bash / MinGW host
(`x86_64-pc-windows-gnu`, rustc 1.98.1, node v26.8.1) on 2026-09-07.

## What "phase 1" is (and is not)

`scripts/bootstrap/preserve-phase-binary.shs` names the lineage snapshots
`phase1 | phase2 | phase3`, and `bootstrap-from-scratch.sh:2529-2532` preserves
`phase1` from `${seed_bin}` immediately before Stage 2 starts. So:

| phase | artifact | produced by |
|---|---|---|
| **phase 1** | the **Rust seed** compiler + runtime archives | three `cargo build --profile bootstrap` invocations |
| phase 2 | seed compiles `bootstrap_main.spl` | Stage 2 |
| phase 3 | Stage-2 binary recompiles itself | Stage 3 |

Phase 1 is therefore **the Rust seed build**, nothing more. It is *not* a
self-hosted compiler, and per `.claude/rules/bootstrap.md` it must never be
copied over `bin/release/<triple>/simple` — a fresh seed with a fresh mtime is
exactly what makes the next lane believe a self-host succeeded. That is the
whole reason this guide deploys into a temp root instead.

## 0. Fix the shell PATH first (Windows only)

Git Bash here inherits the raw Windows `;`-separated `PATH`, which POSIX tools
cannot parse — `ls`, `head`, `cargo` all report `command not found`. The exact
entries needed are host-specific (which drives, where scoop installed
things), so they live in a hostname-keyed config rather than hardcoded in this
guide: `config/host/<hostname>.sdn` (schema `simple-host-env-v1`) carries this
host's ordered `path_prepend` list plus its rustup and temp-deploy values, and
`scripts/setup/host-env.shs` — sourced, never executed directly — resolves the
current hostname, loads that file if one exists, and exports
`SIMPLE_HOST_PATH_PREPEND` plus a `host_env_apply_path` function that prepends
it onto `PATH` idempotently. A host with no config file is a silent no-op: it
keeps the shell's generic `PATH`, which is correct, not degraded. Rebuild
`PATH` before anything else:

```sh
. scripts/setup/host-env.shs
host_env_apply_path
```

See `config/host/DESKTOP-5A4V03J.sdn` for this host's own recorded values, and
`sh scripts/setup/host-env.shs --selftest` to verify the loader itself.
`scripts/bootstrap/run-phase1-local.shs` wraps this PATH setup plus step 1
below into one tracked script.

Confirm the host triple and that its Rust target is installed:

```sh
sh -c '. scripts/setup/platform-detect.shs; echo "$PLATFORM_TRIPLE LLVM_FOUND=${LLVM_FOUND:-0}"'
rustup target list --installed
```

`LLVM_FOUND=0` is fine for phase 1: `bootstrap-from-scratch.sh:1839-1847` leaves
`llvm_features` empty when LLVM is absent, so the seed builds without it. It is
*not* fine for Stage 2/3 with the default `--backend=llvm`, hence
`--backend=cranelift` below.

### rustup's *host* triple must be gnu, not just its default toolchain

Measured 2026-09-07, this is the first thing that breaks on a MinGW host and it
is not obvious. The toolchain is not chosen by `rustup default`. The bootstrap
resolver `bootstrap_stage3_resolve_rust_toolchain`
(`scripts/check/lib/bootstrap-stage3/authority.shs:518-565`) reads
`channel = "stable"` out of `src/compiler_rust/rust-toolchain.toml` and then
runs `RUSTUP_TOOLCHAIN=stable rustc --print sysroot`. Bare `stable` expands to
`stable-<rustup's host triple>` — **not** to whatever `rustup default` points
at. On a host where rustup was installed MSVC-hosted, that yields
`stable-x86_64-pc-windows-msvc` even when `rustup default` is the gnu
toolchain, and the seed build dies with two errors at once:

```
error[E0463]: can't find crate for `core`
  = note: the `x86_64-pc-windows-gnu` target may not be installed
error: linking with `link.exe` failed: exit code: 1
  = note: link: extra operand '...rcgu.o'   <-- MSYS coreutils /usr/bin/link.exe,
          Try 'link --help' for more information.    not MSVC's linker
```

The second error is the giveaway: host build scripts (proc-macros) are being
built for the **msvc host**, no Visual Studio linker exists on this box, and
MSYS's `/usr/bin/link.exe` (a coreutils hardlink utility) answers instead.

Fix rustup's host, not the repo — `rust-toolchain.toml` is shared by every
platform and must not be pinned to one. `scripts/setup/host-env.shs` (sourced
in step 0) exports `SIMPLE_HOST_RUSTUP_HOST_TRIPLE` for this host from
`config/host/<hostname>.sdn`:

```sh
rustup set default-host "${SIMPLE_HOST_RUSTUP_HOST_TRIPLE:-x86_64-pc-windows-gnu}"
```

**That alone is not enough, and the reason is easy to miss.** The resolver
probes with `env -i`, which drops `RUSTUP_HOME` along with everything else. So
rustup does *not* read the home your interactive shell uses (this host's real
home is recorded as `rustup_home:` in `config/host/<hostname>.sdn`, exported
as `SIMPLE_HOST_RUSTUP_HOME`); it falls back to `%USERPROFILE%\.rustup`
(recorded as `rustup_fallback_home:`, exported as
`SIMPLE_HOST_RUSTUP_FALLBACK_HOME`). On this host that fallback home contained
**only** `stable-x86_64-pc-windows-msvc`, so the build failed a second time
with a log line still reading
`RUSTC=<fallback home>/toolchains/stable-x86_64-pc-windows-msvc/bin/rustc`
even after `rustup set default-host` had been run.

Make the fallback home resolve to the real one. Renaming the fallback home
directory is usually refused (`Permission denied` — an open handle), but
additive writes into it succeed:

```sh
cp "$SIMPLE_HOST_RUSTUP_HOME/settings.toml" "$SIMPLE_HOST_RUSTUP_FALLBACK_HOME/settings.toml"
powershell.exe -NoProfile -Command "New-Item -ItemType Junction \
  -Path '$SIMPLE_HOST_RUSTUP_FALLBACK_HOME\toolchains\stable-x86_64-pc-windows-gnu' \
  -Target '$SIMPLE_HOST_RUSTUP_HOME\toolchains\stable-x86_64-pc-windows-gnu'"
```

Use PowerShell's `New-Item -ItemType Junction`, not `mklink /J`: under Git Bash,
`cmd.exe /c 'mklink /J ...'` fails with "The filename, directory name, or volume
label syntax is incorrect" because MSYS rewrites the arguments, and
`MSYS2_ARG_CONV_EXCL`/`MSYS_NO_PATHCONV` do not suppress it here.

Verify with the exact probe the resolver performs — this is the check that
matters, not `rustup default`:

```sh
env -i PATH="$PATH" RUSTUP_TOOLCHAIN=stable rustc --print sysroot   # must end in -gnu
```

Once the host is gnu, linking goes through `gcc`/`ld` and MSYS's `link.exe` is
irrelevant.

## 1. Run phase 1

There is no `--stop-after-stage1` flag. The sanctioned receipt-free lane that
contains phase 1 is `--full-bootstrap --stop-after-stage2`; phase 1 completes
and is published before Stage 2 begins.

```sh
sh scripts/bootstrap/bootstrap-windows.sh \
  --full-bootstrap --stop-after-stage2 --backend=cranelift --no-mcp --verbose
```

On POSIX hosts call `scripts/bootstrap/bootstrap-from-scratch.sh` with the same
flags. The Windows entrypoint only adds
`scripts/setup/materialize-symlinks-windows.shs`, which converts the repo's git
symlinks into NTFS junctions — without it, dozens of source paths
(`src/compiler/backend` and friends) silently resolve to nothing.

Phase 1 is these three cargo invocations, split deliberately to defeat feature
unification (`bootstrap-from-scratch.sh:2138-2163`), each run under a private
`CARGO_HOME`/`CARGO_TARGET_DIR` authority workspace:

```
-p simple-driver          # the seed binary
-p simple-native-all      # native archive
-p simple-runtime --features runtime-symbol-table   # LAST, with LTO off
```

The result is published to `src/compiler_rust/target/bootstrap/simple<exe>`.

**Expect a long silent prefix.** Before cargo starts, the script fingerprints
every Rust seed input with `sha256sum` under `xargs`; on Windows that stage runs
for minutes with no output. `ps | grep sha256sum` confirms it is alive.

### Verify phase 1 by identity, never by exit code

```sh
src/compiler_rust/target/bootstrap/simple.exe --version
```

A phase-1 seed **must** print the seed warning banner:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; ...
Simple Language v1.0.0-rc.1
```

That banner is the artifact's honest self-identification. A binary that answers
`--version` cleanly *without* it is not a phase-1 seed. Per
`doc/08_tracking/bug/stage3_vacuous_binary_is_enum_discriminant_garbage_not_a_link_failure_2026-08-08.md`,
never accept exit code alone as proof.

## 2. Deploy phase 1 + both MCP servers into a temp root

```sh
sh scripts/setup/deploy-local-temp-mcp.shs
sh scripts/setup/deploy-local-temp-mcp.shs --root /c/temp/simple-deploy   # explicit root
```

It writes a throwaway tree and nothing else:

```
<root>/bin/simple.exe          copy of the phase-1 seed
<root>/bin/simple-mcp.cmd      seed `run src/app/mcp/main.spl`  (SIMPLE_LIB=<repo>/src)
<root>/bin/spipe-mcp.cmd       node examples/05_stdlib/spipe/mcp/server.js
<root>/.mcp.json               THE DELIVERABLE — absolute launcher paths
<root>/.mcp.verify.json        probe config for the launchability guard only
<root>/RECEIPT.env             seed sha256 + identity + timestamp
```

Verdict is the last line of stdout: `PASS — <n> artifact(s) deployed to <root>`
(exit 0), `FAIL` (exit 1), or `ERROR — nothing was deployed (<reason>)` (exit 2).
A run that deployed zero artifacts is ERROR, never a pass.

Three deployment details are load-bearing:

- **`simple-mcp` runs interpreted from source.** `bin/simple_mcp_server.cmd` in
  the repo hard-codes `bin/release/x86_64-pc-windows-**msvc**/`, which a
  MinGW (`windows-gnu`) host never populates, so that wrapper cannot resolve
  here. The temp launcher bypasses it and interprets `src/app/mcp/main.spl`
  directly — the same mode `.mcp.json` documents for the repo server.
- **Both commands are path-form.** `check-mcp-config-launchable.shs:150-156`
  **SKIPs** any server whose `command` contains no path separator (a
  PATH-resolved external launcher such as bare `node`), and a skipped server is
  not evidence. Declaring `bin/spipe-mcp.cmd` rather than `node` is what makes
  the spipe server actually get probed.
- **Two configs, on purpose.** The guard's `main()` hardcodes
  `root="$(dirname "$0")/../.."` — the *repo* root — and joins every declared
  command onto that, even when an external config path is passed as an
  argument. It never derives a base directory from the config file's own
  location. So a temp root elsewhere on disk can only be probed with
  repo-root-relative commands (`../../AppData/Local/Temp/.../bin/...`), which
  would be a bizarre thing to hand a real client. `.mcp.json` therefore carries
  absolute paths for actual use, and `.mcp.verify.json` carries the
  repo-root-relative form for the guard alone. Do not "fix" this by editing the
  guard.

## 3. Verify both servers with a real handshake

```sh
sh scripts/check/check-mcp-config-launchable.shs <root>/.mcp.verify.json
```

The guard asserts **content, not liveness**: each server must answer a real
`initialize` request with a well-formed `serverInfo.name` and a
`protocolVersion`. A silent `exit 0` with empty stdout fails — this exact server
was once a perfect silent green. Expected:

```
OK     simple-mcp       ... serverInfo.name=simple-mcp-full
OK     spipe            ... serverInfo.name=spipe
PASS — 2 declared server(s) checked, 2 answered initialize
```

Independent single-server probe, if you want to see the raw frame:

```sh
printf '%s\n' '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"probe","version":"1"}}}' \
  | timeout 30 node examples/05_stdlib/spipe/mcp/server.js
```

`spipe` answers `serverInfo:{"name":"spipe","version":"0.2.0"}` and has no
compiler dependency at all — it is pure node, so it is available before any
bootstrap has produced a `bin/simple`.

## 4. Tear down

The root is disposable; `deploy-local-temp-mcp.shs` `rm -rf`s and recreates it on
every run. Nothing under `bin/release/**` is touched, so there is no deployed
state to roll back.

## See also

- `.claude/rules/bootstrap.md` — why a seed must not masquerade as `bin/simple`
- `doc/07_guide/tooling/bootstrap_options.md` — the full flag surface
- `doc/07_guide/infra/phase_snapshots.md` — phase lineage snapshots
- `doc/07_guide/infra/spipe_mcp.md` — the spipe MCP surface
- `doc/07_guide/app/mcp/mcp.md` — `simple-mcp` wrapper contract and troubleshooting
