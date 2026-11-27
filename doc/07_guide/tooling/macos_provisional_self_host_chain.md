# macOS provisional self-host chain

## Canonical Shared Phase 3 / Phase 4 Build on macOS & All Hosts (2026-11-22)

Before reaching for the provisional diagnostic chain adapter below, use the canonical shared cross-platform Phase 3 / Phase 4 build documented in [phase3_phase4_shared_build.md](phase3_phase4_shared_build.md) and [bootstrap_options.md](bootstrap_options.md):

1. **Shared Cross-Platform Phased Build (`scripts/bootstrap/build-phase3-phase4.sh` & `.bat`):**
   - One shared script across **Linux, macOS, FreeBSD, Windows (Git-Bash/MSYS2), and SimpleOS**.
   - Shows an **interactive Phased Build Menu** when invoked interactively without `--phase=...` (or with `--menu`), and accepts non-interactive `--phase=p3a|p3|p4|all`.
   - On Windows, `scripts/bootstrap/build-phase3-phase4.bat` delegates to `.sh` with 2 configs: **`mingw` is DEFAULT** (`--win-config=mingw`, `llvm-mingw` clang + `ld.lld`) and **`msvc` is optional** (`--win-config=msvc`, `clang-cl`).
   - Old standalone Phase 3/4 scripts (`p3-selfbuild-stage3.shs`, `p3-manual-link-stage3.shs`, `p3-smoke-stage3.shs`, `p3-targeted-stage2-build.shs`, `p3-entry-groups.shs`, etc.) are deprecated — invoking them directly pauses with migration instructions for `build-phase3-phase4.sh` (including phased/shard mode) and returns without building.
2. **Default Bootstrap Skips Phase 1 & Phase 2 Once Phase 3+ Exists:**
   - In `scripts/bootstrap/bootstrap-from-scratch.sh`, when a working native pure-Simple Phase 3+ host compiler already exists (`bin/release/<triple>/simple` or `bin/simple` without the Rust-seed banner), **default bootstrap skips Phase 1 (Cargo Rust seed) and Phase 2 (`seed -> stage2`)** and delegates directly to `scripts/bootstrap/build-phase3-phase4.sh` (`P3 -> P4`).
   - Pass `--from-seed` / `--cold-bootstrap` (or `--full-bootstrap` in CI) ONLY when intentionally rebuilding Phase 1 & Phase 2 from the Rust seed; pass `--skip-seed` to require an existing Phase 3+ compiler without seed fallback.
3. **Compile Mode (`shard` Default, `file` Optional) & `native_host_match` Unit Link:**
   - **`--compile-mode=shard` is DEFAULT** in `build-phase3-phase4.sh` (`SIMPLE_FILE_WORKERS=0`, `SIMPLE_HIR_SHARDING=1`, `SIMPLE_MIR_SHARDING=1`); **`--compile-mode=file` is optional** (`SIMPLE_FILE_WORKERS=1`).
   - `scripts/bootstrap/stage3-native-host-link-policy.{sdn,shs}` enforces the mandatory **`native_host_match` tag check** (`target (platform, cpu) == host (os, arch)`), minimizing `simple` to link **only** thin entry + `(platform, cpu)` static primitive archive (`libsimple-primitive-<platform>-<cpu>.a`) + dead-stripped primitive C core statically, while linking `lib/libsimple-{std,compiler-common,compiler,app}.dylib` (`.so`) dynamically.
   - **Phase 3 builds ONLY native host targets** — non-native backends (other CPUs, VHDL, GPU/CUDA/Vulkan, Wasm) are NOT built during Phase 3, **but if a `.dylib` already exists on disk, `simple` can load and use it** (`--backend-plugin <existing.dylib>`).
4. **Phase 4 Dual-Mode Build (`--xray` + Optimized Release):**
   - Phase 4 builds **both** the optimized production binary (`simple`: `--profile=prod --release --strip`) AND the XRay-instrumented debug binary (`simple-debug`: `--profile=dev --debug --no-strip --xray`), plus Stage 5 essentials (`simple_test_runner`, `simple_build_runner`, `simple_mcp_server`, `simple_lsp_mcp_server`).
5. **Protected Script Guard & Zero-Compile `--path-check`:**
   - Every core bootstrap script carries a top-of-file `PROTECTED BOOTSTRAP SCRIPT — DO NOT MODIFY UNLESS EXPLICITLY REQUESTED BY USER` banner.
   - Run `sh scripts/check/fast-verify-bootstrap-scripts.shs` for a sub-second check of sealed `.sdn` SHA-256 digests, protected banners, syntax, and `check-bootstrap-path-matrix-all.shs` across Unix/Windows/SimpleOS using extensible `PATH_ACTION|...|status=ALIVE` superset records without running actual compilation.

---

## Diagnostic Provisional Stage 2 Replay Adapter (`continue-macos-self-host-chain.shs`)

`scripts/bootstrap/continue-macos-self-host-chain.shs` runs a diagnostic
Stage 2 → Stage 3 → Stage 3 rebuild → Stage 4 compiler chain on Darwin when
the managed bootstrap runner is unavailable. It writes to a caller-owned,
fresh output directory and its adjacent `<output>.process.env` owner receipt.
The chain remains unadmitted and cannot publish or
promote artifacts. Whole-suite testing and GUI verification are separate work.

A run requires the immutable Stage 2 compiler and its canonical command
transcript. Supplying its native-build log and RSS receipt adds completion,
output-path, quiescence, and enforced-limit checks:

```sh
sh scripts/bootstrap/continue-macos-self-host-chain.shs \
  --source-root /path/to/frozen-checkout \
  --phase2 /path/to/stage2/simple \
  --phase2-transcript /path/to/stage2-command.transcript \
  --phase2-build-log /path/to/stage2-native-build.log \
  --phase2-rss-receipt /path/to/stage2-native-build.log.rss.env \
  --runtime-path /path/to/frozen-runtime \
  --sdk-root /Library/Developer/CommandLineTools/SDKs/MacOSX26.5.sdk \
  --deployment-target 26.5 \
  --output /path/to/new-chain-output \
  --backend llvm --jobs 10 \
  --rss-cap-kib 16777216 --timeout-seconds 7200
```

Choose a fresh absolute output path, backend, timeout, and RSS cap for the
machine. Supply the SDK root and deployment target used for this run. When the
Stage 2 transcript records either value, the adapter requires an exact match;
otherwise it records each as caller-provided diagnostic input. It hashes the
SDK's actual `SDKSettings.plist` without treating the installed SDK as a
release-wide canonical pin. The shared bootstrap policy and watchdog reject
RSS caps that exceed the host-derived limits.

`--stop-after-stage3` and `--stop-after-stage3-rebuild` are diagnostic stop-only
options. Their outputs cannot be resumed by this adapter; use the default for
one complete chain run.

The public adapter process becomes the shared watchdog for the entire chain.
Launch it from a clean, unmanaged shell. A public launch with either inherited
managed-session control is rejected before work starts; nested managed launch
is unsupported because the parent forbids descendant session escapes. The
adapter forces whole-session scope for its fresh session. Nested command guards
inherit that verified session. On cancellation, the outer
guard reaps all descendant process groups before returning and records the
result in `<output>.process.env`; require `quiescent=1` and no observer errors
before treating cleanup as verified. Each command retains its selected timeout;
the outer chain also has a finite lifetime of sixteen times that timeout.

The owner snapshots the source and runtime trees, pins the Stage 2 bytes,
transcript, adapter source, native tool environment, SDK settings, and optional
Stage 2 evidence. It checks Stage 2's version and Hello compile/run before
building P3. Each later compiler gets its own version oracle and Hello
compile/run; bootstrap compiler banners must match Stage 2, while the full CLI
Stage 4 must report its `Simple v...` banner. Compiler digests are checked
against the bytes that passed those probes before the next compiler is run.
Stage 3 uses all six roots from the Stage 2 transcript in the same order. A
producer that cannot accept six roots stops before running a compiler; the
adapter never drops a root.

A passing chain proves only that these local provisional artifacts were built
and passed their version and Hello probes. It does not record release
admission, whole-test results, or GUI behavior.
