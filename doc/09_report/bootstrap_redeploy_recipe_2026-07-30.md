# Bootstrap Redeploy Recipe — 2026-07-30

**Mechanical extraction** from `.claude/rules/bootstrap.md`, `.claude/rules/commands.md`, and `scripts/bootstrap/bootstrap-from-scratch.sh` (no execution). Goal: build a genuine pure-Simple `simple` binary and deploy to `bin/release/x86_64-unknown-linux-gnu/simple`.

---

## 1. Command Sequence (Order-Critical)

### Normal Pure-Simple Bootstrap (Reuses Existing Rust Seed)
```bash
# Prerequisites: LLVM installed, Rust seed already at src/compiler_rust/target/bootstrap/simple

# One-command full cycle (all stages + deploy):
scripts/bootstrap/bootstrap-from-scratch.sh --deploy

# Or, step-by-step:
# Stages 1–3 (pure-Simple), no deploy:
scripts/bootstrap/bootstrap-from-scratch.sh

# Then deploy after verification:
scripts/bootstrap/bootstrap-from-scratch.sh --deploy --full-cli
```

### Full Bootstrap (Rebuild Rust Seed First)
```bash
# Rebuilds src/compiler_rust/* via cargo, then pure-Simple stages:
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy
```

### For Windows (Git Bash or MSYS2)
```bash
scripts/bootstrap/bootstrap-windows.sh --deploy
```

### For FreeBSD (Must Run Inside FreeBSD)
```bash
# On FreeBSD:
scripts/bootstrap/bootstrap-from-scratch.sh --deploy

# On Linux (automated QEMU wrapper):
sh scripts/check/check-freebsd-bootstrap-qemu.shs --full
```

### Common Options
| Option | Effect |
|--------|--------|
| `--deploy` | Copy final artifacts to `bin/release/<triple>/` and create symlinks in `bin/` |
| `--full-bootstrap` | Rebuild Rust seed/runtime via cargo (if missing, stale, or sources changed) |
| `--backend=llvm` or `--backend=cranelift` | Codegen backend (default: llvm) |
| `--mode=dynload` or `--mode=one-binary` | Pure-Simple build mode; default: dynload |
| `--full-cli` | Relink the complete CLI (main.spl) after staged build |
| `--fresh-cache` | Clear native cache before rebuilding |
| `--no-mcp` | Skip MCP server builds (Stage 5) |
| `--release` | Deploy + run release-blocking whole test suite |
| `--jobs=N` | Native build parallelism (default: half CPUs) |

---

## 2. Expected Timing & Resource Usage

**Per the `.claude/memory/ref_*` and bootstrap.md:**

| Stage | Notes |
|-------|-------|
| Rust seed rebuild | ~5 min (11 crates) if needed; normally skipped via content-hash staleness detection |
| Stage 2 (seed→bootstrap_main) | Depends on `--mode` and cache state; dynload reuses objects |
| Stage 3 (bootstrap_main→bootstrap_main) | Verification/repetition of Stage 2 |
| Stage 4 (full CLI) | Dominant cost; ~minutes for native-build |
| Stage 4b (UI backend) | Cached native-build of src/app/ui/main.spl |
| Stage 5 (MCP servers) | Two parallel native-build passes |
| **Peak RAM (Stage 4)** | ~65 GB (unfixed; no incremental link yet) |
| **Overall (cold cache)** | Hours for full bootstrap; ~minutes incremental |

**Optimization notes:**
- `SIMPLE_NATIVE_INCREMENTAL=1` + stable `--cache-dir` = only changed modules recompile (reuses objects, but link+entry-closure discovery re-run every build)
- Worktree pitfall: fresh `git worktree` gets empty `build/`; copy `build/native_cache` from main tree or symlink it to avoid cold rebuilds

---

## 3. Output Locations & Artifacts

### Build Artifacts (Transient)
| What | Path |
|------|------|
| **Rust seed binary** | `src/compiler_rust/target/bootstrap/simple` (only used for bootstrapping) |
| **Rust runtime lib** | `src/compiler_rust/target/bootstrap/libsimple_native_all.a` |
| **Stage 2 binary** | `build/bootstrap/stage2/<triple>/simple` |
| **Stage 2 cache** | `build/bootstrap/native_cache/` (reused across stages) |
| **Stage 3 binary** | `build/bootstrap/stage3/<triple>/simple` |
| **Stage 3 provenance** | `build/bootstrap/stage3/<triple>/provenance.env` |
| **Stage 4 full CLI** | `build/bootstrap/full/<triple>/simple` |
| **Stage 4 UI backend** | `build/bootstrap/full/<triple>/simple_ui_backend` |
| **MCP servers (Stage 5)** | `build/bootstrap/full/<triple>/simple_mcp_server`, `simple_lsp_mcp_server` |

### Deployed Artifacts (Persistent)
| What | Path | Purpose |
|------|------|---------|
| **Production binary** | `bin/release/<triple>/simple` | Self-hosted pure-Simple compiler (default for all tools) |
| **Seed delegate** | `bin/release/<triple>/simple_seed` | Backup Rust seed (fallback only, never default) |
| **UI backend** | `bin/release/<triple>/simple_ui_backend` | Cached UI renderer backend |
| **MCP server** | `bin/release/<triple>/simple_mcp_server` | MCP interface (via native fallback wrapper) |
| **LSP MCP server** | `bin/release/<triple>/simple_lsp_mcp_server` | LSP via MCP bridge |
| **Wrapper symlinks** | `bin/simple` → `bin/release/<triple>/simple` | Platform-generic entry point |
| **Wrapper launchers** | `bin/simple_mcp_server`, `bin/simple_lsp_mcp_server` | Shell wrappers with probing logic |

### `<triple>` Examples
- Linux x86_64: `x86_64-unknown-linux-gnu`
- macOS aarch64: `aarch64-apple-darwin` or `aarch64-apple-darwin-macho`
- Windows MSVC: `x86_64-pc-windows-msvc`
- FreeBSD: `x86_64-unknown-freebsd-elf`
- SimpleOS: `x86_64-simpleos`

**The deployable artifact:** `bin/release/<triple>/simple` (Stage 4 full CLI binary, verified via Stage 3 and redeploy gate)

---

## 4. Rust Seed Copy Rule (Verbatim)

From `.claude/rules/bootstrap.md` line 30:
> **NEVER copy Rust bootstrap binary to `bin/release/simple`** — that's the self-hosted binary

**Policy (lines 10–22, bootstrap.md):**
- The Rust seed (`src/compiler_rust/target/bootstrap/simple`) is **bootstrap-only**.
- Default tooling (`test`, `lint`, `fmt`, `build`, `run`, MCP/LSP, doc-coverage) must run on the **pure-Simple self-hosted binary** (`bin/release/<triple>/simple`).
- If the self-hosted binary has a problem, **fix it in pure-Simple** (`src/compiler`, `src/lib`, `src/app`) and re-deploy.
- Reverting `bin/simple` to the seed is an **emergency stopgap only**, never the resting state; file a bug when you do it.

**During deploy:** The script installs `simple_seed` alongside `simple` in `bin/release/<triple>/` as a fallback delegate only (line 1049 of bootstrap script):
```bash
install -m755 "${seed_src}" "${seed_delegate}"
```
This seed is NOT the default and is NOT copied to `bin/release/simple`.

---

## 5. Prerequisites & Stated Constraints

### Required
1. **Existing Rust seed** (for normal bootstrap, skip this if `--full-bootstrap`):
   - File: `src/compiler_rust/target/bootstrap/simple`
   - Status gate: verified by content-hash (`seed_stamp` file tracks fingerprint)
   - If missing or stale + no `--full-bootstrap`: bootstrap exits with error

2. **Rust toolchain** (for `--full-bootstrap` only):
   - `rustc` and `cargo` discoverable in PATH
   - Sysroot resolved via `bootstrap_stage3_resolve_rust_toolchain`
   - Offline vendor directory: `src/compiler_rust/vendor/`

3. **LLVM 18+** (for `--backend=llvm`, the default):
   - Discovered via `scripts/setup/platform-detect.shs`
   - Export: `LLVM_PREFIX`, `LLVM_VERSION`, `LLVM_FOUND=1`
   - If missing and `--backend=llvm`: exits with error; use `--backend=cranelift` instead

4. **C compiler** for Rust authority builds:
   - `cc`/`gcc`/`clang` (resolved per-platform)
   - Linker: `mold`, `lld`, or platform default

5. **Platform tools:**
   - `sha256sum`/`shasum`/`openssl` (hash verification)
   - `timeout`/`gtimeout` (runnable limits)
   - `uname`, `which`, `find`, `sort`, `awk` (standard)

### Known Unmet or Broken (from memory refs)

**Memory ref: "stage4 bootstrap killed by resource-monitor 64GB cap"**
- **Issue:** Stage 4 peaks ~65 GB RAM (unfixed)
- **Impact:** May OOM on systems < 128 GB
- **Mitigation:** `SIMPLE_BOOTSTRAP_LOW_MEMORY=1` in bootstrap script attempts reduction; or use `--mode=dynload` to skip Stage 4

**Memory ref: "Native Dict.get/len are broken 2026-07-27"**
- **Issue:** Pure-Simple native codegen Dict/list methods corrupt or return wrong values
- **Mitigation:** Not blocking bootstrap itself, but affects compiled binaries; fixed in parallel commits

**Memory ref: "Deployed binary has NO LLVM codegen since Jul 29"**
- **Issue:** Some past deployments lost LLVM backend; measurements on non-canonical builds
- **Impact:** LLVM-less builds fail any LLVM-dependent tests
- **Guard:** `check-llvm-simd-row-native-arch.shs` (Linux Stage 3) verifies LLVM strings in binary

### No Stated Blocker for Bootstrap Itself
- FreeBSD bootstrap requires running **inside** FreeBSD (line 240–244): Linux host must use QEMU wrapper
- Windows full-CLI (`--full-cli`) requires native Windows host (line 230–236)

---

## 6. How to Identify Pure-Simple vs. Rust Seed Binary

### Quick Checks
| Attribute | Rust Seed | Pure-Simple Binary |
|-----------|-----------|-------------------|
| **Location** | `src/compiler_rust/target/bootstrap/simple` | `bin/release/<triple>/simple` |
| **Size** | Rust-compiled (~50–150 MB) | Native-compiled (~150–200+ MB or highly variable) |
| **Linker** | Rust's profile settings | Simple's native-build linker |
| **Version string** | `simple-bootstrap <VERSION>` | `simple-bootstrap <VERSION>` (same output) |

### Real Distinction: Runtime Behavior & Build Process

**Rust seed characteristics:**
1. Built via `cargo build -p simple-driver`
2. Prints to stderr (unless silenced):
   ```
   WARNING: compiling with the Rust seed compiler (not production-ready)
   ```
   (Suppress with `SIMPLE_RUST_SEED_WARNING=0` or `SIMPLE_BOOTSTRAP=1`)
3. Direct execution only for bootstrap; never default for `bin/simple`
4. Dependency: links against Rust runtime (libc, libstd)

**Pure-Simple binary characteristics:**
1. Built via `native-build` command (from Stage 2+ onward)
2. Entry point: `src/app/cli/main.spl` (full CLI) or `src/app/cli/bootstrap_main.spl` (bootstrap-only)
3. **Produces no Rust-seed warning** — entirely self-hosted
4. Binaries are **self-sufficient** in-process compilation (no subprocess calls to compiler)
5. **Deployed location:** `bin/release/<triple>/simple` (post-bootstrap)
6. **Symlinked as default:** `bin/simple` → `bin/release/<triple>/simple`

### Post-Deploy Verification

After `--deploy`:
```bash
# Confirm pure-Simple was deployed (no seed warning):
./bin/simple -c 'print(1+1)' 2>&1 | grep -i seed  # Should be empty

# Check it's self-hosted (compiles itself):
./bin/simple check src/app/cli/main.spl

# Verify redeploy gate gates passed (look for Stage 4 log):
cat build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-*.log | head -20
```

---

## Summary: One-Liner vs. Full Sequence

### Minimal (Single Command, All Stages + Deploy)
```bash
scripts/bootstrap/bootstrap-from-scratch.sh --deploy
```
Rebuilds pure-Simple Stage 2 → Stage 3 → Stage 4 (full CLI) → Stage 5 (MCP) → deploys to `bin/release/<triple>/simple`.

### Staged (If Debugging Individual Stages)
```bash
# Build only (no deploy):
scripts/bootstrap/bootstrap-from-scratch.sh

# Then inspect:
ls -lh build/bootstrap/stage{2,3,4}/<triple>/simple*
ls -lh build/bootstrap/full/<triple>/simple*

# Then deploy if satisfied:
scripts/bootstrap/bootstrap-from-scratch.sh --deploy --full-cli
```

### Full Rust + Pure-Simple (If Seed Is Stale or Missing)
```bash
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy
```
Invokes `cargo` to rebuild Rust seed/runtime first, then pure-Simple stages.

### Key Environment Variables (Optional)
```bash
SIMPLE_BOOTSTRAP_MODE=dynload          # Build mode (default)
SIMPLE_NATIVE_INCREMENTAL=1            # Per-module object cache reuse
SIMPLE_NO_STUB_FALLBACK=1              # Fail closed (no fallback to seed)
SIMPLE_BOOTSTRAP_LOW_MEMORY=1          # Attempt to reduce Stage 4 RAM peak
RUST_LOG=error                         # Rust toolchain verbosity
```

---

## Architecture Diagram (Simplified)

```
Rust seed
  ↓
[Stage 2: seed native-builds bootstrap_main.spl]
  ↓ (Stage 2 output)
[Stage 3: bootstrap_main self-compiles itself for verification]
  ↓ (Stage 3 output)
[Stage 4: verified compiler native-builds full main.spl]
  ↓ (Stage 4 output)
[Stage 4b: native-build cached UI backend]
  ↓
[Stage 5: native-build MCP servers (optional)]
  ↓
[Deploy: install to bin/release/<triple>/ and create symlinks]
  ↓
bin/simple ← self-hosted pure-Simple compiler (production)
```

---

## References

- **Policy:** `.claude/rules/bootstrap.md` (authoritative)
- **Quick commands:** `.claude/rules/commands.md`
- **Bootstrap script:** `scripts/bootstrap/bootstrap-from-scratch.sh`
- **Setup/symlinks:** `scripts/setup/setup.shs`
- **Platform detection:** `scripts/setup/platform-detect.shs`
- **Verification gates:** `scripts/check/cert/redeploy_gate/` (Stage 4 provenance & smoke tests)
- **MCP probing:** `scripts/check/check-mcp-native-smoke.shs`

---

**Generated:** 2026-07-30  
**Extraction source:** bootstrap.md (11 KB), bootstrap-from-scratch.sh (1200+ lines), commands.md, setup.shs  
**Status:** Mechanical extraction, no execution. Ready for manual bootstrap verification.
