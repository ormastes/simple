# SimpleOS Node.js AI CLI Migration Plan

**Created:** 2026-05-30
**Status:** Research complete, implementation pending
**Priority:** P1
**Depends on:** serial_sigsegv_and_test_hardening.md (P0)

## Executive Summary

Running Node.js-based AI CLI tools (Codex, Claude Code, Gemini) on SimpleOS
under QEMU is architecturally feasible. Each tool presents a fundamentally
different porting challenge:

| Tool | Architecture | Porting Path | Difficulty |
|------|-------------|--------------|------------|
| Codex CLI | Rust binary + thin JS shim | Cross-compile Rust, no JS engine needed | Medium |
| Claude Code | Node.js app | QuickJS + Node compat layer or bundle | Hard |
| Gemini CLI | React/Ink TUI (69 deps) | Full Node.js compat or heavy bundle | Hardest |

## Research Findings (adversarially verified)

### F1: JS Engine Selection — QuickJS wins (confidence: high, 8-1 vote)

| Engine | Score | Binary Size | Score/MB | ES Level | Multi-Arch |
|--------|-------|------------|----------|----------|------------|
| QuickJS | 1,001 | ~1 MB | 990 | ES2023 | x86_64, AArch64, RISC-V (C99) |
| V8 | 46,852 | 60.1 MB | 779 | ES2024 | x86_64, AArch64 (no RISC-V JIT) |
| Hermes | 1,571 | 36 MB | 43 | ES2020 | x86_64, AArch64 |
| Boa | 169 | 25.3 MB | 6 | ES2022 | All (Rust cross) |
| JerryScript | N/A | 483 KB | N/A | ES5.1 | All (embedded) |
| Node.js | N/A | 109 MB | N/A | ES2024 | x86_64, AArch64 |

**Decision: QuickJS** — 1MB binary, ES2023 (async/await, modules, generators,
Proxy, BigInt), pure C99 (trivial cross-compile to all 3 architectures),
already used by projects like txiki.js for Node.js API compatibility.

### F2: libuv Architecture (confidence: high, 11-1 vote)

- Single-threaded event loop, not thread-safe
- Platform backends: epoll (Linux), kqueue (BSD), IOCP (Windows)
- **POSIX poll(2) fallback** (`posix-poll.c`) used by Haiku/QNX/Cygwin
- Thread pool for: file I/O, DNS, user work (`uv_queue_work`)
- Graceful degradation via `UV_ENOSYS` for unsupported operations
- Requires: pthreads-compatible threading

### F3: libuv Custom OS Ports — Proven Path (confidence: high, 15-0 vote)

Two successful ports demonstrate feasibility:

**Unikraft (unikernel):**
- libuv v1.35.0 via POSIX/Unix backend
- 3 dependencies: pthread-embedded, newlib, lwIP
- Uses `posix-poll.c` instead of epoll
- Build flags: `-U__linux__ -D__GNU__`

**SerenityOS (custom OS):**
- libuv v1.51.0 with exactly 5 patches
- 140-line `serenity-core.c` for platform stubs
- Stubs: network interface enum (UV_ENOSYS), RSS memory (returns 0)
- Real impls: `uv_exepath`, `uv_uptime`, `uv_cpu_info`

**SimpleOS path:** Follow SerenityOS model — `simpleos-core.c` (~150 lines),
stub non-critical APIs with UV_ENOSYS, provide real impls for critical paths.

### F4: Codex CLI — Rust Binary (confidence: high, 9-0 vote)

- Codex CLI v0.135.0 is a **compiled Rust binary**, NOT a JS app
- Zero npm dependencies
- Pre-compiled for: linux-x64, linux-arm64, darwin-x64/arm64, win32-x64/arm64
- Thin `bin/codex.js` wrapper just spawns the native binary
- **No RISC-V variant exists**
- Porting path: cross-compile Rust source to SimpleOS targets
- This is a **Rust cross-compilation problem**, not a JS engine problem

### F5: Gemini CLI — Heavy React/Ink TUI (confidence: high, 7-2 vote)

- Requires Node.js >= 20
- Uses Ink (React-based terminal UI, fork @jrichman/ink v6.6.9) + React 19
- 69 runtime dependencies (ajv, zod, marked, js-yaml, dotenv, execa, glob, chokidar...)
- Mostly pure JS/TS — no native C/C++ compilation required
- Exception: `node-pty` in optionalDependencies (native addon for PTY)
- Pure-JS alternatives exist for node-pty (limited)
- **Heaviest porting target** — needs near-complete Node.js API surface

## Architecture Decision

### Two-Track Strategy

**Track A: QuickJS + Node Compat (Claude Code, Gemini CLI)**

```
┌─────────────────────────────────────────────────┐
│  AI CLI JS Bundle (esbuild single-file)         │
├─────────────────────────────────────────────────┤
│  Node.js Compat Layer (txiki.js-inspired)       │
│  ├─ fs, path, os, crypto, net, http, tls        │
│  ├─ child_process (stub/limited)                │
│  ├─ readline, tty                               │
│  └─ process, Buffer, EventEmitter               │
├─────────────────────────────────────────────────┤
│  QuickJS Engine (~1MB, ES2023)                  │
├─────────────────────────────────────────────────┤
│  libuv (POSIX poll backend, simpleos-core.c)    │
├─────────────────────────────────────────────────┤
│  SimpleOS Kernel (syscall surface)              │
│  ├─ open/read/write/close/stat/fstat            │
│  ├─ socket/connect/bind/listen/accept           │
│  ├─ poll/nanosleep                              │
│  ├─ mmap/mprotect/munmap                        │
│  ├─ pthread_create/join/mutex/cond              │
│  └─ getenv/getcwd/getpid                        │
└─────────────────────────────────────────────────┘
```

**Track B: Rust Cross-Compile (Codex CLI)**

```
┌─────────────────────────────────────────────────┐
│  Codex Rust Binary (cross-compiled)             │
├─────────────────────────────────────────────────┤
│  x86_64-unknown-simpleos target                 │
│  (reuse existing Rust stage1 sysroot work)      │
├─────────────────────────────────────────────────┤
│  SimpleOS Kernel + musl/newlib libc             │
└─────────────────────────────────────────────────┘
```

## Phased Implementation

### Phase 0: Kernel Syscall Surface Audit (1 week)

Verify SimpleOS provides the minimum POSIX surface for libuv:
- [ ] `open`, `read`, `write`, `close`, `stat`, `fstat`, `lstat`
- [ ] `socket`, `connect`, `bind`, `listen`, `accept`, `send`, `recv`
- [ ] `poll` (or `select` — libuv posix-poll.c needs one)
- [ ] `pipe`, `dup2`, `fcntl` (O_NONBLOCK, F_GETFL, F_SETFL)
- [ ] `mmap`, `mprotect`, `munmap` (for QuickJS memory)
- [ ] `pthread_create`, `pthread_join`, `pthread_mutex_*`, `pthread_cond_*`
- [ ] `clock_gettime`, `nanosleep`
- [ ] `getenv`, `getcwd`, `getpid`, `getuid`
- [ ] Document gaps as concrete implementation tasks

### Phase 1: QuickJS on SimpleOS (2 weeks)

- [ ] Cross-compile QuickJS to x86_64-simpleos, riscv64-simpleos, aarch64-simpleos
- [ ] Boot in QEMU, run `qjs -e "console.log('hello')"` via serial
- [ ] Verify: ES2023 features work (async/await, modules, generators)
- [ ] Serial marker: `[ai-cli] quickjs:hello target=<arch>`
- [ ] Binary size target: <2MB per arch

### Phase 2: libuv Port (3 weeks)

Following SerenityOS model:
- [ ] Create `src/runtime/vendor/libuv/simpleos-core.c` (~150 lines)
- [ ] Use `posix-poll.c` backend, disable epoll/kqueue
- [ ] Build flags: `-U__linux__ -DSIMPLEOS`
- [ ] Stub non-critical: `uv_interface_addresses` → UV_ENOSYS
- [ ] Stub non-critical: `uv_resident_set_memory` → 0
- [ ] Real impl: `uv_exepath`, `uv_uptime`, `uv_hrtime`, `uv_cpu_info`
- [ ] Thread pool: verify pthreads work under SimpleOS
- [ ] Test: `uv_run` event loop spins, timer fires, TCP connect works
- [ ] Serial marker: `[ai-cli] libuv:ready target=<arch>`

### Phase 3: Node.js Compat Layer (4 weeks)

Build minimal Node.js API compatibility on QuickJS + libuv:
- [ ] `fs.readFileSync`, `fs.writeFileSync`, `fs.existsSync`, `fs.statSync`
- [ ] `fs.promises.readFile`, `fs.promises.writeFile`
- [x] `path.join`, `path.resolve`, `path.dirname`, `path.basename` deterministic POSIX subset
- [x] `process.env`, `process.argv`, `process.cwd()`, `process.exit()` deterministic embedded subset
- [x] `Buffer` bounded string, array, Uint8Array, and ArrayBuffer subset
- [x] `EventEmitter` deterministic listener bookkeeping subset
- [ ] `net.Socket`, `net.createConnection` (via libuv tcp)
- [ ] `http.request`, `https.request` (via libuv + mbedTLS/BearSSL)
- [x] `crypto.createHash` (sha256/sha1 deterministic subset)
- [x] `crypto.randomBytes` fail-closed subset until secure entropy is wired
- [ ] `child_process.spawn` (limited — stub or real based on kernel support)
- [ ] `os.platform()`, `os.arch()`, `os.tmpdir()`
- [ ] `readline` (for terminal interaction)
- [ ] Test: run a simple Express-like HTTP server
- [ ] Serial marker: `[ai-cli] node-compat:ready target=<arch>`

### Phase 4: CLI Bundle + Smoke Test (2 weeks)

**Claude Code:**
- [ ] Bundle with esbuild: `esbuild --bundle --platform=node --target=es2022`
- [ ] Identify native addon deps, find pure-JS alternatives
- [ ] Test: `claude --version` prints version string
- [ ] Serial marker: `[ai-cli] cli-smoke:start app=claude`

**Codex CLI (Track B):**
- [ ] Add `x86_64-unknown-simpleos` Rust target (reuse stage1 sysroot)
- [ ] Cross-compile Codex Rust binary
- [ ] Test: `codex --version`
- [ ] Add RISC-V and AArch64 targets
- [ ] Serial marker: `[ai-cli] cli-smoke:start app=codex`

**Gemini CLI:**
- [ ] Bundle core package + 69 deps with esbuild
- [ ] Stub/replace `node-pty` with terminal passthrough
- [ ] Stub React/Ink rendering to serial console output
- [ ] Test: `gemini --version`
- [ ] Serial marker: `[ai-cli] cli-smoke:start app=gemini`

### Phase 5: Security Hardening (2 weeks)

Leverage existing `AiCliManifest` capability system:
- [ ] File access: enforce `file_grants` at VFS layer, deny undeclared paths
- [ ] Network: enforce `network_grants` at socket layer, allowlist endpoints only
- [ ] Process: enforce `process_grants`, deny undeclared spawns
- [ ] Credentials: enforce `credential_grants`, block ambient env var reads
- [ ] Compare with Deno permissions model (`--allow-read`, `--allow-net`)
- [ ] Add Node.js `--experimental-permission`-style flags to QuickJS launcher
- [ ] Test: all denial paths from existing `simpleos_ai_cli_js_node_port_spec.spl`
- [ ] Serial marker: `[ai-cli] hardening:ok app=<tool>`

### Phase 6: Full QEMU Validation (1 week)

All three architectures, all three tools:
- [ ] x86_64 (q35 + OVMF UEFI): boot → QuickJS → CLI smoke → serial evidence
- [ ] RISC-V rv64gc (virt + OpenSBI): boot → QuickJS → CLI smoke → serial evidence
- [ ] AArch64 (virt + U-Boot): boot → QuickJS → CLI smoke → serial evidence
- [ ] FAT32 disk image provisioning with runtime + CLI bundles
- [ ] Automated serial capture and marker verification
- [ ] Update `ai_cli_qemu_lane` runtime_status from "blocked-runtime-artifact" to "ready"

## Minimum Syscall Surface Required

```
# File I/O (Phase 0)
open, openat, read, write, close, stat, fstat, lstat, ftruncate
lseek, readv, writev, pread, pwrite
mkdir, rmdir, unlink, rename, readdir/getdents
fcntl (F_GETFL, F_SETFL, O_NONBLOCK, O_CLOEXEC)
dup, dup2

# Networking (Phase 0)
socket, connect, bind, listen, accept, accept4
send, recv, sendto, recvfrom, sendmsg, recvmsg
getsockopt, setsockopt, getsockname, getpeername
shutdown

# Event Loop (Phase 2)
poll (or ppoll) — used by posix-poll.c
pipe, pipe2
eventfd (optional — posix-poll.c works without)

# Memory (Phase 1)
mmap, munmap, mprotect, mremap
brk (or sbrk)

# Process (Phase 3)
fork (or posix_spawn), execve, waitpid, _exit
kill, getpid, getppid, getuid, getgid

# Threading (Phase 2)
clone (for pthreads), futex
pthread_create, pthread_join, pthread_mutex_*, pthread_cond_*

# Time (Phase 1)
clock_gettime, gettimeofday, nanosleep

# Misc (Phase 1)
getcwd, chdir, getenv, uname, getrandom
```

## Risk Register

| Risk | Mitigation |
|------|-----------|
| Claude Code has undocumented native addons | Bundle analysis + pure-JS fallbacks |
| Gemini's React/Ink needs full TTY/PTY | Serial-only rendering mode for QEMU |
| QuickJS ES2023 gaps break CLI bundles | Test with qjs on host first, before porting |
| libuv poll backend too slow for real workloads | Acceptable for smoke test; optimize later |
| RISC-V pthreads broken in SimpleOS | Phase 0 audit catches this early |
| TLS (HTTPS) needs crypto library | BearSSL or mbedTLS, both cross-compile well |

## References

- QuickJS benchmark: github.com/ahaoboy/js-engine-benchmark
- libuv design: docs.libuv.org/en/v1.x/design.html
- libuv UV_ENOSYS pattern: github.com/libuv/libuv/issues/1287
- Unikraft libuv port: github.com/unikraft/lib-libuv
- SerenityOS libuv port: github.com/SerenityOS/serenity/tree/master/Ports/libuv
- Codex CLI npm: npmjs.com/package/@openai/codex
- Gemini CLI: github.com/google-gemini/gemini-cli
