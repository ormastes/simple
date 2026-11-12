# native-build MCP server closure blocked on both available producers (aarch64 Linux host)

Date: 2026-11-12
Host: aarch64 Linux (20 cores), NVIDIA GB10 GPU, 121 GB RAM
Lane: work/native-build-mcp-blocker-20261112

## Symptom

`native-build --entry-closure` of `src/app/mcp/main.spl` (and
`src/app/simple_lsp_mcp/main.spl`) cannot produce a binary on this host with
either available producer, which in turn blocks the POSIX MCP wrapper's
hash-admitted native path (`bin/simple_mcp_server` exits 127
"native simple_mcp_server not found") and therefore the native MCP redeploy.

## Attempt 1 — phase snapshot producer (build/phase_snapshots/phase1_1793951660_phase2_1793952172/simple, Nov 6, simple-bootstrap 1.0.0-rc.1)

Against origin/release/1.0.0 tip source (81c8a7368da):

- Source closure compiled fine (268/268 files), parse fibers fine.
- Parse phase then ran >8 wall-clock hours without finishing: 17
  `parse_shard_main.spl` shard children at ~97% CPU each, followed by
  `[parse-shard] shard=0/17 pid=... FAILED TIMEOUT (orchestrator wait expired)`.
- Killed manually. Root cause hypothesis: the Simple-compiled producer runs
  its own CLI parse shards through `simple run` (JIT/interpreted path),
  which is ~100-1000x slower than compiled execution for this closure size;
  the shard orchestrator timeout is shorter than shard completion time under
  host load (load average ~15 from concurrent agent sessions).

## Attempt 2 — Rust seed producer (src/compiler_rust/target/bootstrap/simple, Nov 5 18:12)

Against tip source: the seed JIT fails to compile the native_build driver
(`call to MirLowering.emit_resolved_direct_call omits argument 4 whose default
is not a call-site constant [in src/app/cli/native_build_main.spl]`), demotes
it to the interpreter, and the hir phase then fails with
`[hir-shard] profile admission rejected: no closure request published` →
`error: HIR aggregate failure` after ~50 min.

Against era-matched source (checkout 671d5545201, Nov 5 13:25, the main
worktree base): the same JIT demotion occurs, and after ~4.4 hours the build
dies in surface_freeze / hir with a single root error
`error: semantic: type mismatch: cannot convert string to int` (no file path
in the shard output) which blocks the HIR ledger and cascades into
`HIR shard ledger claim failed: ledger-blocked` for every remaining module.
Hypothesis: the seed binary was built at 18:12 from a tree ~5h newer than
671d5545201 (its inputs fingerprint has no commit id; exact source commit not
recovered), so even "era-matched" source is not exactly the seed's source.

## Impact / workaround

- MCP servers for kimi/codex/claude/gemini on this host are deployed in the
  source-run form (`bin/mcp_stdio_bridge.js` + seed `simple run <entry>`,
  ~5-20 s initialize warmup, verified Connected on claude 2.x and
  gemini-cli 0.68.0 on 2026-11-12). Configs live in user scope
  (~/.kimi-code/mcp.json, ~/.codex/config.toml, ~/.gemini/settings.json) and
  locally in the repo (.mcp.json, .gemini/settings.json) — the repo-local
  forms intentionally diverge from upstream's wrapper/native convention
  until a native binary exists.
- This violates the production preference for cached compiled artifacts
  (AGENTS.md critical rule); it is a deliberate interim state, not a
  normalization.

## Open questions

1. Which commit exactly is the Nov 5 18:12 seed's source? Recovering it
   (matching category_compiler_sources_sha256=9977c2c0... over 43715 files)
   would allow a fully era-matched retry.
2. Is the shard orchestrator parse timeout tunable (env) for the snapshot
   producer, or can parse shards run pre-compiled instead of via
   `simple run` on the producer's own CLI path?
3. The seed JIT limitation on default-valued cross-module call arguments
   (`emit_resolved_direct_call` omits argument 4) is a seed/frontend gap that
   forces the 100-1000x interpreter demotion of the native_build driver.

## Evidence

- /tmp/mcp_build_1.log, /tmp/mcp_build_seed_1.log, /tmp/mcp_build_base_1.log
  (retained on host; not committed)
