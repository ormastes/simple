# The interpreted lane IS a working local MCP server today — measured (2026-08-25)

- **Status:** MEASURED. No fix, no deploy performed. Written so a deploy
  decision can be taken on numbers.
- **Question:** the native-build route is a project
  (`mcp_native_build_reachability_assessment_2026-08-25.md`, 75 errors / 14
  kinds in the MIR phase alone). Does the INTERPRETED lane already satisfy the
  actual goal — a locally-deployed thing that can serve MCP?
- **Answer: yes.** It initializes, lists 154 tools, and executes real tool calls
  correctly, in **0.75 s startup / ~45 ms for two requests / 160 MB peak
  footprint**.

## What was run

Seed built fresh from `src/compiler_rust` at current `origin/main`
(`cargo build --release --bin simple`, 37,022,760 bytes). The server is run
**interpreted**, no native build anywhere:

```
<seed> run src/app/mcp/main.spl
```

Requests are newline-delimited JSON on stdin (`_mcp_read_message`,
`src/app/mcp/main.spl:321`, accepts a bare `{`-leading line as well as
Content-Length framing).

**Every request id is a per-run nonce** derived from the clock and pid, so a
canned or replayed reply cannot satisfy the check. All three responses echoed
their own nonce.

## Results

| probe | result |
|---|---|
| `initialize` | answered; `protocolVersion 2025-06-18`, `serverInfo simple-mcp-full 4.0.0`; nonce echoed |
| `tools/list` (`SIMPLE_MCP_TOOL_SET=all`) | **154 tools**; nonce echoed |
| `tools/list` (default `auto`) | 3 tools (`simple_pipe`, `simple_search`, `node_repl`) |
| `tools/call simple_search` | **real results**, nonce echoed |

The tool call is the part that distinguishes a working server from a handshake.
Searching for `_hir_optional_container_payload` returned

```
src/compiler/20.hir/hir_lowering/_Items/module_declarations_bootstrap.spl:148: ...
src/compiler/20.hir/hir_types.spl:734:fn _hir_optional_container_payload(t: HirTy...
```

— the exact symbol and sites landed in `3dc5b8dd8a2`. Run from the SHARED
working tree instead, the same query correctly returns `No results found`,
because that tree is behind `origin/main` and genuinely does not contain the
symbol (verified by grep: 0 vs 2 occurrences). So the tool reads the real
filesystem relative to cwd and is not fabricating either answer.

## What a user would feel

Fresh seed, `SIMPLE_MCP_TOOL_SET=all`, three runs each:

| measure | value |
|---|---|
| startup only (EOF immediately) | **0.751 / 0.758 / 0.749 s** |
| startup + `initialize` + `tools/list` | **0.799 / 0.801 / 0.793 s** |
| implied cost of the two requests | **~45 ms combined** |
| **peak memory footprint** | **167,903,880 B ≈ 160 MB** |
| max resident set size | 192,053,248 B ≈ 183 MB |

Footprint is `/usr/bin/time -l`'s **peak memory footprint**, the per-process peak
— not a `ps` RSS snapshot, per the standing rule. Max RSS is reported alongside
only for completeness.

`tool-set=all` (154 tools) is not slower than `auto` (3 tools) and costs ~1 MB
more footprint, so there is no reason to deploy the reduced set for performance.

## Why this matters for the decision

The native route needs, at minimum: an `enum match` arm-pattern feature, ~12
missing method lowerings, an inference/annotation pass over `infer-arm`,
`lower_range` in index position, an array-slice runtime helper, and a
resolution fix for 7 undefined type names — then borrow check (never executed on
this closure), codegen, link, and execution, all unmeasured.

The interpreted lane answers correctly today at sub-second startup. Whatever the
native project is worth, it is not on the critical path to *having a local MCP
server*.

## NOT verified

- **No deploy was performed.** `bin/simple` and
  `bin/release/aarch64-apple-darwin-macho/simple` are untouched (md5
  `0d8857b18e9e0cfaa50de2b08ad02512`, unchanged all session). Wiring this into
  `.mcp.json` is a separate, reversible change and is a decision, not a
  measurement.
- Only `initialize`, `tools/list` and one `tools/call` were exercised. 153 of
  the 154 tools were listed but not called.
- No concurrency, long-session, or crash-recovery testing. Sustained-load
  latency and memory growth over a long session are unmeasured; the numbers
  above are cold-start, single-shot.
- The seed prints `WARNING: this Rust-built Simple binary is a bootstrap seed
  only` on startup. Serving MCP from the seed is contrary to the standing
  "default tooling = pure-Simple self-hosted binary" rule, and that tension is a
  decision for whoever takes the deploy, not something measured here.
