# `app_mcp_intensive_spec` is not hung — it is an 84s spec, RED with 8 real failures

**Status:** MEASURED. The "hang" is a harness artefact. The spec itself is RED
against the product (8 real assertion failures) and is left RED.
**Filed:** 2026-08-10

## The claim under investigation

`test/02_integration/app/app_mcp_intensive_spec.spl` (and its twin
`test/integration/app/app_mcp_intensive_spec.spl`) "spawns
`bin/simple run src/app/mcp/main.spl` subprocesses and hangs past a 500s
timeout (killed, exit 143)". A prior stream restored the working copy and landed
nothing rather than guess.

## Measurement

All runs under `systemd-run --user --scope -p TasksMax=12`, stdin `</dev/null`,
same tree, same binary.

| Run | CPU guard | Result |
|---|---|---|
| `bin/simple test <spec>` | `SIMPLE_TIMEOUT_SECONDS=0` (OFF) | **rc=1, ELAPSED=83s**, `35 total, 27 passed, 8 failed` |
| `bin/simple test <spec>` | default (ON) | **rc=1, ELAPSED=84s**, `35 total, 27 passed, 8 failed` |

The legacy leg was measured too:

| Leg | Result |
|---|---|
| `test/02_integration/app/app_mcp_intensive_spec.spl` | rc=1, **84s**, `35 total, 27 passed, 8 failed` |
| `test/integration/app/app_mcp_intensive_spec.spl` | rc=1, **58s**, `5 total, 3 passed, 2 failed` |

The legs are a **baselined** divergent pair
(`scripts/check/test_tree_divergence_baseline.txt:1`), and the divergence is not
cosmetic: the legacy leg tags 6 of its 7 `describe` blocks
`tag: ["only-compiled"]`, so it executes **5 of the 35** examples the numbered
leg runs. It also drops `SIMPLE_MCP_TOOL_SET=all` from `_send_mcp_intensive`
(line 72) and uses bare-identifier dict keys. Anyone reading only the legacy
leg's `5 total` verdict is seeing an 86%-suppressed spec.

The spec **terminates in ~84 seconds and produces a verdict line**, with the CPU
guard at its default setting. It is:

- **not (b) a deadlock** — it completes, twice, and prints a verdict;
- **not (c) the DAP class** — it does not target a large file set (only 6 helper
  call sites spawn a subprocess, each with bounded input);
- **not (a) genuinely slow at the 500s scale** — ~84s, one order of magnitude
  below the reported timeout.

### Hypothesis explicitly falsified

The obvious explanation — `scripts/resource/kill_simple_monitor.shs` SIGTERMing
any `simple` process at `cpu>=60s`, which surfaces as exit 143 with no verdict
line and reads exactly like a hang — was **tested and is wrong here**: the
guard-ON run completed normally at 84s (row 2 above). Do not re-derive it.

### What is left

The 500s/exit-143 observation is not reproducible in a quiet environment. The
run that produced it was on a host that the same session reports was being
consumed by a self-delegating CLI fork bomb. Under
`systemd-run --user --scope -p TasksMax=12` with stdin closed, the spec is an
84s spec. Attribute the original timeout to **host resource starvation**, not to
the spec or the MCP subprocesses.

Note also that `slow_it` (`app_mcp_intensive_spec.spl:45`) is `fn slow_it(name,
block): it(name, block)` — a pass-through. It does **not** gate or defer
anything, so nothing in this file is actually opted out of a normal run; the
name is misleading.

The subprocess spawns are individually cheap and were separately measured:

| Spawn | Elapsed |
|---|---|
| `bin/simple run src/app/mcp/main.spl --help` | 1s, rc=0 |
| `printf '{...\"method\":\"ping\"}' \| bin/simple run .../main.spl` | 1s, rc=0, returns `{"jsonrpc":"2.0","id":9,"result":{}}` |

So the subprocesses account for a small fraction of the ~84s; the bulk is
in-process interpreter work across 35 examples.

## How to run it

```
systemd-run --user --scope -p TasksMax=12 \
  bin/simple test test/02_integration/app/app_mcp_intensive_spec.spl </dev/null
```

No env override is needed. Nothing about the spec needs changing to make it
terminate. Run it on a quiet host and close stdin.

## The 8 real failures (left RED)

```
MCP Source-Mode Protocol Coverage
  ✗ returns tool-level error for unknown source-mode MCP tool   expected false to equal true
MCP Server Lifecycle - Intensive
  ✗ validates server configuration                              expected 2024-11-05 to equal true
MCP Message Handling - Intensive
  ✗ validates request structure                                 expected tools/call to equal true
  ✗ handles error responses                                     expected Method not found to equal true
MCP Tool Integration - Intensive
  ✗ validates build parameters                                  expected examples/hello.spl to equal true
  ✗ handles format requests with options                        expected {dry_run: true} to equal true
  ✗ returns tool-level error for unknown source-mode MCP tool   expected false to equal true
MCP JJ Integration - Intensive
  ✗ handles diff requests                                       expected ghi789 to equal true
```

Six of the eight share one signature: `expect(<dict value>.?).to_be(true)`
(e.g. `app_mcp_intensive_spec.spl:138-139`) reports the **underlying text**
rather than the boolean of the `.?` presence operator — `expected 2024-11-05 to
equal true`. That is a `.?`-on-dict-value defect in the interpreter, not a spec
error: `.?` must yield `bool`. The remaining two (`expected false to equal true`)
are genuine product failures in unknown-tool error handling.

## Unblock condition

1. Fix `.?` so it evaluates to `bool` on a dict-value receiver (6 of 8 failures).
2. Fix unknown-tool error handling so the two `expected false to equal true`
   examples pass.

Then `35 total, 35 passed, 0 failed`. There is no harness change to make.

## Do not

Do not delete examples, mark the file pending, or split it up on the theory that
it is "too slow" — it is an 84s spec that finishes, and the 8 failures are the
point.
