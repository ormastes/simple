# Local LLM setup: slang backend + caret (and driving spipe from it)

How to run a local GGUF model through slang's ggml backend and use it from
caret — including letting the local model run the spipe (SSpec) development
flow. Verified 2026-09-16 on a GB10 host (128G unified memory) with
`Qwen3-Coder-Next-Q4_K_M` (4-shard, 46G) and `Qwen3.5-9B-Q3_K_M` (4.7G); the
server and caret-suite sections (6-10) were verified 2026-11-12 with
`Qwen3-Coder-30B-A3B-Q4_K_M`.

## 1. Put a GGUF model under a model root

slang reads models as **directories** under a model root. One directory per
model, GGUF file(s) inside (multi-shard is fine):

```
/home/yoon/dev/model/
  Qwen3-Coder-Next-Q4_K_M/   *.gguf (4 shards)
  Qwen3.5-9B-Q3_K_M/         Qwen3.5-9B-Q3_K_M.gguf
```

Download quants with the `hf` CLI (specify the file — a bare `hf download`
of a repo pulls every quant):

```bash
hf download unsloth/Qwen3.5-9B-GGUF Qwen3.5-9B-Q3_K_M.gguf \
  --local-dir /home/yoon/dev/model/Qwen3.5-9B-Q3_K_M
```

Non-GGUF models (safetensors BF16/NVFP4) are recognised and refused with a
typed reason — expected, not a bug. Architecture support follows the linked
llama.cpp revision (Qwen3.5 needs `qwen35` graph builders).

## 2. Build the ggml backend shim in the tree you run from

The shim links against a llama.cpp build. `scripts/check/build-slang-ggml-shim.shs`
defaults `LLAMA_ROOT` to `/home/yoon/dev/llama.cpp`; a fresh host has no `build/`
there, so build it first (once per host, not per worktree).

### llama.cpp with CUDA (clang-18 host compiler)

nvcc 13.0 rejects clang >= 21 as the host compiler ("unsupported clang version!
clang version must be less than 21"), so pass clang-18 explicitly. Never GCC
(repo rule).

```bash
cd /home/yoon/dev/llama.cpp
cmake -S . -B build -G Ninja -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_COMPILER=/usr/bin/clang-18 \
  -DCMAKE_CXX_COMPILER=/usr/lib/llvm-18/bin/clang++ \
  -DCMAKE_CUDA_HOST_COMPILER=/usr/lib/llvm-18/bin/clang++ \
  -DBUILD_SHARED_LIBS=ON -DGGML_CUDA=ON -DGGML_NATIVE=ON -DLLAMA_CURL=OFF \
  -DLLAMA_BUILD_TESTS=OFF -DLLAMA_BUILD_EXAMPLES=OFF -DLLAMA_BUILD_SERVER=OFF
cmake --build build -j 10
```

Then, in each worktree:

```bash
sh scripts/check/build-slang-ggml-shim.shs   # -> build/sffi/libslang_ggml.so
```

Run this **per worktree**. `backend.spl` dlsyms an exact symbol set from the
shim; a shim built from older source dies with
`spl_dlsym: unresolved symbol 'slang_ggml_capabilities'`. A fresh worktree has
no `build/sffi/` at all — without the shim you get "GGUF recognised but no
ggml backend library is configured". `SLANG_GGML_LIB=<path>` overrides the
default location.

### Windows (clang-cl + lld-link; verified 2026-10-03, Windows 11, CPU only)

```bash
# llama.cpp outside the repo, shared libs, clang-cl (never cl). VS's bundled
# cmake/ninja; LLVM 21 first on PATH.
. scripts/setup/windows-msvc-bootstrap-env.shs
export PATH="/c/dev/install/clang+llvm-21.1.3-x86_64-pc-windows-msvc/bin:$PATH"
git clone --depth 1 --branch b11371 https://github.com/ggml-org/llama.cpp D:/tools/llama.cpp
cmake -S D:/tools/llama.cpp -B D:/tools/llama.cpp/build -G Ninja -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_COMPILER=clang-cl -DCMAKE_CXX_COMPILER=clang-cl -DCMAKE_LINKER=lld-link \
  -DBUILD_SHARED_LIBS=ON -DGGML_NATIVE=ON -DGGML_OPENMP=OFF -DGGML_CUDA=OFF -DGGML_VULKAN=OFF \
  -DLLAMA_CURL=OFF -DLLAMA_BUILD_TESTS=OFF -DLLAMA_BUILD_EXAMPLES=OFF -DLLAMA_BUILD_SERVER=OFF
cmake --build D:/tools/llama.cpp/build -j 8   # llama.dll + ggml*.dll; a few tool
                                              # exes fail to link, not needed

LLAMA_ROOT=D:/tools/llama.cpp sh scripts/check/build-slang-ggml-shim.shs
# -> PASS -- 50 symbol(s) exported, .../build/sffi/slang_ggml.dll
```

- The shim is `build/sffi/slang_ggml.dll` (exports from a `.def` generated off
  the compiled object). The script copies `llama.dll` and `ggml*.dll` next to
  it, and `backend.spl` preloads those siblings before opening the shim, so no
  PATH edit is needed (Windows does not search a DLL's own directory for its
  imports).
- `llm_engine.spl` resolves the backend as: `engine_set_lib_path` >
  `SLANG_GGML_LIB` > per-OS default (`slang_ggml.dll` on Windows, else
  `libslang_ggml.so`).
- The memory gate reads `Win32_OperatingSystem` via PowerShell
  (`FreePhysicalMemory`, `TotalVisibleMemorySize`): ~1.2 s per probe, two
  probes per model load.
- Run Simple with a phase-1 seed that matches the tree's stdlib, e.g.
  `SIMPLE_BINARY=build/p1-target/x86_64-pc-windows-msvc/bootstrap/simple.exe`.
  An older seed dies before reaching slang (`rt_process_run_bounded:
  max_output_bytes must be a non-negative integer`).
- Model choice: caret flattens the transcript into a raw `user:/assistant:
  <think>` completion with the tool-use system prompt rather than the GGUF's
  chat template. Qwen2.5-0.5B-Instruct generates but does not follow it (it
  answered a code fence); Qwen2.5-1.5B-Instruct Q4_K_M does.

## 3. Sanity gates

```bash
# every model dir under a root reaches a verdict through caret
sh scripts/check/check-slang-ggml-inference.shs --models /home/yoon/dev/model

# one-shot prompt (no tools, prints the reply, exits)
SLANG_MODEL_ROOT=/home/yoon/dev/model bin/caret \
  --provider slang_local --model Qwen3.5-9B-Q3_K_M \
  --prompt "Say exactly: hello world"
```

`SLANG_MODEL_ROOT` is required unless your models live under `./models`.

## 4. The agent tool loop lives in the TUI (headless via tmux)

`--prompt` is one-shot: it prints a single reply and exits — the bash /
read_file / write_file tool loop (`run_agent_loop`) only runs in the TUI. To
run it headless, give it a PTY with tmux:

```bash
tmux new-session -d -s caret-agent -x 220 -y 50 \
  "cd <your-worktree> && \
   SLANG_MODEL_ROOT=/home/yoon/dev/model \
   SIMPLE_RUST_SEED_WARNING=0 \
   <simple-binary> run src/app/llm_caret/main.spl \
     --provider slang_local --model Qwen3-Coder-Next-Q4_K_M \
     --workspace <your-worktree> --dangerously-allow-all"

tmux send-keys -t caret-agent "your instruction" Enter
tmux capture-pane -t caret-agent -p          # read progress
tmux link-window -s caret-agent:0 -t 0:8     # watch it in your own session
```

Notes:
- `--workspace <path>` sandboxes the bash/read/write tools; ALWAYS point it
  at an isolated worktree, never the shared main checkout.
- `--dangerously-allow-all` auto-approves mutating tools — only with an
  isolated workspace underneath.
- The TUI needs a seed binary built after 2026-09-07 (the
  `rt_atexit_install` interpreter bridge); the sealed seed at
  `src/compiler_rust/target/bootstrap/simple` has it.
- Worktrees also need a `bin/simple` (symlink one in) and their own
  `build/sffi/libslang_ggml.so` (step 2).

## 5. Letting the local model run spipe

The spipe/SSpec process is documented in `.claude/skills/spipe.md`; the model
reaches it through caret's bash tool. Prompt pattern that works:

```
You are in a clean worktree (branch work/<topic>, cwd <worktree>).
1) Read .claude/skills/spipe.md for the spipe SSpec process.
2) Run the unit tests for a bounded area:
   bin/simple test test/01_unit/<area>
3) If any test fails, diagnose and fix src/ per .claude/rules/language.md,
   re-run until green.
4) Do NOT git commit; leave fixes in the working tree.
Finish with: tests run, pass/fail, files changed, root cause per fix.
```

Forcing "do NOT commit" keeps the landing decision with the human session
that owns the lane (per `.claude/rules/vcs.md`, worktrees are where ordinary
changes are authored, and a local model must not push). The parallel-agent
pattern in section 8 does the opposite on purpose: each agent owns its own
worktree and branch and opens its own PR.

## 6. Run the slang OpenAI-compatible server

Verified 2026-11-12 (GB10, `Qwen3-Coder-30B-A3B-Q4_K_M`, 18.5 GB:
`hf download unsloth/Qwen3-Coder-30B-A3B-Instruct-GGUF
Qwen3-Coder-30B-A3B-Instruct-Q4_K_M.gguf --local-dir
/home/yoon/dev/model/Qwen3-Coder-30B-A3B-Q4_K_M`).

```bash
cd <worktree> && SIMPLE_RUST_SEED_WARNING=0 SIMPLE_TIMEOUT_SECONDS=0 \
  <seed> run src/app/slang_server/main.spl -- \
  --plaintext-development --models=/home/yoon/dev/model \
  --model=Qwen3-Coder-30B-A3B-Q4_K_M --port=8721 --n-ctx=32768
```

- `--model=<id>` is required (PR #8514). The server preloads that model at
  startup, so a load failure (memory gate, CUDA init) appears before the port
  opens, not on the first request.
- One server process serves several concurrent sessions (PR #8514; verified with
  two caret agents at once). Each request renders the whole `messages` list
  through the GGUF chat template. Two long generations together take about 1.9x
  the time of one: decode is not yet batched.
- `--plaintext-development` is mandatory (loopback dev only; production needs TLS).
- `--n-ctx=<tokens>` sets the per-request context. The default 4096 is too small
  for a caret agent (tool prompt plus one file read overflows it); caret's
  in-process `slang_local` path uses 32768. A non-positive or non-numeric value
  fails with `Error: --n-ctx must be a positive integer`.
- Endpoints: `GET /v1/models` (every model slang recognises on disk, runnable or
  not) and `POST /v1/chat/completions` (real tokens for GGUF; 503
  `model_not_runnable` with a reason otherwise).

Smoke test (Bash `curl`/`wget` are blocked by repo hooks; use `nc`):

```bash
printf 'POST /v1/chat/completions HTTP/1.1\r\nHost: 127.0.0.1\r\nContent-Type: application/json\r\nContent-Length: <n>\r\nConnection: close\r\n\r\n<json>' \
  | nc -q 900 127.0.0.1 8721
```

For "Say exactly: hello world" the reply was
`{"choices":[{"message":{"role":"assistant","content":"\n\nHello world!"}}]}`.

**Do not wrap the server in `systemd-run -p MemoryMax=...`.** On GB10 the CUDA
context is host memory charged to the cgroup, and `cudaSetDevice` then fails
with "out of memory" in `ggml_cuda_init`. slang's own fit gate
(`memory_budget.spl`: MemAvailable minus 1/16 of total as headroom) is the guard.

Seed-age prerequisites (the server and caret run on the Rust seed):

- A seed built before 2026-11-09 (commit `afb36d2e0a5`, process-global
  interpreter socket registry) cannot serve HTTP: connections hang in CLOSE-WAIT
  and `GET /v1/models` never answers.
- A seed without PR #8492 (merged 2026-11-12 into `release/1.0.0`) reads
  `/proc/meminfo` as an empty string, so the memory gate refuses every model
  ("could not establish available memory (no MemAvailable in /proc/meminfo
  ...)"). It also lacks `--n-ctx`.
- Rebuild: `cd src/compiler_rust && cargo build --release --bin simple`
  (`target/release/simple`, ~1.5 min warm).

## 7. Point caret at the server

Provider `slang` is an HTTP client to `SLANG_BASE_URL` (default
`http://localhost:8721`); `slang_local` is the in-process engine (needs
`SLANG_MODEL_ROOT`, no server). Config file (section headers unindented and
ending in `:`, keys indented):

```
defaults:
    provider: slang
slang:
    base_url: http://127.0.0.1:8721
    model: Qwen3-Coder-30B-A3B-Q4_K_M
```

```bash
<seed> run src/app/llm_caret/main.spl --config <file> \
  --workspace <isolated worktree> --dangerously-allow-all
```

`--prompt "..."` prints one reply and exits; the tool loop runs only in the TUI.

Tool notes (PR #8514):
- `bash` runs in `--workspace`, not in caret's own working directory.
- `edit_file(path, old_text, new_text)` writes only when `old_text` occurs
  exactly once, so tell local models to use it instead of `write_file`. A 30B
  model rewriting a whole file with `write_file` truncated it twice in testing.

## 8. Caret suite (cs)

`cs` is a dashboard that launches and watches several agents in tmux panes.
Run it inside a tmux window (verified in a window named `caret-suite`, pane
backend shown as `connected: smux`):

```bash
bin/cs [session]          # wraps bin/caret with CARET_ENTRY=src/app/llm_caret/cs_main.spl
SIMPLE_BINARY=<seed> <seed> run src/app/llm_caret/cs_main.spl <session-name>   # direct
```

`SIMPLE_BINARY` selects which `simple` spawns the agents (order: `SIMPLE_BINARY`,
`PATH`, `bin/simple`).

Dashboard: header `cs <session> · connected: <backend> · N agents · N running`;
an AGENTS list; DETAIL (spec, pane id, pid, status, cpu, rss, stderr path
`/tmp/cs-<session>-<agent>.stderr`); LOG; the live screen of the selected
agent's pane on the right; an input line at the bottom.

| Command | Effect |
|---|---|
| `/launch <spec> [args...]` | start an agent |
| `/switch <n\|id>` | select an agent |
| `/max` | maximise the selected pane |
| `/key <enter\|esc\|tab\|space\|up\|down\|left\|right\|ctrl-c>` | send a key |
| `/kill <n\|id>` | kill an agent |
| `/agents` | list agents |
| `/help`, `/quit` | help, exit |

Any non-command line is sent as chat to the selected agent's pane.

Spec grammar: `harness[:provider][/model]`. Harnesses: `claude`, `codex`,
`kimi`, `opencode`, `gemini`, `caret`. Only `caret` takes a provider
(`claude_api`, `openai`, `openai_compat`, `kimi`, `glm`, `slang`, `slang_local`,
`local_torch`, `dummy`, `deepseek`); a caret spec spawns
`simple run src/app/llm_caret/main.spl --provider P --model M`.

Words after the spec (PR #8492) are appended verbatim to the agent argv. They
are split on spaces, so an argument containing spaces is not supported, and a
typo after the spec becomes an agent argument. Two agents, each with its own
config and workspace:

```
/launch caret:slang/Qwen3-Coder-30B-A3B-Q4_K_M --config /path/agent-a.sdn --workspace /path/worktree-a --dangerously-allow-all
/launch caret:slang/Qwen3-Coder-30B-A3B-Q4_K_M --config /path/agent-b.sdn --workspace /path/worktree-b --dangerously-allow-all
```

Pattern used for parallel bug fixing: one isolated worktree plus a
`work/<topic>` branch per agent (`branch.<b>.merge=refs/heads/release/1.0.0`),
and a short `build/TASK.md` brief per bug (file:line, repro spec, expected
result, fix sketch, landing steps). Each agent commits, pushes its branch and
runs `gh pr create --base release/1.0.0`; a higher model reviews and
admin-merges. Keep briefs short: a 30B local model cannot digest
`.claude/skills/spipe.md`.

Agents inside podman (PR #8532): `/launch <spec> --container <image>
[--container-mount src:dst[:ro|rw]] [--container-network ...]` runs the agent
through the Simple container layer (`podman_session_v1`). `/kill`, `/quit` and
cs exit remove the container; `/reap` removes leftovers. With `busybox` add
`--container-mount /lib/aarch64-linux-gnu/libgcc_s.so.1:/lib/libgcc_s.so.1`,
and pass the served model name (the default `slang-local` is rejected). Details:
`doc/00_llm_process/feature_expert/podman_container/skill.md`.

Driving a cs agent from outside (for example `tmux send-keys`): the chat line
types text into the agent pane but does not submit it; follow it with
`/key enter`.

## 9. Known issues (open)

- **GB10 intermittent CUDA OOM.** CUDA context creation can fail with "out of
  memory" in `ggml_cuda_init` when a second CUDA process starts while a slang
  process holds a loaded model. Run one server for all agents.
- **Prefix-restore crash.** After hours of two-agent load, the server aborted
  with `CUDA error: an illegal memory access` right after
  `state_read_meta: cell_count = 15809` (restoring a cached prompt prefix).
  Restart the server; a fix is in progress.
- **JIT demotion.** Fixed: `dir_list` (PR #8524), `RingTelemetry` (PR #8518)
  and `jo1(p1:)` (PR #8531). Still open: an unbraced single-symbol
  `use a.b.fn` is not counted as an import by the co-compiled ambiguity check
  (`ambiguous call to dir_create ... neither defines nor imports it`), so caret
  still runs in the interpreter. It works, just slower.

## 10. Troubleshooting

| Symptom | Cause | Fix |
|---|---|---|
| `GET /v1/models` never answers; connection stuck in CLOSE-WAIT | seed older than 2026-11-09 | rebuild the seed (section 6) |
| "could not establish available memory (no MemAvailable in /proc/meminfo ...)" | seed without PR #8492 | rebuild the seed from a tree containing it |
| `Error: --n-ctx must be a positive integer` | bad `--n-ctx` value | pass a positive integer |
| Agent overflows context on first file read | default `--n-ctx` 4096 | start the server with `--n-ctx=32768` |
| `cudaSetDevice` "out of memory" in `ggml_cuda_init` | server under a cgroup `MemoryMax`, or a second CUDA process | remove the cgroup wrapper; run one CUDA process (section 9) |
| nvcc "unsupported clang version" building llama.cpp | clang >= 21 as host compiler | use clang-18 (section 2) |
| `spl_dlsym: unresolved symbol` | shim built from older source | rebuild the shim in this worktree |
| 503 `model_not_runnable` | non-GGUF or unsupported model | use a GGUF; read the reason in the response |
| Agent argument ignored or misparsed after `/launch` | args are space-split | no spaces inside one argument |

Design context: `doc/00_llm_process/feature_expert/slang_local_inference/skill.md`.
