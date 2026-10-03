# Local LLM setup: slang backend + caret (and driving spipe from it)

How to run a local GGUF model through slang's ggml backend and use it from
caret — including letting the local model run the spipe (SSpec) development
flow. Verified 2026-09-16 on a GB10 host (128G unified memory) with
`Qwen3-Coder-Next-Q4_K_M` (4-shard, 46G) and `Qwen3.5-9B-Q3_K_M` (4.7G).

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
changes are authored, and a local model must not push).

Design context: `doc/00_llm_process/feature_expert/slang_local_inference/skill.md`.
