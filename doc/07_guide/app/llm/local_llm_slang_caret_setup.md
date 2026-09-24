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
