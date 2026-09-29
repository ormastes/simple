# slang_local was unrunnable off the DGX: Linux-only memory probe, DGX-scale budget constants, and a Metal teardown abort after a correct answer
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Filed** 2026-09-05 · lane `slang-on-mac`, goal `caret_workbench` AC-6
**Host** macOS 26 / Apple silicon (arm64)
**Status** FIXED for the first three; one residual shortcut recorded below.

## Summary

`caret --provider slang_local` could not reach a single generated token on this
mac. Four separate defects sat in series; each one had to be cleared before the
next became visible, and every one of them looked like "the environment is
wrong" rather than "the code is Linux-only".

## 1. Availability probe read `/proc/meminfo` only

`memory_budget.spl:mem_available_bytes` parsed `MemAvailable:` out of
`/proc/meminfo` and returned `-1` otherwise. macOS has no `/proc`, so `-1` was
the only possible answer, and `check_fit` correctly turned that into a refusal:

```
ERROR: refusing to load 'qwen2.5-0.5b-instruct-q8': could not read MemAvailable
from /proc/meminfo; refusing rather than loading blind
```

A fit gate that refuses everything is not a gate, it is an outage. Fixed by
adding a Darwin lane (`sysctl -n hw.memsize` / `hw.pagesize` plus one `vm_stat`
pass) that derives availability as total minus resident (active + wired +
compressed). That is conservative by construction — inactive and purgeable pages
are reclaimable and are still counted as unavailable — which errs toward
refusing a load that would have fitted, the safe direction here. `-1` is still
returned when neither lane can answer, and still refuses.

## 2. Runtime-overhead estimate was a flat 6 GiB

`llm_engine.spl:_runtime_overhead_bytes` returned a flat 6 GiB for the KV cache
and activations. On the 128 GB unified host the module was written for that is
noise. For a 0.64 GiB 0.5B model it is an over-estimate of roughly ten times,
and it alone pushed the load over budget. Fixed by scaling with the weights (the
only proxy for the model's dimensions available before the file is opened), with
a 1 GiB floor and the previous 6 GiB kept as a **ceiling** — so no large model is
admitted on a laxer budget than before.

## 3. OS headroom was a flat 8 GiB

`memory_budget.spl:default_headroom_bytes` returned a flat 8 GiB. That is 6.25%
of the 128 GB host it was calibrated on and more than half an ordinary laptop:
the reserve alone exceeded free memory, so nothing of any size could ever be
admitted. Fixed by making it that same 6.25% of physical memory (`total / 16`),
which returns approximately the DGX's old reserve and scales down sanely. Not
exactly: Linux `MemTotal` excludes the kernel's own reserve, so a 128 GB box
lands nearer 7.5 GiB than 8 — marginally **laxer** than before on the one host
where over-admission takes the machine down. That is small at this magnitude but
unverifiable from this mac, and the DGX owner should confirm it. With a 1 GiB
floor and the old flat value retained as the fallback when
total memory cannot be read at all. `mem_total_bytes` was added and exported.

## 4. Metal teardown aborted (exit 134) AFTER a correct answer

With the budget cleared the model loaded and generated correct text — and then
the process died:

```
 A compiler is a program that translates source code into machine code, ...
ggml-metal-device.m:1021: GGML_ASSERT([rsets->data count] == 0) failed
... ggml_metal_device_free ... __cxa_finalize_ranges ... exit
```

This is the worst shape of failure: correct output and a non-zero status. Cause
is on our side, not upstream's — `slang_release()` exists and was never called,
so the model stayed resident until process exit and ggml's static device
destructor ran while its resource sets were still populated. Fixed by releasing
in `provider.spl:_dispatch_slang_local` after the answer is captured. Teardown
is now clean (`ggml_metal_free: deallocating`) and the run exits 0.

**Residual shortcut (marked `# ponytail:` at the call site).** Releasing after
every dispatch drops `engine_ensure_loaded`'s residency cache, so an interactive
multi-turn caret session will reload the model once per turn. **Upgrade path:**
release from caret's shutdown path in `main.spl` instead, so one-shot runs tear
down and TUI sessions keep the model resident across turns. Not done here
because the one-shot path is what AC-6 needed and the shutdown path is a larger
edit in a file three peer lanes are concurrently editing.

## Script portability, fixed in the same pass

- `scripts/check/build-slang-ggml-shim.shs` defaulted `LLAMA_ROOT` to
  `/home/yoon/dev/llama.cpp` and hard-required `build/bin/libllama.so`. It now
  accepts `.so` **or** `.dylib`, and an unset `LLAMA_ROOT` is an explicit ERROR
  rather than a silent host-specific default. Two latent bugs were fixed with
  it: `cc_rc=$?` was unreachable under `set -e` (a failed compile aborted before
  the promised FAIL verdict line could print), and the non-vacuity check used
  GNU-only `nm -D --defined-only` with a `' T slang_ggml_'` pattern that cannot
  match Mach-O's underscore-prefixed symbols — it would have FAILed a good macOS
  build. Now `nm -g` with an optional leading underscore.
- `scripts/check/check-slang-ggml-inference.shs` used GNU-only `find -printf`
  with stderr discarded, so on BSD find the model listing came back empty and
  the gate ERRORed "no directories" on a root holding a good model. Replaced
  with portable `-print | sed 's|.*/||'`.
- The shim OUTPUT deliberately keeps the `.so` name on every platform:
  `llm_engine.spl:26` hardcodes `build/sffi/libslang_ggml.so` and dlopen on
  macOS does not care about the suffix.

## Evidence

llama.cpp `6a1a922` ("metal : fix memory leak in early return (#28399)"), built
with `-DBUILD_SHARED_LIBS=ON`. `slang_ggml_shim.c` compiled against that
`llama.h` with **no API drift** — `PASS -- 17 symbol(s) exported`.

Model: `Qwen/Qwen2.5-0.5B-Instruct-GGUF`, `qwen2.5-0.5b-instruct-q8_0.gguf`,
675,710,816 bytes, at `models/qwen2.5-0.5b-instruct-q8/`.

```
SIMPLE_BINARY=src/compiler_rust/target/bootstrap/simple \
SLANG_MODEL_ROOT=$PWD/models SLANG_GGML_LIB=$PWD/build/sffi/libslang_ggml.so \
sh scripts/check/check-slang-ggml-inference.shs

MODEL qwen2.5-0.5b-instruct-q8 -> GENERATED:  A compiler is a program that
translates source code into machine code, allowing programmers to write code
that can be executed on a computer.
PASS -- 1 model(s) reached a verdict, 1 generated, 0 refused with a reason, 0
silent (binary: .../src/compiler_rust/target/bootstrap/simple)
```

exit 0. `SIMPLE_BINARY` is required on this host: both the gate and `bin/caret`
prefer `bin/simple`, which is bootstrap-only and has no `run` subcommand while
still answering `--version`. That selector is a separate latent trap, not fixed
here.

