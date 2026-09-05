# cuda-gdb MI semihosting-lane spike (B6)

**Date:** 2026-08-07
**Status:** Spike complete — research only, no production code
**Plan:** `doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md` §3 (B6)
**Related:** `doc/05_design/runtime/gpu_remote_interpreter_architecture.md` (GMB-1 mailbox, §3.1),
B2 (`cuda_jit` lane), B3 (`cuda_vm` / SVM-G lane)

## Verdict

**NO-GO** for a `cuda-gdb`-backed lane in the routed GPU-lane matrix (A3/B2/B3). **GO** as
an opt-in, developer-invoked debugging tool for SVM-G (D1/D2/B3) bring-up — outside the CI
lane matrix, not a `GpuLaneExecutor`.

## Environment actually used

- Host has 2 real GPUs: `NVIDIA RTX A6000` and `NVIDIA TITAN RTX` (`nvidia-smi -L`).
- `cuda-gdb` 13.0 present at `/usr/local/cuda-13.0/bin/cuda-gdb` (GNU gdb 14.2 base).
- `nvcc` 13.0.88 present, used to build a device-debug (`-g -G`) test binary.
- No `expect`/pty helper installed; drove the MI session with a small Python subprocess
  script over `--interpreter=mi2` stdin/stdout (scratch-only, not committed to the repo).

## What was actually run

Trivial vector-add kernel (`__global__ void vecadd(int*,int*,int*,int)`), compiled with
`nvcc -g -G`, launched under:

```
cuda-gdb --interpreter=mi2 --args ./vecadd
```

MI command sequence sent over stdin, transcript captured from stdout (full log kept in the
spike's scratch dir; representative excerpts below are the real captured output, not a
paraphrase):

```
--- SEND: -break-insert vecadd ---
^done,bkpt={number="1",...,func="vecadd(int*, int*, int*, int)",
  file="vecadd.cu",line="3",thread-groups=["i1"]}

--- SEND: -exec-run ---
^running
*running,thread-id="all"
... (host-side library-loaded / thread-created noise, incl. libcudadebugger.so.1) ...
~"CUDA thread hit Breakpoint 1.2, vecadd<<<(1,1,1),(32,1,1)>>> (a=0x7fffd1a00000,
  b=0x7fffd1a00200, c=0x7fffd1a00400, n=32) at vecadd.cu:4\n"
*stopped,CudaFocus={device="0",sm="0",warp="0",lane="0",kernel="0",grid="1",
  blockIdx="(0,0,0)",threadIdx="(0,0,0)"},reason="breakpoint-hit",bkptno="1",locno="2",
  frame={addr="0x00007fffd727d1f0",func="vecadd",
  args=[{name="a",value="0x7fffd1a00000"},{name="b",value="0x7fffd1a00200"},
        {name="c",value="0x7fffd1a00400"},{name="n",value="32"}],
  file="vecadd.cu",line="4",arch="m68k"},thread-id="1",stopped-threads="all",core="11"

--- SEND: -data-evaluate-expression threadIdx.x ---
^done,value="0"

--- SEND: -data-evaluate-expression blockIdx.x ---
^done,value="0"

--- SEND: -exec-continue ---
^running
*running,thread-id="all"
0 3 6 9 12 15 18 21 24 27 30 33 36 39 42 45 48 51 54 57 60 63 66 69 72 75 78 81 84 87 90 93
~"[Inferior 1 (process 4018019) exited normally]\n"
*stopped,reason="exited-normally"

--- SEND: -gdb-exit ---
^exit
```

Program output `0 3 6 ... 93` is `a[i]+b[i] = i + 2i = 3i` for `i=0..31` — correct. The
device-side breakpoint hit on real hardware (device 0, warp 0, lane 0), args and
`threadIdx.x`/`blockIdx.x` were read via `-data-evaluate-expression`, and the process
continued to normal exit and clean `-gdb-exit`. Total wall time for the whole scripted
session (insert breakpoint → run → hit → 4 evaluations → continue → exit) was ~14 s.

## Assessment against the GPU-lane use case

**What worked well:**
- MI mode is fully non-interactive and scriptable over plain stdin/stdout — no pty/expect
  needed, just a subprocess with an idle-timeout read loop (MI has no strict
  request/response token pairing; async `*running`/`*stopped`/`=library-loaded` records
  interleave with `^done` replies, so a scripted driver must frame on protocol records, not
  assume one line per command).
- `CudaFocus={device,sm,warp,lane,kernel,grid,blockIdx,threadIdx}` on every stop is a
  genuinely useful structured GPU-state record — richer than anything the GMB-1 mailbox
  layout carries today.
- Breakpoints on `__global__` kernel functions resolve correctly and report the CUDA launch
  config (`vecadd<<<(1,1,1),(32,1,1)>>>`) directly in the stop message.

**Why it doesn't fit as a lane backend (B2/B3):**
1. **Heavyweight, exclusive, stateful attach.** `cuda-gdb` must own the process (launch via
   `--args` or `attach <pid>`) and injects `libcudadebugger.so.1` into the CUDA driver debug
   API. This is a single-consumer, exclusive-per-device debug session — fundamentally
   different from GMB-1's model of a passive/interactive shared-memory mailbox that many
   short-lived lane launches can use back-to-back without a persistent controlling debugger
   process. It was not tested here, but is documented/expected that only one active
   CUDA-GDB debug session can occupy a given device at a time; this alone conflicts with the
   plan's parallel-lane execution model.
2. **Startup cost.** A few seconds of the ~14 s round trip is fixed attach/library-load
   overhead (host shared-library loads, `libcudadebugger.so.1`, PTX JIT), independent of the
   actual kernel work. B2/B3 lane executors are designed for cheap, frequent per-test
   launches (hello-kernel specs, ≥40 D3 conformance vectors) — paying multi-second debugger
   attach overhead per launch is not compatible with that budget.
3. **Wrong abstraction for the mailbox contract.** GMB-1 (§3.1 of the design doc) is a
   byte-buffer protocol (`TRIGGER_MAGIC`, `SENTINEL_TIMEOUT`, `PUTC`/`EXIT`/`RESULT`) meant
   to be polled or serviced from the host without controlling the device process via a
   debugger. `cuda-gdb` MI is a control-plane / introspection channel, not a data-plane
   transport; it composes poorly with the resident-mode command ring in B4, which expects
   the host to be a lightweight doorbell servicer, not a process supervisor holding a ptrace
   attach.
4. **No non-GPU skip path.** The GPU-lane routing (A3) requires clean `skip:`/`blocked:`
   reporting on hosts without a GPU/driver. A `cuda-gdb`-based lane would need its own
   parallel probing and failure-mode taxonomy (attach failure vs. no device vs. no
   `libcudadebugger`), duplicating A3's existing probing machinery for no benefit over the
   already-landed direct-launch approach.

**Where it does fit:**
- As a **manual/opt-in debugging aid** for SVM-G interpreter development (D1 assembler, D2
  host-ref VM, and especially B3's on-device SVM-G interpreter kernel): when a D3
  conformance vector fails only on-device (CUDA-specific divergence per the plan's risk
  table), a developer can point `cuda-gdb --interpreter=mi2` (or interactively) at the SVM-G
  interpreter kernel, breakpoint the fetch/dispatch loop, and inspect PC/opcode/register
  state directly — exactly the kind of use this spike exercised. This is a **local
  troubleshooting tool**, not a CI-routed lane, and should not gain a grammar token
  (`cudagdb` in A1) beyond what's already parse-only/reserved.

## If someone wants to build this anyway (task list, NOT implemented here)

Only pursue if a concrete recurring need for on-device SVM-G debugging shows up during B3:

1. `scripts/dev/cudagdb_svmg_attach.shs` (or `.spl` if wrapped, per repo's shell-script
   exception) — thin wrapper that launches the checked-in SVM-G PTX artifact under
   `cuda-gdb --interpreter=mi2 --args <harness> <sgp-blob-path>`, sets a breakpoint on the
   interpreter's dispatch function, and dumps `CudaFocus` + a handful of named locals
   (PC/opcode/stack-top) on each stop — a developer-facing script, not a lane executor.
2. Document the one-session-per-device exclusivity constraint (verify it empirically before
   relying on it — untested here) so it's never accidentally invoked from parallel CI.
3. No changes to `GpuLaneExecutor`, A3 routing, or GMB-1 (`gpu_mailbox.spl`) — this stays
   entirely outside the routed lane matrix (`doc/08_tracking/lane_matrix.md`, E2).
4. If future work wants scripted assertions instead of ad hoc use, wrap the MI
   request/response framing (idle-timeout based read loop over async + reply records, as
   used in this spike) in a small internal test helper — but scope it to interpreter
   bring-up debugging, not to the production lane path.
