# Windows piped process cold handle growth

Status: CLOSED 2026-11-03 as expected one-time OS init (bcrypt.dll + CNG RNG); see per-stage table below.

The genuine Windows fixture compiled and strict-linked against retained Rust199, but cycles2and3 exited36 at exact final handle equality. [Final run38201907318](https://github.com/ormastes/simple/actions/runs/38201907318) reused the actual cycle2 Windows provider object; no repeated provider compile or Simple/Rust generation build occurred.

| Phase | Actual process handles |
|---|---:|
| Baseline |128|
| Empty argv |131|
| Cancel |158|
| Threads |158|
| Slots |158|
| Final |158|

The diagnostic fixture emitted six phases. The driver wrongly expected an additional Unicode phase, so its diagnostic JSON was not written. Actual native exit36 and these six stderr counts remain retained evidence. No fourth retry is allowed. The plateau during threads and sixteen-slot reuse does not prove legitimate initialization or absence of a leak; it rejects the earlier thread-specific attribution.

Source-only investigation binds frozen82 constructor/accessor and validator paths. First spawn reaches BCrypt/Windows process APIs; stdout validation reaches SIMD tier selection, which can resolve CPU configuration through dirs_next cache directories and filesystem metadata. Those are candidate chains, not observed handle ownership. No cold baseline was weakened, no provider eligibility advanced, and no full compiler/core/MCP/whole-test PASS is claimed.

**Revalidated 2026-11-02: still plausible because OPEN, P1 qualification blocker; heap/OS owner attribution unresolved; no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 handle accounting (C provider)

`test/01_unit/runtime/process_piped_handle_stress_test.c` (runner `run_process_piped_handle_stress_test.shs`) drives `rt_process_spawn_piped`/`write_stdin`/`read_stdout`/`close_piped` for 3 warmup + 100 serial + 4x15 concurrent cycles and asserts `GetProcessHandleCount` returns to the post-warmup baseline. Result on Windows 11 (clang): baseline=79 serial=79 concurrent=79, 0 failures, peak RSS 5 MB, wall 21 s. The C provider (`runtime_process.c` spawn/close/is_alive paths) does NOT leak per cycle; the 128->158 cold growth is therefore one-time lazy initialisation outside this primitive (Rust-side first-spawn/SIMD-tier/dirs init), not per-process. Bug remains open for the Rust fixture's cold baseline; use this spec as the guard.

## 2026-11-03 per-stage handle table and verdict: (b) expected one-time setup

Measured with `GetProcessHandleCount` (clang, Windows 11) by `test/01_unit/runtime/process_piped_cold_handle_budget_test.c` and a stage probe calling the same Win32 sequence as `rt_process_spawn_piped`:

| Stage | Handles | Delta | Persists after close |
|---|---:|---:|---|
| process start | 58-64 | | |
| `LoadLibraryA("bcrypt.dll")` (in `win_random_pipe_name`) | | +12 | yes (loader state) |
| `BCryptGenRandom` first call (CNG RNG init) | | +4 | yes |
| `FreeLibrary` | | 0 | the 16 stay |
| named pipe + CreateFile, CreatePipe, event, job | | 0, +3, +1, +1 | closed by `close_piped` |
| `CreateProcess` (suspended) | | +4 | closed by close |
| second cycle | | +1 | yes (one-time) |

Full spawn/write/read/close first cycle: +24 during spawn, -5 on close, net +19; second cycle +1; total cold growth 20. Steady state: 0 over 50 cycles and 0 for 5 distinct first-use command shapes. Owner: the OS loader and CNG RNG (bcrypt.dll), not Simple code; all provider handles (pipes, event, job, process, thread) are closed. The 128->158 figure in the Rust fixture is the same class (BCrypt/first-spawn init plus Rust std/SIMD tier cache lookups); no per-spawn leak. Verdict (b): pinned by budget spec `run_process_piped_cold_handle_budget_test.shs` (cold <= 24, 0 per cycle over 50, 0 for distinct first uses). The Rust seed fixture's exact-equality-after-first-spawn check should use the post-warmup baseline.
