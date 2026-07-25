# Embedded Coroutine / State-Machine Patterns for NVMe FW (wave-4 research)

Status: research input for wave-4, informing the four-core rv32 dataplane in
`doc/05_design/hardware/nvme_fw_multicore/fourcore_ipc_index_handle_design.md`
(the "four-core doc"). Grounded against the current wave-3 implementation:
`examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_fourcore_core.spl` (pure
routing fns) + `ipc_fourcore_check.spl` (host round-robin harness, step
functions `hil_step`/`ftl_step`/`fil_step`/`nand_step`), and
`.claude/rules/language.md` (no inheritance, `gen` reserved, nogc tiers).

## 1. Landscape (compressed — general knowledge, not repo-specific)

| Pattern | Core mechanism | State storage | Embedded cost/risk |
|---|---|---|---|
| **Protothreads** (Dunkels 2006) | Duff's-device `switch` on a saved line number (`LC_SET`/`LC_RESUME`), one `struct pt` per thread | Single `lc_int` scalar in the pt struct | Zero stack overhead, but **locals do not survive a yield** (they live on the C stack, which is discarded/reused across the switch re-entry) — only fields explicitly hoisted into a state struct persist. No nested blocking calls. |
| **Stackful coroutines** (ucontext, fibers, per-task-stack RTOS tasks) | Real context switch (saved SP + register file), each coroutine gets its own stack | Entire call stack + registers | Full expressiveness (any C/locals/recursion), but each task burns a dedicated stack (this repo's `fw_rv32` reserves 4×16 KB total for 4 harts — a 5th "coroutine" stack per hart is not in that budget); stack-overflow risk is silent unless guard pages exist (rv32 freestanding has none here). |
| **C++20 coroutines** | Compiler-generated resumable-function frame + promise type | Heap- (or HALO-elided) allocated coroutine frame | The "frame allocation problem": frames are heap-allocated by default, which is disqualifying under a no-heap freestanding boot graph; HALO (Heap Allocation eLision Optimization) can stack-allocate a frame when the compiler proves the coroutine doesn't escape, but that proof is optimizer-dependent, not a language guarantee — unsuitable to rely on for a *rule*, only as a possible win under a specific toolchain. |
| **Rust async / Embassy** | `async fn` desugars to a compiler-generated enum state machine (one variant per await point) + a `Waker` for resumption signaling | The generated enum, stack-sized at compile time (no heap) | This is the closest *conceptual* match to what we want: a compile-time state machine with zero runtime allocation. Embassy specifically targets bare-metal Cortex-M with no RTOS. We have no such codegen in Simple; the analogous move here is to hand-write the enum-of-states ourselves (see §5). |
| **Run-to-completion (RTC) event loops** | A dispatcher calls each handler once per event/tick; handler returns immediately, no blocking | Whatever state the handler explicitly persists between calls (globals/struct fields) | This is what wave-3 already does: `hil_step`/`ftl_step`/`fil_step`/`nand_step` are each "move at most one message, then return." RTC is the correct embedded default — it composes with a step budget and never blocks a hart. |
| **Classic explicit FSM** (state int + `switch`/`if`-chain) | A named state constant + a dispatch on it | One scalar (or small struct) per FSM instance | Cheapest, most auditable pattern; the entire "coroutine" literature above is various automations of hand-writing this. Wave-3's step fns are *implicitly* this pattern already, just without a persisted state word (see §3). |
| **Hierarchical statecharts** (Harel; QP/QM nanoframeworks) | Nested states, entry/exit actions, guarded transitions, generated dispatch tables | A current-state pointer/id + a state hierarchy table | Powerful for UI/protocol stacks with many cross-cutting events; overkill for a 4-stage linear dataplane pipeline with no hierarchy — the four-core doc's cores don't have nested sub-states, they have one active "waiting on ring X" position each. |
| **Table-driven FSM** ((state, event) → (action, next_state) matrix) | An explicit transition table, usually `const` data | State id + the table | Best verifiability of all patterns (the table IS the spec, and "is this transition legal" becomes a single lookup) but needs an array/table in memory; on scalar-only rv32 boot graph this becomes a chain of `if` comparisons instead of a real table — same semantics, no array. |

## 2. The "statement-like" property

A coroutine reads "statement-like" — i.e., linearly, like ordinary sequential
code with `await`/`yield` marking suspension points — when the *reader* can
trace top-to-bottom and mentally reconstruct control flow without chasing a
separate transition table. Rust's `async fn` and C++20 coroutines achieve this
syntactically (the state machine is compiler-generated from linear source);
protothreads achieve it with a macro trick (`PT_BEGIN`/`PT_WAIT_UNTIL`) over a
plain function re-entered via `switch`. What differs across patterns is
**where the resume point is stored** and **what else survives resumption**:

- **Protothreads**: resume point = one integer (`lc.line`) in the pt struct.
  Everything else — local variables — does **not** survive, because the
  function's C-stack frame is discarded and rebuilt from scratch on
  re-entry; the `switch` only restores program-counter position, not values.
  This is the single most common protothreads bug class: a local declared
  before a `PT_WAIT_*` silently resets to garbage/undefined after resume. The
  fix pattern (used by every serious protothreads deployment) is to hoist
  every value that must survive a yield into the per-instance struct (exactly
  what `src/lib/nogc_async_mut/coroutine.spl`'s "saved local variables
  (slots)" does — see §5).
- **Stackful coroutines**: resume point + every local = the entire saved
  stack/register file. Nothing to hoist manually, but nothing is
  inspectable without a stack unwind either — a debugger has to walk frames
  to answer "where is this coroutine paused," rather than reading one word.
- **Explicit FSM / table-driven FSM**: resume point = the state constant,
  by construction *is* the one thing hoisted (there are no "locals across a
  yield" because there is no implicit yield — the function returns and is
  re-called, and any survives-the-call value is, by construction, a named
  field, never an anonymous stack slot).

**Debuggability consequence**: explicit-state patterns (protothreads-with-
hoisted-struct, hand-rolled FSM) are strictly the most post-mortem-friendly
for this repo's toolchain, because a paused system's *entire* resume state is
one readable scalar per instance, visible in a raw memory/shm dump with no
stack-walking, no symbol table, no debugger attached — exactly the situation
of a crashed/hung QEMU rv32 core inspected via a memdump or serial trace.
Stackful and heap-framed coroutines fail this test in a freestanding rv32
environment with no unwinder.

## 3. Easy-to-check / verify dimension

Wave-3 already established several of these mechanisms independently; they
generalize directly to a coroutine-state discipline:

- **Name every state.** A bare integer state is only as auditable as its
  naming; require a `fn`-per-constant just like the existing opcode/status
  constants (`OP_WRITE()`, `ST_BOUNDS()` in `logic_ipc_msg_core.spl`) rather
  than inline literals — greppable, single point of truth, and
  `const_drift_check.spl`-style drift guards apply unchanged.
- **Log state transitions, level-gated.** Per `.claude/rules/code-style.md`
  ("Logs are NOT unused code... convert them to level-gated logs, default
  off"), a transition helper should carry an optional trace print gated by a
  build-time/runtime level, never removed once added.
- **Assert a legal-transition table in checks.** Even without a runtime array
  on rv32, the *host* check (which already runs with `[i64]` arrays — see
  `ipc_fourcore_check.spl`'s header: "Arrays are legal here: this file is
  host-only") can hold a real (from_state, to_state) legality matrix and
  assert every observed transition against it — a pure verification-only use
  of arrays, matching the existing host/rv32 accessor split (§8 of the
  four-core doc: same state machines, only the shm accessor differs).
- **Deterministic replay of step sequences.** Because every step fn here is
  RTC (return after ≤1 message movement) and reads all its "am I ready"
  state from the same shm, a captured (state, shm-snapshot) sequence replays
  bit-identically — no timers, no wall-clock, no thread interleaving
  nondeterminism to fight, which is the actual precondition needed for
  regression-testing a concurrency protocol on this scale.
- **Invariant checks per state.** E.g. "if `coro_state == WAIT_FTL2HIL`, then
  a tag must be outstanding in HIL's own bookkeeping" — cheap post-step
  assertions the same way `ipc_fourcore_selftest` already asserts buf-pool
  free-list integrity (stage 4) and halt convergence (stage 5).
- **Run-to-completion + bounded steps keep FSMs testable.** The existing
  `drain_until_ftl2hil_ready`/`drain_until_all_empty` 100000-step budget and
  the rv32 `SPIN_MAX` wait-loop budget (four-core doc §6: "exhaustion prints
  a FAIL marker and parks — fail-closed, no silent hangs") are precisely the
  "bounded steps" testability property coroutine literature calls out as
  the main reason RTC step machines beat blocking/threaded designs for
  verification: a hung protocol degrades to a *loud, bounded* failure
  instead of an infinite wait.
- **Absolute-oracle convention.** The four-core doc's own verification
  matrix line (§10: "every `*_check.spl`... with absolute oracles + at least
  one deliberate-red calibration") is the repo's existing standard this
  research must not deviate from — any new coroutine-state check must print
  a single unambiguous PASS/FAIL marker and exercise a known-bad transition
  once during development.

## 4. Constraint mapping to this repo

Constraints (from the four-core doc + `.claude/rules/language.md`): (C1)
scalar-only rv32 boot graph — no arrays/heap/closures/classes in the
`entry.spl`→`logic_*` import graph; (C2) existing pure-verdict-fn + thin-
driver split (`logic_*_core.spl` pure, `*_check.spl`/`entry_smp.spl` drivers
do the shm I/O); (C3) shm word map is fixed and drift-guarded, only specific
words are free; (C4) host harness must mirror the rv32 state machine exactly
(§8: "SAME state machines run host-side... only the shm accessor differs");
(C5) no inheritance, `gen` is reserved (cannot name a helper `gen_*` as a
keyword collision risk — descriptive names only).

| Pattern | C1 scalar-only | C2 pure+driver | C3 shm map | C4 host mirror | C5 no-inherit/no-gen | Fit |
|---|---|---|---|---|---|---|
| Protothreads (raw, no hoisted struct) | Fails — Duff's-device macro needs a `switch` over a saved line, and its usual C form is fine, but its core promise (locals persist implicitly) is false and would hide C1-adjacent bugs | Fails — the macro conflates state storage and control flow, can't be split into pure fn + driver | Needs 1 word/instance | possible but macro form doesn't port to Simple (no `switch`-line trick in this language) | untested vs C5 | **No** — wrong idiom for this language; hoisted-struct variant is just an explicit FSM (see below) |
| Stackful coroutines | Fails — needs a second stack per hart, outside the sized 4×16K budget | N/A | N/A | N/A | N/A | **No** — stack budget + no guard pages makes this a silent-corruption risk |
| C++20 coroutines / frame allocation | Fails — not applicable, this is a Simple codebase, and the heap-frame default fails C1 outright even conceptually | N/A | N/A | N/A | N/A | **No** — pattern doesn't exist in this toolchain; noted for completeness only |
| Rust async/Embassy (conceptual model only) | Matches the *goal* (compile-time enum state machine, zero alloc) but Simple has no such codegen | N/A | N/A | N/A | N/A | **Inspirational only** — hand-write the enum-of-states manually (§5) |
| Run-to-completion event loop | **Pass** — already the shape of `hil_step`/`ftl_step`/`fil_step`/`nand_step` | **Pass** — already split (verdict fns in `logic_fourcore_core.spl`, shm I/O in the step fns) | **Pass** — no new storage needed for RTC itself | **Pass** — already proven identical host/rv32 by design | **Pass** | **Already adopted** |
| Explicit FSM (state constant + `if`-chain, hoisted fields) | **Pass** — one scalar per core, no arrays/heap | **Pass** — `coro_next_state(...)` as a pure fn, driver just loads/stores the word | **Needs 4 free words** (§below) | **Pass** — same pure fn, host and rv32 both load/store via their own accessor | **Pass** (name it `coro_state`, not `gen_state`) | **Best fit — recommended** |
| Hierarchical statecharts | Fails C1 in spirit (needs a state-hierarchy table/array to be worth the complexity) and is unneeded — no nested sub-states exist in a 4-stage linear pipeline | Could split but the split buys nothing extra over flat FSM here | N/A | N/A | N/A | **No — overkill** |
| Table-driven FSM | Table itself fails C1 (no array on rv32); host-side legality-matrix use is fine (§3) | Pass for the host verification use | N/A | Host-only, not symmetric with rv32 | Pass | **Host-only tool, not a firmware pattern** |

**Word-map arithmetic (verified against four-core doc §3):** buf pool spans
words 220–253 (34 words) and NAND state starts at word 256 — **only words
254–255 are currently free (2 words)**. A per-core `coro_state` word for
all four cores (HIL/FTL/FIL/NAND) needs **4** words — a 2-word shortfall.
Word 3 ("reserved") is already claimed as `IPC_HALT_IDX`
(`logic_fourcore_core.spl:76-78`, `ipc_reserved_idx()`) and must not be
reused. Resolution (DECIDED at design review, supersedes the draft's
mid-map insertion): **append** the 4-word `COROSTATE` region at the END of
the map — words **8448–8451** (`COROSTATE[core]` = 8448+core, core 0..3),
`IPC_SHM_WORDS` 8448 → **8452**. Appending is strictly additive: no landed
base moves, every existing oracle (`nand_state_idx(0)==256`,
`nand_data_idx(4095)==8447`, all `ipc_drift_check.spl` literals) stays
valid, and only `logic_ipc_layout_core.spl` (+drift-check additions and the
asm stub's `.space` byte count, 33792 → 33808) changes. Mid-map insertion
would have re-based ~8192 NAND words and invalidated the landed drift
oracles for zero functional gain.

## 5. Recommendation (wave-4)

**Adopt: explicit-state stackless-coroutine discipline** — i.e., formalize
what the RTC step functions are already halfway doing, by giving each core a
**named, persisted resume-state word** instead of re-deriving "where am I"
implicitly from ring emptiness each call.

**Current state (wave-3, as read):** `hil_step`/`ftl_step`/`fil_step`/
`nand_step` are *stateless* RTC handlers — each call re-derives its position
purely from ring occupancy (e.g. `ftl_step`'s up-pump-before-down-pump
priority is a live `if`/`if` order in the function body, not a recorded
fact anywhere). This works and is correct today, but nothing external can
answer "what is core N about to do" without re-running the same occupancy
checks — there is no single word to read in a memory dump.

**Proposed change:**
1. Add `COROSTATE[0..3]` to the shm layout per §4 (words 254–257).
2. Define named resume-state constants per core in each core's
   `logic_*_core.spl` (e.g. `FTL_ST_IDLE()`, `FTL_ST_UPPUMP()`,
   `FTL_ST_DOWNPUMP()` — mirroring the existing `OP_*()`/`ST_*()` constant-fn
   convention), each returning a distinct small int; a fail-closed default
   (`FTL_ST_UNKNOWN() = -1`) covers uninitialized/corrupt reads the same way
   `ftl_route_opcode`/`fil_route_opcode` already fail-closed to `-1`.
3. Add one pure transition-verdict fn per core, e.g.
   `ftl_next_state(cur_state, up_ready, down_ready) -> i64`, colocated with
   the existing pure routing fns in `logic_fourcore_core.spl` — no shm
   access, matching C2.
4. Add a `coro_transition(shm, core, from, to) -> [i64]` driver helper
   (host) / equivalent shm-store call (rv32) that (a) asserts `to` is a
   legal successor of `from` per a small `if`-chain legality check (§3 —
   this is the "assert legal-transition table" requirement, expressed
   without an array to satisfy C1), (b) stores the new state word, (c) emits
   a level-gated trace line (`code-style.md` convention — default off).
5. Keep the actual message-moving logic unchanged; `coro_state` becomes an
   *observability and assertion* layer over the existing correct behavior,
   not a rewrite of it — lowest-risk path to landing this in wave-4.
6. Host harness (`ipc_fourcore_check.spl`) gets a **new stage**: after
   stage 5 (halt+drain), assert every `COROSTATE[core]` word equals its
   respective idle/done state — a direct, cheap use of the persisted state
   for post-mortem-style verification, proving the debug-visibility win is
   real inside the existing absolute-oracle harness rather than aspirational.

**Simple-language support note (host side only, verified against repo
source, not invented):** `src/lib/nogc_async_mut/coroutine.spl` already
documents exactly this discipline in its header — "Manual enum-based state
tracking. Each coroutine holds: a state tag..., saved local variables
(slots)..., a step function that dispatches on the current state" — with a
`CoroutineResult.Yielded`/`Completed` protocol, and
`src/lib/nogc_async_mut/generator.spl` layers a lazy iterator (`step_fn:
state -> (next_state, should_continue)`) on top of it, explicitly noting
"Users write explicit state machines; generators are lazy by default." Both
are **`nogc_async_mut` tier** (host/async), not `nogc_async_mut_noalloc`
(baremetal) — they use classes/enums/closures, which fail C1, so they are
**not usable inside `fw_rv32`'s scalar boot graph**; their relevance is
strictly to the host-side test harness and any future host-tooling that
walks a firmware trace. Lang-survey verdict (2026-07-19, source-verified):
the `gen`/`yield` keyword surface is REAL syntax but NOT a usable coroutine
anywhere relevant — the interpreter runs generator bodies EAGERLY and
collects all yields into a Vec before returning
(`interpreter_call/core/function_exec.rs:266-288`); native Cranelift/JIT
lowering exists but heap-allocates via `rt_generator_*` externs; the LLVM
backend **silently no-ops `Yield`** (`codegen/llvm/functions.rs:1475` — a
silent-wrong-code hazard, bug to be filed in wave-4); and native-build
forces `FallbackReason::Generator` interpreter fallback
(`compilability.rs:330,823`), which on freestanding targets is a hard
failure. `async fn` parses but the keyword is skipped (sugar for `fn`), and
`rt_future_await` needs a thread-pool executor. The manual
`std`-tier `coroutine.spl` pattern IS usable host-side today (it is the
documented idiom); named-enum returns are safe (the interpreter landmine is
ANONYMOUS tuples specifically, per the agent guide). Conclusion: build the
wave-4 discipline on explicit state everywhere; do not touch `gen`/`yield`. Separately, the suspension operator `~`
(`doc/06_spec/03_system/feature/language/suspension_operator_spec.md`) is
explicitly modeled with "ordinary control flow" in its own spec because the
real `~` syntax is noted there as unsupported — it is **not** a currently
usable coroutine primitive and should not be cited as one.

**Non-goals for wave-4:** no hierarchical statecharts (no nested sub-states
exist to justify one), no stackful/second-stack coroutines (budget risk),
no attempt to port `std.coroutine`/`std.generator` into the rv32 firmware
path (violates C1 outright).
