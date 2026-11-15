# Unified memory model plan

- **Date:** 2026-11-14. **Status:** proposal; owner decisions in section 8. No product
  code changed by this plan.
- **Evidence:** `doc/01_research/compiler/memory_model/engine_memory_model_study_2026-11-14.md`
  ("the study"). Section and P-numbers below refer to it.
- **Supersedes:** the staging in `doc/05_design/compiler/jit_memory/seed_jit_array_reclamation.md`
  ("the JIT design"); see section 7. Its measurements and its Option A proof remain valid.
- **Builds on, does not replace:** `doc/03_plan/language/memory_safety/nogc_ownership_recovery_plan_2026-10-19.md`
  ("the no-GC plan"). This plan says how each engine reaches it and in what order.
- `rs/` abbreviates `src/compiler_rust/`.

## 1. Is a JIT memory model needed

**For values: no.** One language contract, implemented by every engine. A second rule
set for the JIT would make today's divergence permanent. The interpreter, the JIT, the
native backends and the heap-free tiers differ only in *how* they reclaim.

**For code: yes, and it is not JIT-only.** Executable memory created at run time needs
an owner, a generation and a release rule. The JIT, the loader and the JTAG remote
interpreter share that need. It exists locally and is missing for remote targets.

So the work is three tracks:

| Track | Content | Section |
|---|---|---|
| V | The value contract and each engine's conformance | 2, 3, 6 |
| X | Executable-memory ownership, local and remote | 4.1, stage M7 |
| T | Test and product introspection | 5 |

## 2. The contract

Twelve rules. Each is observable, so each can be tested on every engine. Rules marked
(OD) depend on an owner decision in section 8; the text is the recommended answer.

1. **Mutable value kinds** (array, dict, tuple, struct, enum and `Option` payloads) are
   values. Every share site yields an independent value: `let`, assign, store into a
   field, container or global, capture, return. An engine may copy, move when the source
   is dead, or share invisibly with copy-on-write. Two names never observe each other's
   writes.
2. **Immutable kinds** (text, closures, frozen data) may be shared freely; sharing is
   unobservable.
3. **Classes are references.** `var c2 = c1` shares identity on every engine (ruling of
   2026-11-04). A class instance has shared, counted, thread-confined ownership; `&C` is
   the opt-in unique form. (OD2)
4. **Parameters of value kinds are short borrows, the same for every value kind.** A
   plain parameter is read-only; a write through it is a compile error. `mut` grants an
   exclusive borrow whose writes the caller sees. One argument may not be passed as
   `mut` and as another argument in the same call. A class parameter is a shared
   reference: a write through it reaches the one instance, as on every engine today;
   whether that write should also require `mut` is part of OD3. (OD3)
5. **Return transfers ownership.** A returned value is owned by the caller and is never
   a borrow of a callee local.
6. **Release happens once, when the owner dies**: scope exit, overwrite, removal from a
   container. Owners in one scope die in reverse declaration order. When the memory is
   physically reused is not observable.
7. **Cleanup hooks.** There is no general destructor trait. `resource` types have a
   close hook that runs at owner death, including on error and cancellation edges, and
   resources are uniquely owned. `defer` stays. (OD6)
8. **Explicit pointer forms** keep the `memory.md` meanings: `&T` unique owner, `*T`
   counted shared and read-only, `@T` atomic counted, `-T` weak with `upgrade`, `+T`
   generational handle whose resolution is a fresh short borrow. A plain class type
   (rule 3) is a further form that `memory.md` does not list: counted, shared and
   mutable.
9. **Across threads** a value moves or is deep-copied. A class crosses only as `@T`.
   There is no shared mutable buffer. A region is ended only by the thread that opened it.
10. **Foreign boundary.** Each extern states, per parameter and result: borrowed for the
    call, transferred, or handle. A foreign handle is a resource. An object is freed by
    the allocator that made it. A remote or device address is not a managed value: the
    host never counts, copies-on-write or frees through it.
11. **A region is an owner.** An object leaves its region only through a checked
    move-out (promotion). Ending a region with a live outside reference is an error the
    quarantine mode must catch. A region is never the only mechanism inside an unbounded
    loop.
12. **Profiles.** *Hosted*: all rules. *Noalloc*: no heap and no hidden runtime call.
    *Remote payload*: noalloc, no runtime symbol at link, declared header-free layout for
    probe-visible types, scalar marshalling. A program accepted by a narrower profile
    behaves the same on a wider one.

Raw addresses, `nil` and `any` stay inside `unsafe` (existing owner rules).

What may differ between engines: the mechanism, the moment of physical reuse, the detail
of introspection. What may not: any row of the alias matrix, visibility of parameter
writes, class identity, the order and count of cleanup hooks, rejection of
use-after-move, the result of `upgrade`.

### Relation to the existing documents

- `memory.md` stays the source for pointer sigils (owner ruling 2026-10-20). Its "GC
  domain (default)" describes something no engine implements (P13); the recommendation
  is to mark it as not implemented and state the no-GC ownership default. (OD1)
- The no-GC plan's OWN rows map as follows: OWN-01 (one owner, transfer on share) is
  rules 1 and 5; OWN-03 (exactly-once cleanup) is rules 6 and 7; OWN-02 (a borrow
  allocates no control block) is implied by rule 4; OWN-06 (an owner need not be a heap
  object) by rule 12. OWN-04 (no cleanup after process death) and OWN-05 (no implicit
  forget) are not restated here and stay in force.
- Rule 3 departs from both documents for class types. It overrides `memory.md:28`
  (plain `T` is `&T` in no-GC mode), adds a mutable counted form next to the read-only
  `*T`, and reads against the no-GC plan's "no implicit RC for ordinary unique values".
  The reconciliation offered is that declaring a `class` is the explicit choice of
  shared ownership. If OD1 and OD2 are accepted, `memory.md` must be amended to say so.

## 3. Mechanism per engine

| Engine | Mutable value kinds | Immutable kinds | Classes | Regions |
|---|---|---|---|---|
| Seed interpreter | Keep `Arc` + copy-on-write. Already conforms to rule 1 | `Arc` | `Arc`; cycles leak (accepted) | Not needed |
| Seed JIT (both lanes) | Static: copy-or-move at share sites, release at owner death. No counts | Leak, bounded by regions | Leak, bounded by regions | Hand-placed per phase; per example in the test runner |
| Interpreter/JIT bridge | Deep copy per crossing (today) | – | Must preserve identity; today it copies (bug to file in M3) | – |
| Core interpreter (pure Simple) | Inherits its host engine. Its slot arena is ordinary Simple data | – | – | – |
| Self-hosted native backends | Static, same proof as the seed (shared pass) | Counted in the runtime | Counted, non-atomic | Owners with checked promotion |
| Noalloc tier | Static, no heap | Literals only | Not heap-allocated | Caller-supplied arenas |
| Remote payload, SVM-G | Static, no heap, no runtime call | Literals only | Rejected | – |

Rejected everywhere: a tracing or moving collector (no stack maps in any engine; breaks
rule 10 and the remote profile). Rejected for mutable value buffers: reference counts
(the JIT design's Option B; nothing changed since its rejection, and rule 1 makes them
unnecessary once share sites conform).

The seed is bootstrap-only by policy, so it gets the cheapest conforming mechanism and
may leak the kinds that would need counts. Regions bound that leak. (OD5)

## 4. Invariants per consumer

### 4.1 JTAG remote interpreter and remote execution

| Invariant | Guards | Enforced by |
|---|---|---|
| A payload accepted for the remote profile contains no heap allocation and no runtime call | Raw-linked target code | Compile check plus the existing undefined-symbol link error. Re-run as a gate after every stage that makes lowering insert calls (M2, M3, M6) |
| Target and device addresses are unmanaged | Host-held PC, SP, LR, code and device pointers | Rule 10; a typed address kind when a host interpreter over probe memory is built |
| Target code memory has one owner with per-unit release | Notebook sessions that keep target memory across cells | Stage M7 |
| Release of target or device memory is host-side and may be refused while completion is unknown | Halted or running targets, in-flight GPU kernels | Rule 7 resources with an explicit "leave allocated" outcome |
| Probe-visible state uses a declared, header-free, section-placed layout and is not a counted class | RTOS snapshot decode and restore | Stage M7; until then the snapshot path is documented as not layout-safe |
| Marshalling at the probe is scalar, with explicit width, sign and endianness | 32-bit targets under a 64-bit host | Remote profile check |
| Halt, resume and restore invalidate host views of target memory | Replay and checkpoint | Rule 10; no ownership operation spans a halt |
| Host code keeps array value semantics | `append_halt` | Rule 1, alias matrix |
| Host out-parameters keep working through the parameter migration | `save_state(..., cpu_regs_out)` | Rule 4 autofix adds `mut` |

### 4.2 Other modules

| Module | Invariant |
|---|---|
| Test runner | One example's garbage does not accumulate into the next (M5). Hook closures held by the BDD runtime and module-level bindings survive an example reset |
| MCP, LSP, T32 servers | Steady-state RSS per request. A request region promotes anything stored into module state |
| caret, DB arena | Overwriting a module-level container releases the old buffer (M2, overwrite release) |
| Compiler driver | Region promotion cannot free a live object; the two filed cases become regression specs (M5) |
| SimpleOS | No collector, no hidden allocation in `@noalloc` code; budgets enforced by its own owners |
| GPU, engine2d, SFFI | Handles are resources; release is explicit and deterministic; no finalizer may run later than the owner's death |
| Actors, channels, threads | Rule 9. The heap registry stays global; regions stay thread-local |
| Hot reload | A code unit is not unmapped while a live closure or object points into it (M7) |

## 5. Test and product introspection

The owner rule stands: tests may call private functions, and the test-path exemption is
not narrowed. That rule cannot be the only key for memory controls: it is enforced only
on the seed interpreter's call path, not on the JIT `main` lane and not across threads,
and it admits files under `src/**/test/` (study section 8). Design:

1. **Read-only statistics are public**: one module, `std.mem.stats`, on every engine.
   Live count and bytes per kind, including struct blocks. An engine that cannot answer
   returns `Unsupported`; zero is never a stand-in.
2. **Raw `extern fn rt_heap_*`, `rt_transient_*`, `rt_session_heap_*` declarations are
   fenced** to provider modules. The existing ratchet
   (`scripts/check/check-no-direct-rt.shs`) does not do this today: it counts extern
   declarations without gating them, its push row is advisory, and it scans `src` only.
   The work is to extend it to ratchet declarations of these prefixes, include `test/`,
   and make the row blocking. Existing users migrate to the modules in 1 and 3; the
   baseline only shrinks.
3. **Mutating controls are private functions of `std.mem.test_control`**: force an
   example reset, switch quarantine on, read owner and share counts, call private
   runtime hooks. Tests reach them under the private-access rule.
4. **The runtime checks a second key.** The test runner grants a test capability to the
   processes it starts; the runtime refuses every control in 3 without it, on every
   lane and thread. A product binary that calls a control fails loudly even if the
   visibility gate missed it. The key must not be something Simple code can set for
   itself; an environment variable is not enough, since programs can set those. An
   inherited descriptor or a token only the runner holds would do. If only an
   environment switch is built, it is an interlock against accidents, not a fence, and
   the documentation must say so.
5. **Open residual, now a prerequisite:** `fn main` on the JIT lane is not gated for
   private access. It must be closed before a spec relies on 3 from the JIT lane; item 4
   keeps product code safe in the meantime.

## 6. Order of work, and why

Fixing aliases adds copies; copies leak until releases exist; a release is unsafe while
an alias exists. The order that never makes things worse:

1. tools that make a wrong release loud and a leak visible;
2. releases that need no alias fix (fresh buffers that are provably never shared);
3. alias fixes by *move* (no new allocation);
4. each remaining alias fix as a *copy landed together with the release of its
   destination*, one matrix row at a time, with a memory gate.

## 7. Roadmap

Every stage records the binary sha256, runs serially under a memory cap, and keeps the
alias matrix output on both lanes as evidence. "Red first" means the acceptance spec
fails on the base binary.

| Stage | Work | Acceptance |
|---|---|---|
| **M0 Decide** | Owner answers section 8. Write the contract into `memory.md` (or beside it). File the bridge class-copy bug and the JIT dict-alias bug (P4) | Decisions recorded with date; no code |
| **M1 Tools** | Alias matrix as a spec on both lanes: the 20 rows of the JIT design plus dict assign, class identity, struct nesting, parameter writes. `std.mem.stats` with `Unsupported`. Struct blocks counted. Quarantine for every kind that can be freed. Extern fence in the ratchet | Matrix spec runs on both lanes with today's divergent rows tagged in-development. A 1,000-struct loop reports 1,000. Mutation "counters return zero" fails a spec on each lane. A use-after-free fixture aborts under quarantine, including through a typed index fast path |
| **M2 Proven-unique release (seed JIT)** | S1 (block-end release of fresh scalar arrays), then exit edges and text/nested elements, then overwrite release including module-level containers | Per slice: red first; the JIT design's positive rows flat (live delta ≤ 2 per 1,000) and every negative row unchanged; 2M-iteration RSS near the empty loop; Stage 2 bootstrap and `test/01_unit/compiler/interpreter` under quarantine with zero hits; matrix output identical before and after. Overwrite release: `xs = xs + [v]` in a loop holds flat |
| **M3 Single owner at share sites (seed JIT)** | Per matrix row: turn the alias into a move where the source is dead; otherwise copy and release the destination's previous value in the same change. Dict `let` copy lands only together with dict release at owner death, since nothing releases a dict before this stage. Struct release (the JIT design's S5) also lands here. Bridge keeps class identity. Call results become owned (rule 5), which replaces the JIT design's S4 summary | The row prints the interpreter's values on the JIT. Peak RSS of Stage 2 bootstrap and of the 128 KiB zstd decode is not above the M2 baseline. No new quarantine hit |
| **M4 Parameter rule** | Lint "write through non-`mut` parameter" in warn mode; count; autofix (`mut` for array and dict parameters, local copy for struct parameters); then error. Same rule for `for` loop variables. Class-parameter writes are not flagged | Count published; zero in the bootstrap closure before the error flips; JTAG `save_state` and the remote-exec specs pass unchanged in behaviour |
| **M5 Regions as owners** | Test runner opens a region per example on the JIT spec-entry lane and promotes module-level bindings and runtime-held hooks. Request region for MCP with promotion. Promotion runs under quarantine | The 1M-iteration comprehension spec peaks near one example's footprint instead of the sum. A spec that stores into a module-level `var` in one example and reads it in the next passes. The two transient-scope bugs of P9 are regression specs |
| **M6 Self-hosted backends** | Port the release proof (`mir_array_move.spl`), make `Drop` lowering real for value buffers, counted classes and text in the runtime, `*T`/`-T` at run time, resource close hook | The same matrix and counter specs pass on a natively built binary. The no-GC plan's drop and transfer acceptance rows move from unverified to verified |
| **M7 Code memory** | One owner contract for code units: owner, generation, unmap, covering the seed JIT, the loader, the self-hosted tiered JIT (`src/compiler/95.interp/execution/tiered_jit_manager.spl`, not examined in the study) and the remote lane. Remote mapper with per-unit release for notebook sessions. Unload refuses while a live closure points into the unit. Flat section-placed layout type for probe-visible state. Remote-profile gate (no runtime symbol) wired into M2, M3, M6 | A notebook session of N cells with replacement stays within the code region. Unload-with-live-closure is refused in a spec. Remote ARM32 and RV32 payload specs pass after each lowering change. Board path keeps working: QEMU real-firmware lanes first, hardware evidence where a board is available |

M7 does not depend on M2 or M3 and can run in parallel. In M4 the lint and the `mut`
autofix can run in parallel too; the struct autofix adds a struct copy per call, which
the seed JIT cannot release before M3, so it waits for M3. M6 needs OD2 and OD7.

S1 may land before M1 although section 6 puts tools first: it carries its own
quarantine mode for the one kind it frees. Every later slice waits for M1.

Enums: an enum payload is a value (rule 1). On the seed JIT enum blocks are not
released (OD5); they are treated like structs once M3's struct release exists.

### How this changes the JIT design's plan

| JIT design item | Now |
|---|---|
| Option A, proven-unique release | Kept as M2. Its proof and allowlist stand |
| S1 | M2 first slice. Verdict below |
| S2 (exit edges, text, nested), S3 (overwrite) | M2, unchanged in content. Non-scalar elements wait for OD2 and OD7, because releasing an array of classes or text needs to know who owns the elements |
| S4 (fresh-return summary) | Replaced by rule 5 in M3 |
| S5 (struct temporaries) | M3; needs structs counted (M1) |
| Option B, reference counts | Still rejected for value buffers. Adopted only for classes and text, only in the self-hosted runtime (M6) |
| C1 explicit regions | Kept. C2 per example becomes M5 with promotion. C3 per frame stays rejected |
| Option D, nothing in the seed | Rejected: the seed runs the specs and the bootstrap today |
| Option E, tracing collection | Rejected for every engine |
| D1-D7 | Mapped in section 8 |

### Verdict on slice S1

Branch `work/jit-array-free-s1-20261114` (commits `4e69c9a7521`, `59bca88628b` in
worktree `simple-jit-free-s1-20261114` at the time of writing).

**Land it, with conditions. Do not change its design and do not drop it.**

Why it is sound under this plan: it releases only a buffer that lowering itself just
created (a literal or its own copy) and that the proof shows was never handed to another
name. Such a buffer cannot be either side of any alias row, so S1 is safe while the JIT
still aliases at 15 sites and stays correct after M3. Two things are part of that
argument and must stay: the runtime removes a freed array from any open transient scope
or session (otherwise the region is a second holder), and the proof's exclusions
(functions with `defer`, captured locals, `for` pattern locals, module-init functions,
any early exit after the `let`, uses other than scalar index and `len`). The Opus
reviewer read the S1 commits looking for a counter-example and found none; nothing was
executed in that review.

Conditions before landing:

1. Stage 2 bootstrap and the interpreter unit directory run under
   `SIMPLE_ARRAY_FREE_QUARANTINE=1` with zero hits; the binary sha256 is recorded.
2. The alias matrix prints identical values before and after, on both lanes.
3. The acceptance spec of the JIT design (positive rows flat, every negative row
   unchanged, transient-scope survivor case) is in the change and was red first.
4. `[f64]` is either covered by an RSS row or excluded; a boxed float element would
   leak, not corrupt.
5. The emitted free is documented at the site as a release of a proven-unique buffer.
   If arrays ever become shared copy-on-write buffers, this call must become a counted
   release; a comment and a todo make that visible.
6. A todo records the missing `mir_array_move.spl` twin; the twin is required before
   the next M2 slice (OD9).
7. A spec covers an S1 local freed inside an open transient scope, with a later
   allocation and a read of a survivor after the scope ends.
8. The quarantine set is a mutex-guarded set in the runtime. Under the lockless rule it
   needs a documented exception (debug-only, off by default) or a lock-free form.

S1 alone does not fix the reported growth: the core interpreter's rows are `[[text]]`
and module-level overwrites, which need the later M2 slices.

## 8. Owner decisions needed

Recommendations first; the mapping to the JIT design's D1-D7 is in brackets.

1. **OD1 Governing statement [D1].** Adopt the twelve rules as the contract and mark
   `memory.md`'s "GC domain (default)" as not implemented. *Recommend yes.*
2. **OD2 Who owns a class instance.** Counted, thread-confined shared ownership, with
   the `class` keyword read as the explicit opt-in; `&C` for unique. Counts only in the
   self-hosted runtime; the seed leaks classes inside regions. *Recommend yes.* The
   alternative, unique-with-move, breaks every program that aliases a class.
3. **OD3 Parameter rule [D6].** `memory.md` Rule 4 for every value kind, introduced by lint,
   then autofix, then error. *Recommend yes;* the migration size is unmeasured and M4
   measures it before anything becomes an error. For class parameters the recommendation is to leave writes legal without `mut` for now (classes are shared references; the lint does not flag them) and revisit after M4 has numbers.
4. **OD4 Fix JIT aliasing in the seed [D2].** *Recommend yes,* move-first and each copy
   paired with a release (M3), limited to the measured matrix rows.
5. **OD5 Seed investment ceiling [D3, D4].** *Recommend* M1 to M3 for arrays, dicts,
   tuples and structs; text, closures, enums and classes leak on the seed and are
   bounded by regions (M5).
6. **OD6 Cleanup hooks.** No general destructor trait; resource close hook plus
   `defer`. *Recommend yes.*
7. **OD7 Text and closures.** Immutable and shared; counted in the self-hosted runtime.
   *Recommend yes.*
8. **OD8 Introspection.** Public read-only statistics, fenced raw externs, private
   controls plus a runtime-checked test capability; the test-path rule is not narrowed.
   *Recommend yes.*
9. **OD9 Parity [D5].** The seed may lead for S1; the self-hosted twin is required
   before each later slice. *Recommend yes.*
10. **OD10 Hand-written `rt_array_free` in Simple source [D7].** Freeze by ratchet now;
    remove each site when M2 or M3 covers it. *Recommend yes.*
11. **OD11 Code memory and probe-visible layout.** One owner contract including a
    remote mapper; probe-visible types are flat, header-free and not classes.
    *Recommend yes.*

## 9. Risks

- **Copy cost.** Static copy-or-move makes move precision a performance property. Each
  M3 row has a memory gate; a time gate on Stage 2 bootstrap should be added with it.
- **Migration size of rule 4 and of counted classes is unmeasured.** M4 and M6 start
  with a count, not a change.
- **Quarantine coverage.** Typed and inline index fast paths may not call a validated
  accessor (JIT design, constraint 8). M1's fixture must prove they trip.
- **Two runtimes.** The C and Rust runtimes define the same symbols; rule 10's "freed
  by the allocator that made it" needs a check where both are linked.
- **Unattributed evidence.** The caret RSS (P14) is not proven to be this problem. M2's
  overwrite release should be measured against a recorded caret session before it is
  claimed as the fix.
