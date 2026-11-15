# Engine memory model study

- **Date:** 2026-11-14. **Base:** `ec758ee501c` (`origin/release/1.0.0`). No product code changed.
- **Question (owner):** is a JIT memory model needed; what is broken today; what must a
  model support (JTAG remote interpreter, other modules); consistency with the compiler;
  test-runner private access.
- **Plan that follows from this study:** `doc/03_plan/compiler/memory_model/unified_memory_model_plan.md`.
- **Method:** Fable read the code and ran the probes in section 2; three read-only search
  agents built the inventories; two Opus agents then worked independently (section 9).
- `rs/` abbreviates `src/compiler_rust/`. "Measured" means run in this study on the seed
  in section 2.1. "Read" means taken from source and not executed. "Unverified" is said
  where it applies.

## 1. Answer in brief

1. **No separate JIT memory model is needed for values. A written language memory
   contract is needed, and there is none that the engines implement.** No engine needs
   semantics that another cannot implement (section 6). What differs, and may keep
   differing, is the reclamation *mechanism* per tier.
2. **A model for executable memory is needed, and that is the part specific to a JIT
   and to the JTAG remote interpreter**: who owns an uploaded or mapped code unit, when
   it is replaced or unmapped, and what may still point into it. It exists locally
   (`SharedExecMapper`) and not for remote targets (sections 4 and 6). The first draft
   of this study missed it; the Opus critic found it (section 9).
3. The JIT's two visible defects are one defect. It **aliases** where the language says
   copy (15 measured forms: the design doc's 14 plus dict assignment; section 5) and it
   **never frees**. Both come from the same missing rule: a mutable value buffer has
   exactly one owner. Every alias form is a place where a second owner is created
   silently. Where ownership is single, a release at the owner's death is sound without
   reference counts. Immutable values (text, closures) and class instances are shared by
   design and need a different mechanism (section 9, items 3 and 4).
4. The contract documents disagree and the ownership features are not implemented:
   `memory.md` describes a GC default that no engine has; the no-GC plan describes
   unique ownership that no backend lowers; that plan's acceptance file shows none of
   its 35 non-core criteria evidenced as closed (its nine core rows are tracked
   separately, and "unverified" there does not assert the implementation is absent).

## 2. Current problems (first-hand)

### 2.1 Binary and method

- Seed: `/home/yoon/dev/.cargo-target-nested-mod-20261114/release/simple`, sha256
  `220e1bea5833bd0ea705dc96cbfba0044d4d146cda2c41b33440bd2e4aa4557e`, built 2026-11-14
  12:22 by another lane from worktree `simple-nested-mod-20261114` (near `ca3b0b74bd6`;
  whether that tree was dirty is unknown). It is not a build of the base commit.
- Runs: serial, from the study worktree,
  `systemd-run --user --scope -q -p MemoryMax=12G timeout 600`,
  `SIMPLE_EXECUTION_MODE=interpret|jit SIMPLE_JIT_STRICT_ALL=1 simple run <probe>`.
- Probe sources: appendix.

### 2.2 Findings

| # | Problem | Evidence |
|---|---|---|
| P1 | Seed JIT frees nothing. 1,000 loop iterations leave 1,000 live arrays and 1,000 live dicts, `frees=0`. | Measured (`cnt.spl`). Matches `doc/05_design/compiler/jit_memory/seed_jit_array_reclamation.md` section 2.3, which has all kinds and RSS. |
| P2 | Structs are invisible to the counters: 1,000 struct literals report `allocs=0`. | Measured. Raw `rt_alloc` blocks, `rs/compiler/src/codegen/instr/closures_structs.rs:571-573`. |
| P3 | JIT aliases where the interpreter copies: return through a function, struct-literal field, global store, `push`, plain assign. | Measured (`alias.spl`): A5, A6, A8, A9, A10 print `1` on the interpreter and `9` on the JIT. |
| P4 | **New:** dict `var d2 = d1; d2["k"] = 9` copies on the interpreter and aliases on the JIT. The JIT copies arrays on a `Let` but not dicts. | Measured (row D1). |
| P5 | Parameter rules differ by kind on *both* lanes: a callee's `x[0] = 9` on an array parameter is seen by the caller; `p.a = 9` on a struct parameter is not. | Measured (A3 = 9, S2 = 1 on both lanes). |
| P6 | Ownership sigils are not enforced on the run path in the default mode (`nogc_strict` was not probed). `val c = u2` on a `&Node` is accepted and both names stay usable (`memory.md` Rule 2 says error). `weak_of` does not exist at run time. | Measured on the interpreter (`ptr.spl`). `Expr::New` is a stub returning the inner value, `rs/compiler/src/interpreter/expr/ops.rs:456-461`. `weak_of` is type-checked (`rs/type/src/checker_ownership.rs:159`) and has no run-time implementation. |
| P7 | No working destructor. `trait Drop` and seven `impl Drop for` exist only in the seed-side std (`rs/lib/std/src/core/traits.spl:268`); `src/lib`, `src/compiler`, `src/app` and `src/os` have none (grep over `src`, 8 hits, all under `rs/lib/std/`). A user `impl Drop for Res` is accepted on both lanes and its `drop` never runs (measured, `dropd2.spl`): a silent no-op. Cleanup today is `defer` (works on both lanes, measured) and explicit `close`/`release`/`_free`. | Self-hosted MIR emits `Drop` only for `resource` locals (`src/compiler/50.mir/mir_lowering_stmts.spl:592`), and every backend lowers it to nothing: `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:1521`, `src/compiler/70.backend/backend/native/isel_x86_64.spl:498`, `src/compiler/95.interp/mir_interpreter.spl:664-672`. |
| P8 | The core interpreter never frees value slots during a program. `val_free` has one caller; `val_reset` runs once in `eval_init`. | Read: `src/compiler/10.frontend/core/interpreter/value.spl:161-174`, `eval_decls.spl:418`. Per-iteration array counts: `doc/08_tracking/bug/core_interp_per_iteration_array_leak_2026-11-14.md`. |
| P9 | Regions are the only bulk reclamation and they have freed live data twice. | `doc/08_tracking/bug/option_struct_none_box_freed_by_transient_scope_2026_11_09.md` (P1), `s3_parse_selected_result_freed_by_transient_scope_2026-11-02.md`. Rust lowering never emits a region; Simple source brackets phases by hand (`src/compiler/80.driver/driver_hir_pipeline_lowering.spl`). |
| P10 | Hand-written `rt_array_free(` in 13 Simple source files under `src/` (compiler front end, LLVM backend, `simple_core`); the count includes `extern` declarations. Each call is an unchecked manual free. | Exhaustive grep; e.g. `src/compiler/10.frontend/core/lexer.spl:39-44`. |
| P11 | Introspection is ungated. `cnt.spl` lives outside any `test/` path and calls `rt_heap_*` freely. Product code declares the same externs for legitimate reporting (`src/lib/nogc_sync_mut/mem/dump.spl:21-23`, `src/app/cli/native_build_worker.spl:24-29`). | Measured and read. |
| P15 | Module-level accumulation by rebuild: `CHAT_CONTENTS = CHAT_CONTENTS + [content]` (`src/app/llm_caret/chat.spl:72`) builds a new array per turn. With no release of the old one the retained bytes grow quadratically with turns. | Read (found by the Opus critic). A candidate cause for P14, not measured. |
| P12 | Counters read zero on the interpreter for every row. A test that only reads counters passes vacuously there. | Measured. The no-GC plan lists "return fabricated zero allocation counters" as a mutation a gate must catch (`doc/03_plan/language/memory_safety/nogc_ownership_recovery_plan_2026-10-19.md:813`). |
| P13 | The documents disagree. `memory.md` makes GC the default domain (`doc/05_design/language/misc/memory.md:10`, `:55`). Program values never reach a collector: `--gc=off` only selects `NoGcAllocator` for the runner (`rs/driver/src/exec_core.rs:253-257`); per the search agent that allocator receives SMF code bytes only (not re-read). The no-GC plan requires a unique owner and forbids implicit RC and GC (plan `:51-56`). | Read. |
| P14 | Live long-running data point: two caret processes (`simple run src/app/llm_caret/cs_main.spl`, default lane, no `SIMPLE_EXECUTION_MODE`) at 13.9 GB and 11.4 GB RSS after 68,582 s; RSS equals peak. Two `slang_server` processes on the same kind of seed sit at 132 MB and 35 MB after 84,459 s and 156,739 s. | Measured with `ps`. **Not attributed:** whether caret's modules run JIT'd or fell back to the interpreter was not determined, so this is not proof of P1 as the cause. |

One side observation, cause not investigated: a probe with `defer print "x"` on one line
and paren-less `print` did not run the deferred statement on the interpreter; the
variant with a `defer:` block and `print(...)` ran on both lanes. Two things differ
between the probes, so which one matters is unknown.

## 3. Engine inventory

Citations in this table were collected by search agents and spot-checked; rows marked ‡
were not re-read by Fable.

| Engine | Value representation | Reclamation | Array assign | Struct / class | Cleanup hooks |
|---|---|---|---|---|---|
| Seed interpreter | `Arc` everywhere: arrays `Arc<ArrayData>` with `Arc::make_mut` (`rs/compiler/src/value.rs:3112-3116`), dict `:3138`, struct `Object` `:3159-3162` | Rust refcount drop. Class cycles presumably leak (unverified). | Copy-on-write: observably a copy | Struct value (CoW). Class reference, `Arc<ClassInstance>` (`value.rs:3165`; field locking per the search agent), default since 2026-11-04 (`value.rs:3496-3506`) | `defer` yes; `errdefer` no-op ‡ (`rs/compiler/src/interpreter/node_exec.rs:760-766`) |
| Seed JIT, main lane | Runtime heap objects, header without refcount (`rs/runtime/src/value/heap.rs:57-66`); structs raw blocks | None, except one field-overwrite site (`rs/compiler/src/mir/lower/lowering_stmt.rs:708-765`) | Copy on `Let` from a place; alias at every other share site | Struct copies on `Let`/param; class reference | `Drop` no-op (`rs/compiler/src/codegen/instr/mod.rs:1494-1529`); `defer` yes |
| Seed JIT, spec-entry lane | Same codegen; the seed wraps examples in a generated `main` (`rs/driver/src/exec_core.rs:1651-1683` ‡) | Same: none. All examples of a file share one heap. | Same | Same | Same |
| Hybrid interpreter splice | Deep copy in both directions per crossing (`rs/compiler/src/runtime_bridge.rs:65-171` ‡). Classes cross by value; pointer kinds become nil (`:158` ‡) | None on the JIT side | Copy | Class identity is lost across the bridge | – |
| Core interpreter (pure Simple) | Parallel-array arena with slot free list (`value.spl:30-47`, `:129-153`) | Slot reuse only through one caller; whole arena reset per program | CoW with a backing refcount (`value.spl:271-326` ‡) | Classes keep identity | Runs on whatever engine hosts it, so it inherits P1 on the JIT |
| Self-hosted backends (LLVM, native x86_64/aarch64/riscv, cranelift adapter) | C runtime objects (`RtCoreArray`, `src/runtime/runtime_native.c:1516-1524` ‡), allocated with `malloc` per the search agent, not re-read | None emitted. `rt_array_free` (`:9448` ‡), `rt_rc_*`, regions exist but are explicit calls | Eager shallow copy, move where proven (`src/compiler/50.mir/mir_lowering_stmts.spl:922-960` ‡, `src/compiler/50.mir/array_move/mir_array_move.spl`) | AOT copies structs; aliases list and dict element extraction (`doc/07_guide/language/value_semantics_by_engine.md:187-188`) | `Drop` no-op |
| Wasm / C backends | Wasm bodies are `unreachable` stubs (`src/compiler/70.backend/backend/wasm_codegen_adapter.spl:54-56` ‡). An AST-to-C++ generator exists (`src/compiler/10.frontend/core/compiler/c_codegen.spl`, 773 lines) and emits no free ‡ | None | not measured | not measured | Wasm is not an engine today |
| Other lanes, existence only | Self-hosted `MirInterpreter` (aggregates at virtual addresses in dicts, `src/compiler/95.interp/mir_interpreter.spl:57-72` ‡); SMF bytecode VM (`rs/runtime/src/bytecode/` ‡); fork shared-heap worker (`rs/runtime/src/fork_shared_heap_v1.rs` ‡); Lua and IrTc backend kinds ‡ | No reclamation seen in `MirInterpreter` | – | – | Whether each is reachable from `run` was not checked |
| Noalloc / baremetal tier | Bump, free-list, fixed-block, pool allocators over a caller region (`src/lib/nogc_async_mut_noalloc/baremetal/allocator.spl` ‡) | Allocator-specific, explicit | – | – | `@noalloc` is a hard error (`src/compiler/35.semantics/noalloc_checker.spl:3-14` ‡). The gc/nogc directory split is a warning-only lint ‡ |
| Remote CPU payload (JTAG) | No runtime, no heap (section 4) | Host overwrites the code region | – | – | – |
| SVM-G GPU VM | 32-bit stack VM, static slots, 64 KiB data region | None needed; lowering rejects allocation | – | Rejects struct and enum literals | – |

Ownership features across engines: sigils parse (`src/compiler/10.frontend/parser_types_expr.spl:66-84` ‡);
HIR keeps Unique/Shared/Weak only under `nogc_strict` ‡; MIR lowers them to plain
references ‡; the C runtime's unique/shared constructors are identity stubs
(`runtime_native.c:21980-21990` ‡); the seed JIT emits `rt_unique_new`/`rt_shared_new`
but never a release ‡. The plan's own acceptance file records none of its 35 non-core
criteria evidenced as closed
(`doc/03_plan/language/memory_safety/nogc_remaining_acceptance_evidence_2026-10-21.md`).

Not examined (found by the final Opus review): the self-hosted tiered JIT
(`src/compiler/95.interp/execution/tiered_jit_manager.spl`), which also creates
executable memory; ExecIR and the MIR SIMD interpreter in `src/compiler/95.interp/`; the
CUDA, HIP, OpenCL and Vulkan compute backends; long-lived notebook local, CUDA and
Vulkan sessions in `src/lib/nogc_sync_mut/notebook/`.

## 4. The JTAG remote interpreter

The glossary defines the term: a remote interpreter "executes same frontend/lowering
contract but targets remote memory", "requests exec allocation from remote mapper", places
bytes through a "memory copier bridge (gdb/trace32/etc.)" and "keeps local/remote
behavior identical except memory transport backend" (`doc/glossary.md:260-266`). So it
is a JIT whose code memory is on the target. In the tree the name covers three different
things; none is a host interpreter that keeps Simple objects on a target.

| Mechanism | What executes where | Memory |
|---|---|---|
| `interpreter(remote(...))` test mode | For `.spl`: the **host** interpreter in a child process. For `.elf`: a prebuilt semihosted ELF on QEMU or GHDL (`src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl:391-406` ‡) | Host process memory only |
| Remote JIT execution (`src/lib/nogc_sync_mut/debug/remote/exec/`), the JTAG/T32/OpenOCD/QEMU lane | Host compiles a function to raw target bytes, bump-allocates in the target code region, uploads in chunks and reads back, writes PC/SP/LR and argument registers, resumes, waits for the halt instruction, reads the return register (`manager.spl:51-152`) | Target: code region + stack from a fixed `MemoryMap` (`types.spl:15-28`). Host: target addresses as plain `i64`, bytes as `[i32]`. |
| SVM-G GPU "remote interpreter" | A VM resident on the device runs lowered bytecode; host talks through a mailbox | Device: fixed arena. Host: raw `i64` device pointers with manual `rt_alloc`/`rt_free` ‡ |

Facts that constrain a memory model (read first-hand unless marked):

- **The payload has no runtime.** ARM32 payloads are compiled for `thumbv7m-none-eabi`
  in the `baremetal` context and raw-linked; an undefined symbol is a link error
  (`src/compiler/70.backend/backend/native/remote_arm32_compile.spl:32-38`, `:88-90` ‡;
  `src/compiler/70.backend/linker/elf/arm32_raw_link.spl:122-123` ‡). So a payload cannot
  call `rt_array_new`, a retain/release helper, or a region call. Whether RV32 also
  rejects unresolved symbols is unverified.
- **Target code memory is a region owned by a host object, and it is not the local
  code-memory owner.** `TargetMemoryAllocator` is a bump allocator with `reset()` and no
  per-allocation free (`memory_alloc.spl:19-39`). Local JIT and loader code goes through
  `SharedExecMapper` with owners and generations
  (`src/compiler/99.loader/loader/object_mapper.spl:39`); the glossary's "remote mapper"
  is not built.
- **Two lifetimes exist.** The test lane makes a fresh manager per run ‡, so the next
  run overwrites. The notebook lane keeps one session and its target memory across
  cells (`src/lib/nogc_sync_mut/notebook/remote_exec.spl:341-345`); every cell bumps the
  allocator and nothing is released until `reset()`, so a long session exhausts the
  code region.
- **Arguments and results are scalars by value** (`manager.spl`, register writes and
  one register read). No object crosses the probe.
- **Teardown is host-only** (disconnect). Nothing may require a target round trip to
  release memory.
- **The library compile bridge fails closed today** (`compiler_bridge.spl:22-26`); specs
  that run real code call the target compilers directly ‡. The lane is real but thin.
- **The RTOS JTAG snapshot decodes a Simple class at fixed byte offsets**
  (`src/os/realtime/jtag/state_capture.spl:49-62` ‡ against `state_layout.spl:45-55` ‡)
  and restores raw bytes. The class holds heap arrays, nothing places it in the
  `.rtos_state` section, and its prepare step allocates on the target ‡. So the
  dependency is on a feature that does not exist yet: a flat, header-free,
  section-placed type. It is not a layout that works today and must be preserved.
- **The host side relies on array value semantics.** `append_halt` copies the byte array
  and pushes; the caller then uses the original length as the halt address
  (`manager.spl`, `execute_bytes`).
- **The host side also relies on caller-visible writes through a plain array
  parameter.** `save_state(..., cpu_regs_out: [u64])` pushes into its parameter
  (`src/os/realtime/jtag/state_capture.spl:56`). This is P5 in use.
- The RV32 payload path also rejects undefined symbols ‡ (Opus critic, citing
  `src/compiler/70.backend/backend/native/mod.spl:227`; not re-read by Fable).
- GDB-MI, ptrace and TRACE32 backends read frames and variables through GDB and DWARF;
  no code decodes the heap header ‡.

Requirements this places on the model:

1. A **no-runtime tier** must exist in the contract: code that is accepted for it has no
   heap allocation and no hidden runtime call. Any reclamation scheme that inserts calls
   (retain/release, write barriers, safepoint polls, region begin/end) must be provably
   absent from that tier, enforced at compile and at link.
2. **No moving collector** for any object whose address can be held outside the engine:
   target memory, device memory, probe-visible state, SFFI handles.
3. **Deterministic, host-side release** of target and device regions, with an explicit
   "leave it allocated" outcome when completion is unknown (the CUDA session already
   does this ‡).
4. **Stable declared layout** for probe-visible types, without a hidden object header in
   front of the fields.
5. **Scalar or by-value marshalling** at the probe boundary; no host object may be
   reachable from target memory.
6. **Bounded stack** on the target; today the CPU lane passes `stack_bytes: 0` and checks
   nothing ‡.
7. **One code-memory owner contract for local and remote.** A code unit has an owner, a
   generation and an explicit unmap; a session that outlives one run (the notebook) can
   release or replace a unit; dropping the host owner while the target may still be
   running is a defined state, not an accident.
8. **A remote-address kind.** A target address held by the host is never retained,
   released, copied on write or freed by the host's value machinery. Today it is a bare
   `i64`, which is safe only because integers are not managed.
9. **Width and endianness are data**, not assumptions: a 32-bit target under a 64-bit
   host needs defined sign and zero extension at the boundary.
10. **Halt and restore invalidate host views.** Any host-side cache of target memory
    is dead after resume or snapshot restore. No ownership operation may be left half
    done across a halt.

Items 7-10 come from the Opus critic. Items 8-10 guard a host interpreter over probe
memory that does not exist yet; they cost nothing today and are listed so the contract
does not rule that design out.

## 5. Consistency: what the engines disagree on, and which is right

Reference documents: `doc/07_guide/language/value_semantics_by_engine.md:90` ("arrays and
text copy on assignment in every engine"), `memory.md` Rules 1-5, the no-GC plan
(OWN-01 to OWN-06, plan `:161-171`).
Provenance of the table: this study ran A1, A3, A5, A6, A8, A9, A10, the dict row, the
struct and class rows for `let` and parameters, and text, on the interpreter and JIT. The
other array rows (A7, A13-A20) are the JIT design's measurements. The native column and
the struct-extraction, nested-struct and `m[1][0]` rows are the guide's 2026-08-10
measurements and may be stale.


| Form | Interpreter | JIT | Native (AOT) | Right per the documents |
|---|---|---|---|---|
| `var b = a` (array) | copy | copy | copy | copy |
| `b = a` plain assign (A10) | copy | alias | not measured | copy |
| array returned through a function (A5) | copy | alias | not measured | copy (or move if `a` is dead) |
| array stored into struct literal, global, container, tuple, `Some`, dict, captured (A6-A9, A13-A20) | copy | alias | not measured | copy (or move) |
| `var d2 = d1` (dict) | copy | alias | not measured | copy. Not written anywhere for dicts; follows from "containers are values" |
| struct `var f2 = f` | copy | copy (since the 2026-08 fix) | copy | copy |
| struct with nested struct field, copy then mutate | copy | alias in the 2026-08-10 measurement; later deep-copy fix not re-measured here | copy | copy |
| `var e = lst[0]; e.a = ..` (struct from list or dict) | copy | copy | alias | copy |
| callee mutates array parameter (A3, A4) | caller sees it | caller sees it | not measured | **Neither.** `memory.md` Rule 4: a plain parameter is shared read access and the write is an error; `mut` grants it |
| callee mutates struct parameter (S2) | caller does not see it | caller does not see it | caller does not see it | Same rule: an error without `mut` |
| element passed as argument, callee mutates (A19) | copy | alias | not measured | Same rule |
| class `var c2 = c1` | shared identity | shared identity | not measured | Shared identity. Owner ruling 2026-11-04: classes are reference types on every engine, structs are the value types (`doc/07_guide/language/capability_library_authoring.md:33-36`). **Who frees a shared instance is undecided**: `memory.md` makes plain `T` a unique `&T` in no-GC mode, which contradicts free sharing |
| class across the interpreter/JIT bridge | copied by value (`rs/compiler/src/runtime_bridge.rs:183-187`, comment still cites the superseded value-type ruling) | – | – | identity must be preserved; the bridge is wrong |
| `Dict.remove` return value | differs from native, per a source comment (`src/compiler/99.loader/loader/object_mapper.spl:72-75` ‡) | not measured | differs | not a memory rule; listed because the code-memory owner depends on it |
| `m[1][0] = 9` | rejected (2026-08 measurement) | works | works | accept; the interpreter is wrong |
| drop order, finalizers | none | none | none | plan OWN-03: exactly-once cleanup at the owner's scope end. Unimplemented everywhere |
| `-T` weak, `*T` shared | not constructible | handles created, never released ‡ | identity stubs ‡ | `memory.md`; unimplemented everywhere |

Summary: for value kinds the **interpreter is right** and the JIT and native lanes are
wrong at specific sites. For parameters **no engine is right**: the rule the documents
state is not what any engine does, and existing code (including the JTAG host code,
section 4) depends on today's behaviour. For classes the engines agree with the latest
ruling on identity, and the ownership documents have not caught up. Both are owner
decisions, not bugs to fix quietly.

## 6. Is a distinct JIT memory model needed

The test: does any engine need observable semantics that another engine cannot
implement? Checked against each constraint found:

- Interpreter: implements value semantics with shared buffers and copy-on-write. That is
  an implementation of "copy", not a different semantics.
- JIT and native: can implement the same observable result with copy-or-move at share
  sites and a release at owner death. Nothing in cranelift or the runtime prevents it;
  the single existing free site already works (design doc section 2.3).
- Noalloc and remote payload tiers: need *less* (no heap), which is a restriction of the
  same contract, not a different one.
- Long-running modules (section 7): need bounded growth, which any deterministic
  release gives.

So for values: **one contract, several conformance profiles.** A "JIT memory model" as a
separate set of value rules would cement the divergence in section 5. What the JIT needs
there is an implementation plan for the common contract, and the plan document provides
that.

For code the answer is different. A JIT, a loader and a remote interpreter all create
executable memory at run time, and an interpreter does not. That memory needs an owner,
a generation, a release rule, and a rule for what may point into it (closures, vtables,
return addresses on a halted target). The local half exists as `SharedExecMapper`; the
remote half is a bump allocator with no owner contract; hot unload does not check for
live closures (section 7). This is the one place where "a JIT memory model" is a real,
separate need, and it is shared by the JIT, the loader and the remote lane.

What the JIT legitimately may differ in: the mechanism (static release, no refcount on
value buffers), the timing of physical reuse, and introspection detail. What it may not
differ in: whether two names observe each other's writes, whether a parameter write is
visible, when a cleanup hook runs.

## 7. Modules that depend on memory behaviour

| Module | Engine in practice | Lifetime | Reclamation today | What it needs |
|---|---|---|---|---|
| Test runner | Spec child forced to the interpreter (`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:345` ‡); `# @jit_spec_entry` files on the JIT | One process per spec file; daemon long-lived (`src/app/test_daemon/light_daemon.spl` ‡) | Process exit only. No per-example reset | Per-example reclamation or a bounded per-file footprint; a 1M-iteration example peaked at 15.2 GB (bug doc) |
| MCP, LSP, T32 servers | `simple-mcp` on the interpreter by configuration; `simple-lsp-mcp` through a cached native wrapper; `t32-mcp` interpreted with a 512 MB cap (`.mcp.json` ‡) | Long-running request loop | None per request | Steady-state RSS. A request-scoped region alone is unsafe: requests store into module globals (`src/app/mcp/main_static_tools.spl:165` ‡, `src/app/mcp/dap_bridge.spl:297` ‡), so a region needs checked promotion |
| caret | Seed default lane | Long-running (19 h observed) | None | Release on overwrite of module-level containers (P15). 11-14 GB observed (P14, unattributed) |
| BDD runtime state | Seed runtime | Per spec process | None | Hook closures registered by `before_each`/`after_each` are held by the runtime (`rs/runtime/src/value/bdd_sffi.rs:86-88` ‡) and must outlive the scope that registered them; a per-example region must not free them |
| slang server | Seed default lane + native ggml | Long-running | Explicit close/`dlclose` ‡ | Foreign handle lifetimes; RSS returns well below peak |
| Self-hosted compiler driver | Seed JIT (bootstrap), then native | One-shot, large | Hand-placed transient scopes, session heap, `rt_array_free` | Region promotion that cannot free live data (P9) |
| SimpleOS kernel / userland | Native + C runtime | Per boot | Kernel mimalloc port, boot-path bump allocator, userland dlmalloc ‡ | Real free; no collector; budgets enforced by its own owners (plan `:642`) |
| GPU / Vulkan / engine2d | Any | Per session | Manual `retain()`/`release()` in Simple code ‡; `i64` handles | Deterministic release; never free while the device may still use the buffer (plan `:640`) |
| SFFI / `rt_*` boundary | All | – | Text copied in; `i64` handles freed by explicit `_free`/`_close` (`doc/07_guide/platform/ffi/sffi.md:477` ‡) | An ownership statement per extern: borrowed, transferred, or handle |
| Actors, channels, threads | JIT / interpreter | Long | Channel send copies text and numbers only and refuses the rest (`rs/runtime/src/value/channels.rs:122-133` ‡); isolated spawn copies ‡ | Move or copy across threads; never a shared mutable buffer. Transient scopes are thread-local ‡, so a region must not be ended from another thread |
| DB engine | Any | Long | Arena is a global `[[u8]]`; discard assigns `[]` (`src/lib/nogc_sync_mut/db/dbfs_engine/arena.spl` ‡) | Overwrite must release the old buffer (stage S3 of the old design, stage 3 of the new plan) |
| Hot reload / module unload | Seed, self-hosted loader | Long | Code unmapped; objects untouched ‡ | Closures and objects that point into unloaded code must be dead or refused first |
| JTAG remote execution, SVM-G | Target / device | Per run | Section 4 | Section 4 requirements |

Older records consulted: `simple_test_runner_memory_leak_2026-06-14.md` (parent runner
45-118 GB, open), `phase2_test_runner_rss_cap_2026-10-12.md`,
`seed_jit_array_copy_never_freed_2026-10-19.md`,
`seed_jit_field_store_array_copy_never_freed_2026-11-04.md`,
`native_array_copy_leaks_2026-10-20.md`,
`simpleos_bump_heap_no_free_interactive_session_2026-07-26.md`,
`lsp_mcp_server_process_leak_2026-07-05.md` (all under `doc/08_tracking/bug/`). The bug
directory has roughly 220 memory-related file names; only these were read.

## 8. Test-runner interpreter and private access

Facts:

- Owner rule: test code may call private functions; a refusal is a compiler bug.
- The gate is a path rule. Seed: `is_test_caller`
  (`rs/compiler/src/interpreter_module/module_loader.rs:2858`), a path that starts with
  `test/` or has a `/test/` component. Self-hosted twin:
  `private_import_is_test_importer`
  (`src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl:65`).
- Only the seed interpreter enforces the *call* gate. `fn main` on the JIT lane is not
  gated (`doc/08_tracking/bug/private_call_gate_skips_import_bound_and_entry_calls_2026-11-14.md:112`).
  The seed's private-name registry is thread-local and fails open across threads.
- Memory introspection is not behind that gate at all: it is raw `extern fn rt_*`
  declarations, usable from any file (P11). 76 files under `test/` use them, 63 of those
  the transient-scope calls ‡.
- The counters are engine-specific: real on the JIT, zero on the interpreter, blind to
  structs (P2, P12).

More facts, from the Opus critic and checked by Fable where marked:

- The gate is not a fence. Same-directory callers and baselined pairs are exempt
  (`module_loader.rs:3038`, `:3041` ‡). Any `/test/` path component counts, and `src/`
  has such directories, for example `src/app/test/` (checked) and
  `src/lib/nogc_sync_mut/debug/remote/test/` ‡. The owner rule says not to narrow this.
- The self-hosted gate skips `extern` functions and only warns unless
  `SIMPLE_STRICT_PRIVATE_IMPORTS=1`
  (`src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl:801-810`,
  checked).
- The lanes are disjoint: the call gate is enforced on the interpreter, where the
  counters read zero; the counters are real on the JIT, where the gate is not enforced.

Consequences for a model:

- Tests need more than product code may have: a forced scope reset between examples, a
  quarantine switch that turns a use-after-release into an abort, and (once they exist)
  owner and share counts.
- Read-only totals are a different thing. Product code already needs them for
  reporting (P11), so they should be a public API, not a private one.
- A path-based visibility rule cannot protect the mutating controls: it is not enforced
  on the JIT lane or across threads, and it admits files under `src/**/test/`. The
  private-access rule stays as it is for calling private functions. The controls need a
  second key that the runtime itself checks.
- Every engine must answer the same questions. An engine that cannot answer must say
  "unsupported", never zero.

The design that follows is in the plan, section 5.

## 9. Fable and Opus: reconciliation

Two Opus agents worked independently of each other: a critic that re-read the code
against the Fable draft, and a language-design analyst that was given the facts and asked
for an option analysis. Neither executed anything. Outcomes:

| # | Fable draft | Opus | Decided by | Result |
|---|---|---|---|---|
| 1 | No separate JIT memory model | Critic: true for values; a code-memory model (owner, generation, unmap, remote mapper) is needed and missing | `doc/glossary.md:260-266`; `object_mapper.spl:39`; `memory_alloc.spl:19-39`; notebook session lifetime | **Opus right.** Sections 1, 4, 6 changed; the plan has a code-memory track |
| 2 | Regions are a coarse optimisation, not the correctness mechanism | Analyst: for graph data (AST, HIR, MIR) regions are the owner, and two filed bugs show they need a checked contract | Plan section 4.2 of the no-GC plan; P9 | **Opus right** on status. Fable's point survives in part: a region cannot be the only mechanism, because a long loop inside one region still grows |
| 3 | Value kinds are single-owner, so static release is sound once alias sites are fixed | Analyst: false for immutable kinds. Text is shared by handle (interned literals are refused by `rt_string_free`); closures likewise | Read by the analyst (`rs/runtime/src/value/collections.rs:8909-8916` ‡) | **Opus right.** The contract gets an immutable-shared category. Single ownership holds for mutable buffers: array, dict, struct, tuple |
| 4 | Classes: undecided, owner decision | Analyst: decide now as counted, thread-confined shared references; the keyword `class` is the explicit opt-in to sharing | Ruling of 2026-11-04 settles identity; nothing settles ownership | **Partly reconciled.** Both now recommend counted classes on the self-hosted native lane and leak-or-region on the seed. It stays an owner decision because it reads against "no implicit RC" in the no-GC plan |
| 5 | Parameter writes: owner decision; documents say error without `mut` | Analyst: adopt Rule 4 for all kinds with a behaviour-preserving autofix. Critic: JTAG host code depends on array out-parameters | `state_capture.spl:56`; analyst's grep: 285 signatures with a `mut` parameter against 16,403 with an array parameter (upper bounds) | **Agreed:** Rule 4 with autofix (`mut` added where a callee writes an array or dict parameter; a local copy where it writes a struct parameter). Size of the migration is unmeasured. Owner decision |
| 6 | Introspection as private functions behind the test-path gate | Both Opus agents: not workable. Critic: public read-only stats, provider allowlist for raw externs, runner-granted capability for controls | Section 8 facts | **Opus right.** Plan section 5 uses the critic's design |
| 7 | S1: verdict pending | Analyst read the S1 commits: sound today and after alias fixes because it releases only fresh, never-shared buffers; land with conditions | S1 worktree commits `4e69c9a7521`, `59bca88628b` (quarantine mode present, checked by Fable) | **Agreed:** land with conditions (plan section 7) |
| 8 | "No C codegen found"; MCP/LSP interpreter-only; 18 files with manual frees; remote lane reclaims per run | Critic: each wrong or incomplete | Checked by Fable: `c_codegen.spl` exists; 13 files; notebook session comment | **Opus right.** Corrected in sections 2, 3, 4, 7 |
| 9 | Ordering not stated | Analyst: tools, then proven-unique release, then alias fixes by move, then each copy fix paired with its release | Design doc section 2.5 (copies without release took one workload from 280 MB to 2.0 GB) | **Adopted** as the plan's stage order |

Still open between the two models:

- The critic suspects existing code was written for copy-on-extract classes (a comment
  in `src/lib/nogc_sync_mut/notebook/remote_exec.spl:170-174` ‡ predates the 2026-11-04
  default). Neither side measured how much code depends on either behaviour.
- The analyst would narrow `is_test_caller`; the owner rule says not to. The plan does
  not narrow it and adds a runtime-checked capability instead.

Not verified by anyone: reachability of the bytecode VM, Lua, IrTc and `MirInterpreter`
from `run`; whether native binaries resolve `rt_heap_live_count_by_kind`; the cause of
the caret RSS; class-cycle leaks on the seed interpreter.

## Appendix: probes

`alias.spl` (section 2.2, P3-P5; one block per row):

```simple
struct Holder:
    xs: [i64]
    n: i64

var g_slot: [i64] = [0]

fn ident(x: [i64]) -> [i64]:
    x

fn mut_param(x: [i64]):
    x[0] = 9

fn main():
    val a5 = [1, 2, 3]
    var b5 = ident(a5)
    b5[0] = 9
    print "A5 ident a={a5[0]} b={b5[0]}"       # interpreter 1 / 9, JIT 9 / 9
    var d1 = {"k": 1}
    var d2 = d1
    d2["k"] = 9
    print "D1 dict d1={d1["k"]} d2={d2["k"]}"  # interpreter 1 / 9, JIT 9 / 9

main()
```

Printed values, interpreter then JIT: A1 `1/9`, `1/9`; A3 `9`, `9`; A5 `1/9`, `9/9`;
A6 `9/1`, `9/9`; A8 `9/1`, `9/9`; A9 `9/1`, `9/9`; A10 `1/9`, `9/9`; struct let `1/9`
both; struct param `1` both; class let `9/9` both; class param `9` both; text `ab/abc`
both; dict `1/9`, `9/9`.

`cnt.spl` (P1, P2): three loops of 1,000 iterations (`val a = [i, i+1, i+2]`,
`val d = {"k": i}`, `val p = Plain(a: i, b: i)`) bracketed by `rt_heap_alloc_count`,
`rt_heap_free_count` and `rt_heap_live_count_by_kind`. JIT: `arr allocs=1000
live_delta=1000; dict live_delta=1000; struct allocs=0; frees=0`. Interpreter: all zero.

`ptr.spl` (P6): `new* Node(v: 1)`, `new& Node(v: 2)`, `move`, then `val c = u2` on a
`&Node` followed by a read of both names (accepted), then `weak_of(s1)` (semantic error:
function not found).

`dropd2.spl` (P7): a class `Res` with `impl Drop for Res: fn drop(): print("drop {self.id}")`,
a function that binds `val r = Res(id: 1)` and has a `defer:` block. Both lanes print
`in scope`, `defer ran`, `after scope`; `drop 1` is never printed.
