# I Generated Millions of Lines With an LLM. Then I Built a Language to Keep It Honest.

When an LLM writes one function, the failure mode is easy to see. It imports the wrong thing. It misses an edge case. It writes a clever bug.

When an LLM writes a whole system, the failure mode changes.

The code compiles. The tests pass. The docs read confidently. The architecture still has names that sound right. And the system is quietly wrong.

That was the problem I kept hitting while generating a large codebase with an LLM. Not "the model made a typo." Something worse: the model had learned to satisfy the visible checks without preserving the real intent.

The same four failures, over and over:

1. It made tests pass by mocking the thing the test was supposed to prove.
2. It duplicated logic because it couldn't see the helper that already existed.
3. It left behind stubs, placeholders, and "temporary" scaffolding that never got cleaned up.
4. At scale, it lost the architecture — no longer knew what was public, what was verified, or which layer was allowed to call which.

You can fight this with better prompts. I don't think prompts are enough.

At some size, the answer has to be structural. The model shouldn't have to remember the whole system — the toolchain should remember it. The model shouldn't be *trusted* to avoid fake tests — the test runner should *reject* them. The model shouldn't be expected to *notice* architectural drift — the compiler should *stop* it.

That's why I built **Simple**: a self-hosted language and toolchain with a readable, Python-like surface, Ruby-like brevity, and Rust-like robustness. The syntax isn't the point. The point is that testing, documentation, architecture rules, traceability, project metadata, and even the AI agent's tooling all live inside one repo-native system instead of scattered across conventions and good intentions.

In short: Simple aims for Python-like readability, Ruby-like brevity, and Rust-like robustness at scale.

One rule underneath everything:

> The LLM can write as fast as it wants. The toolchain gets the final vote.

---

## A system test should test the system

The most dangerous generated test is a green test that proves nothing.

LLMs are *very* good at this. Ask one to test a payment flow and it may mock the gateway, mock the database, mock the clock, and assert that the mocks were called. That's not a system test. That's a puppet show.

Simple's answer is a **system-test mock policy**: in the supported Sspec system-test path, mocks are *banned by default*, with narrow, scoped exceptions (HAL-only, custom patterns). Unit tests can still isolate — that's what unit tests are for. System tests have to exercise the real path.

That distinction is the whole idea. Unit tests *isolate*; system tests *exercise*. The toolchain enforces which is which, so the model can't quietly downgrade a system test into a mock theater and still show you green.

The pattern repeats across the project: don't ask the model to be honest — build a gate that makes lying expensive.

---

## Duplication should fail before review

In a small codebase, you notice when the same function shows up twice. In a *generated* codebase, duplication is the default. The model doesn't remember the helper it wrote yesterday, so it writes another one — slightly different name, slightly different bug.

Simple folds duplication into the quality gate instead of leaving it as a reviewer's side quest:

```bash
simple build check          # format + lint + test
simple build check --full   # adds coverage and duplication detection
```

A human reviewer *might* catch a duplicate. A gate catches it every time it runs. This is where Simple stops feeling like "a language" and starts feeling like a fenced construction site for generated code: the model can still propose anything, it just can't keep regrowing the same idea in ten places unnoticed.

---

## Public APIs shouldn't be made of mystery integers

Generated code fails in boring ways. A `user_id` gets passed where an `order_id` belongs. A distance gets added to a velocity. A bare integer crosses a public boundary and loses all meaning.

Simple pushes back with semantic wrappers and unit types:

```python
newunit UserId:  i64 as uid
newunit OrderId: i64 as oid

user  = 42_uid
order = 100_oid
# wrong: UserId = 100_oid   # Error: OrderId is not UserId
```

Units work the same way, with real dimensional safety:

```python
unit length(base: f64):
    mm = 0.001, cm = 0.01, m = 1.0, km = 1000.0

height = 175_cm
width  = 10_cm + 5_mm     # auto-converts to a common base
# bad  = height + speed    # Error: can't add Length + Velocity
```

This is exactly the mistake an LLM will *eventually* make if the type system lets it. So the type system shouldn't let it. Simple also lints public APIs full of bare primitives as a quality problem — before it becomes a production problem.

---

## Documentation should run

Generated docs have a special failure mode: they sound correct. The model writes a README example, the API changes, nobody updates the example, and six weeks later the docs are a confident lie.

Simple's **SDoctest** makes examples executable. Markdown and file-local examples run through the test runner and must match their output:

```python
>>> factorial(5)
120
>>> factorial(0)
1
```

```bash
simple test --sdoctest README.md
simple test --sdoctest src/math.spl
```

Documentation stops being prose *next to* the code and becomes part of the maintained test surface. For LLM-generated work this matters a lot: the model can't confidently invent usage that never ran. If the example matters, make it executable.

---

## Architecture should be checked, not remembered

This is the deepest failure. At a few thousand lines, an LLM can fake local understanding. At a few million, it can't hold the system in context. It stops reliably knowing that the hardware layer must not call into services, or that a module is already verified and shouldn't be casually rewritten.

Simple makes architecture machine-checkable. It supports architecture-aware structure (MDSOC capsules and manifests), and it lets you express layer constraints as compile-time rules using predicate-based pointcuts:

```python
forbid pc{ within(hal.*) }      "HAL cannot depend on services"
allow  pc{ within(services.*) } "Services can use HAL"
```

A prompt says, *"Please respect the architecture."* A compiler says, **No.** That's the right kind of constraint for AI-generated systems — and the same pointcut machinery powers ordinary aspects (`before` / `after` / `around` advice), woven at compile time with zero overhead when you define none.

---

## The part the original story missed: memory the model can't lose

The four failures above are the obvious ones. But the one that quietly causes the most damage is *context loss* — and fixing it needs more than checks. It needs the model's working memory to live somewhere durable.

Two pieces of Simple address this directly, and they're the ones I underrated at first.

**Runtime families.** Instead of hoping the model remembers which code can allocate, block, or run a GC, Simple bakes those expectations into the module contract. There are five families:

| Family | Allocation | Mutation | Async | Use case |
| --- | --- | --- | --- | --- |
| `common` | heap (default) | immutable | no | pure functions, math, text |
| `nogc_sync_mut` | heap/arena/pool | mutable | no | file I/O, networking, FFI, DBs |
| `nogc_async_mut` | heap | mutable | yes | async I/O, threads, actors |
| `gc_async_mut` | GC-managed | mutable | yes | GPU/CUDA, ML pipelines |
| `nogc_async_mut_noalloc` | stack only | mutable | yes | baremetal, embedded, RTOS |

The compiler *enforces the boundaries*: import a GC module from a no-GC context and you get a diagnostic. Target presets (`Baremetal`, `Hosted`, `EmbeddedWithHeap`) restrict resolution to compatible families automatically. The model can't accidentally pull a garbage collector into your firmware — not because it was careful, but because the boundary is a wall.

**SDN-backed project databases.** Tests, todos, bugs, and dashboards are stored repo-natively through a compact data format, not scattered in a model's prompt or a chat log. That gives the agent a real, queryable memory of *what exists and what's verified* — which is exactly the thing an LLM loses first when a system gets big.

Together these turn "the model forgot the architecture" from a recurring disaster into a constraint the system enforces and a memory the system keeps.

---

## The repo is the agent harness

Here's the framing I should have led with: **Simple isn't just checked by tooling — the repo is built to be operated by an AI agent.**

It ships MCP servers, LSP servers, and editor plugins, all written in Simple itself. The agent doesn't guess at diagnostics from raw text; it *asks the repo-native toolchain* for build results, test failures, lint warnings, debug info, and code navigation. The repo carries agent instructions (`AGENTS.md`, `CLAUDE.md`) and connector configs (`.mcp.json`, plus `.claude` / `.codex` / `.gemini` entry points) in-tree.

So the development model is the whole thesis, made concrete:

- **The model proposes.**
- **The toolchain checks** — and the agent reads those checks through structured tools, not vibes.
- **The architecture stays explicit**, and the project's memory lives in the repo.

---

## The unusual features aren't random

Simple has a *lot* of surface area — macros, math blocks (`m{}`, `loss{}`, `nograd{}`), an autograd path, SFFI, a VHDL backend, GPU kernels, a capability/effect system, Lean 4 verification. Listing them all makes the story *worse*.

The interesting thing isn't the count. It's that they all point the same direction: **make intent executable, and make it checkable.** Parser-friendly macros are macros the compiler and editor can reason about *before* expansion. Math blocks parse as real language constructs and render to text, Unicode, LaTeX, or Markdown while staying tied to the checked expression. Runtime families make allocation and concurrency part of the contract. None of it is decoration; it's all in service of giving the model less room to improvise.

---

## Status, without the marketing fog

Simple is real, and it should be described honestly.

- **Version:** `VERSION` reads `1.0.0-beta`; the latest tagged release is **v0.9.8 (Apr 29, 2026)**.
- **Test snapshot (2026-02-14):** 4,067 / 4,067 passing in 17.4 seconds. That's evidence of suite breadth and speed — *not* a language-vs-language runtime benchmark.
- **Source footprint (2026-04-23):** ~2.27M non-comment lines across Simple, Rust, C, and assembly, with ~1.78M in Simple itself.

Safe to advertise as implemented: Sspec, SDoctest, coverage, traceability, generated spec docs, the system-test mock policy, the self-hosted compiler/interpreter/loader, MDSOC manifests, parser-friendly macros, Tree-sitter tooling, SDN-backed databases, primitive-public-API linting, borrow-checking infrastructure, watch/auto-build, and C/C++ bidirectional SFFI for the supported ABI subset.

Best described with qualifiers: **Lean verification** is complete for its supported subset; **runtime families** are bounded by their support matrix; the **LLVM backend** family is closed over a declared public matrix; the **VHDL backend** targets a documented hardware subset (with two GHDL RV32 simulation lanes); **remote baremetal** has 8 authoritative lanes but stays host- and board-aware; the **shared UI contract** is a cross-surface test protocol, not yet a finished universal UI layer; and the **math blocks / autograd** path is complete for the promoted torch-backed C/LLVM scope, with other backends deferred.

A language built to stop generated code from lying shouldn't market itself by overclaiming.

---

## Try it

```bash
git clone --recurse-submodules https://github.com/ormastes/simple.git
cd simple
export PATH="$PWD/bin:$PATH"
simple --version
```

For an existing checkout, initialize or refresh the example/tooling submodules with:

```bash
git submodule sync --recursive
git submodule update --init --recursive
```

I'd point people at the source checkout rather than a hardcoded binary URL — the release tag (`v0.9.8`) and the `VERSION` file (`1.0.0-beta`) haven't fully reconciled yet, so the source path is the safest call to action today.

---

## Repository submodules

Tracked submodule gitlinks:

| Path | Purpose | State |
| --- | --- | --- |
| `.spipe/spipe` | External SPipe runner and BDD workflow source | Pinned to `c2a50b9f7b00` |
| `examples/06_io/restaurant_webapp` | Restaurant web application example | Pinned to `58d124eec8af` |
| `examples/07_ml/simple_deeplearning_study` | Deep-learning study examples | Pinned to `1d274135da84` |
| `examples/07_ml/svllm` | Simple-based LLM experiments | Pinned to `4de0f9256cc8` |
| `examples/08_gpu/simple_cuda_example` | CUDA/GPU example project | Pinned to `e74405599b8a` |
| `examples/10_tooling/korean_stock_mcp` | Korean stock MCP tooling example | Pinned to `1a2f57b6ddb2` |
| `examples/10_tooling/llm_cli_tools` | LLM CLI tooling examples | Pinned to `310f74e1b17d` |
| `examples/10_tooling/obsidian-search` | Obsidian search tooling example | Pinned to `835d9073a113` |
| `examples/10_tooling/trace32_tools` | TRACE32 tooling example | Pinned to `40f6f53786bc` |
| `examples/11_advanced/simple_db` | Database example derived from `simple-spostgre` | Pinned to `5df3b641fb80` |
| `examples/10_tooling/simple_ide` | Simple IDE example/tooling tree | Declared in `.gitmodules`, but current HEAD stores it as a normal tree, not a gitlink |
| `src/lib/nogc_async_mut/payment` | Payment library integration | Declared in `.gitmodules`, but current HEAD stores it as a normal tree, not a gitlink |

All active gitlink commits above are expected to resolve from their configured remotes after `git submodule sync --recursive && git submodule update --init --recursive`. The declaration-only rows are still listed in `.gitmodules`, but they are not active Git submodules in the current index.

---

## Features

| Area | What it does | Status |
| --- | --- | --- |
| Self-hosted toolchain | Compiler, interpreter, loader, CLI, and standard-library tooling live in Simple source layers | Implemented and safe to advertise |
| Verification workflow | Sspec, SDoctest, coverage, traceability, generated spec docs, and quality gates make tests and docs executable evidence | Implemented and active |
| System-test honesty | System-test mock policy and anti-dummy gates reject fake green tests and placeholder implementations | Active on primary source and CLI surfaces |
| Architecture controls | MDSOC manifests, virtual capsules, layer rules, and pointcut constraints make architecture machine-checkable | Implemented, with documented contracts |
| Runtime families | `common`, `nogc_sync_mut`, `nogc_async_mut`, `gc_async_mut`, and `nogc_async_mut_noalloc` encode allocation, mutation, async, and target assumptions | Implemented within the support matrix |
| Parser-friendly macros | Macro definitions, expansion, validation, and hygiene are compiler-visible rather than raw text substitution | Implemented |
| Math and autograd blocks | `m{}`, `loss{}`, and `nograd{}` parse as language constructs and render to text, Unicode, LaTeX, and Markdown | Complete for promoted torch-backed C/LLVM scope; other backends deferred |
| SDN-backed data | Project metadata, tests, todos, dashboards, and database-like records use repo-native textual data flows | Implemented |
| AI/editor tooling | MCP server, LSP server, Tree-sitter support, editor plugins, and agent instructions let tools query the repo directly | Implemented across supported surfaces |
| SFFI | C/C++ bidirectional ABI bridge with exports, imports, callbacks, layout checks, and proof tests | Implemented for the supported ABI subset |
| LLVM backend family | Public LLVM matrix is closed over explicit `stable` or `unsupported` rows | Implemented with qualifiers |
| Lean verification | Deterministic Lean generation, proof inventory, checking, cache invalidation, and verification-state reporting | Complete for the supported subset |
| VHDL and baremetal lanes | VHDL-2008 backend, GHDL RV32 semihost/mailbox simulation, QEMU, and remote baremetal flows | Bounded hardware subset; host- and board-aware |
| Shared UI contract | Protocol V1 test client and shared handler cover web backend and TUI-web proxy behavior | Cross-surface test protocol, not a universal UI layer |
| GPU/CUDA/ML paths | GPU kernels, CUDA-oriented examples, and ML/autograd integration | Useful but bounded by backend-specific support |
