# I generated millions of lines of code with an LLM. Then I built a language so it would stop lying to me.

When you let an LLM write code at scale -- not a function, not a file, but a whole system, millions of lines -- you stop hitting the bugs you expect and start hitting a different class of problem. The code compiles. The tests pass. And it's still wrong, in ways that are quietly corrosive and hard to see until they've spread.

I kept hitting the same four failures over and over:

1. The model writes a **mock** so a system test goes green without the real thing working.
2. It **duplicates** logic that already exists three folders away, because it couldn't see it.
3. The codebase drifts toward **complexity** -- placeholder stubs, dead scaffolding, verbose boilerplate that does nothing but grow.
4. At a few million lines, the model **loses the thread**. It can no longer tell what's public, what depends on what, or what's already been verified -- so it can't safely keep going.

Simple is a programming language and toolchain built around the premise that these four failures should be *structurally impossible* -- caught by the compiler, the linter, or the test runner, not by a human reviewer who is, frankly, not going to read all of it.

This is the argument for the language. The Ruby-like syntax, the GPU backends, the baremetal support -- that all matters, and I'll get to it. But the reason Simple exists is the four failures above.

> **A note on honesty:** Simple is a real, self-hosted toolchain -- the compiler, standard library, and tools are written in Simple itself. The README's published full-suite snapshot from 2026-02-14 reports 4,067/4,067 passing in 17.4 seconds. But some features below are complete within a bounded scope and others are designed-and-partial. I mark which is which. The repo's own README separates "safe to advertise" from "best described with qualifiers," and I follow that.

---

## Failure 1: The test that lies

The most dangerous thing an LLM does in a large codebase is make a test pass by faking the thing under test. You ask for a system test of a payment flow; you get a test that mocks the payment gateway, the database, and the clock, and asserts that the mocks were called. It's green. It proves nothing.

Simple's answer is a **system-test mock ban**, enforced by the toolchain. At the system-test level, mocks are not allowed -- the test has to exercise the real path. The policy ships in three modes: a full ban, a HAL-only mode (you may mock the hardware abstraction layer but nothing above it), and a custom-pattern mode for teams that need a controlled exception list.

The point is that "mock it until it's green" is no longer a move the model can make. If the only way to pass a system test is to run the real code, then a passing system test means the real code ran.

```simple
# A system test exercises the real path -- no mocked collaborators.
# Lower test levels may mock; system level may not.
simple test --level system
```

This pairs with a second guard the repo calls **anti-dummy / anti-stub enforcement**: a lint/verify gate that rejects placeholder implementations and empty stubs left behind as scaffolding. An LLM loves to write `# TODO: implement` behind a function that returns a plausible constant. That doesn't survive `simple lint` / `simple verify quality`.

---

## Failure 2: The duplication you never see

In a small codebase you notice when something gets written twice. In a million-line codebase generated in thousands of separate model calls, duplication is the *default outcome* -- the model has no memory of the helper it wrote yesterday, so it writes it again, slightly differently, with a slightly different bug.

Simple folds duplication detection into the standard quality gate rather than leaving it to a separate tool nobody runs:

```sh
# Format + lint + test
simple build check

# Adds coverage *and* duplication detection
simple build check --full
```

Making duplication a build-check failure rather than a code-review observation changes who catches it: the toolchain, every time, instead of a human, sometimes.

---

## Failure 3: Complexity creep

Two forces in Simple push back on the slow inflation of generated code.

The first is the **surface syntax**, which is deliberately Ruby-like: simple defaults, used everywhere they don't hurt readability. Variables are immutable by default and you opt into mutation with `var`. Types are inferred. String interpolation is on by default. Functions return their last expression. Lambdas are `\x: ...`. The less ceremony per line, the less room for the model to pad.

```simple
x = 10                      # immutable by default
var y = 20                  # opt into mutation
name = "world"
msg = "Hello, {name}!"      # interpolation, no extra syntax

fn add(a: i64, b: i64) -> i64:
    a + b                   # implicit return

double = \x: x * 2
evens  = [1,2,3,4].filter(\x: x % 2 == 0)
```

The second is the type system's insistence that **primitive types not leak across public interfaces**. A public function that takes a bare `i64` for a user id and another bare `i64` for an order id is an invitation to pass the wrong one -- and an LLM will eventually pass the wrong one. Simple lints primitive types on public APIs and gives you cheap, composable custom types instead:

```simple
unit length(base: f64):
    mm = 0.001, cm = 0.01, m = 1.0, km = 1000.0

unit velocity(base: f64) = length / time:
    mps = 1.0, kmph = 0.2777777777777778

newunit UserId:  i64 as uid
newunit OrderId: i64 as oid

height   = 175_cm
speed    = 200_kmph
distance = 42_km

# bad = height + speed     # compile error: Length + Velocity
travel_time = distance / speed   # returns a Time

user  = 42_uid
order = 100_oid
# UserId = 100_oid          # compile error: OrderId != UserId
```

Two failure classes -- unit mix-ups and id mix-ups -- become compile errors instead of production incidents. The model can't talk its way past a type error.

---

## Robust by construction: no null, and every case handled

The single most common way generated code fails in production isn't a logic error -- it's the absent value nobody handled and the case nobody knew existed. So Simple removes both at the language level.

**There is no null.** Absence is modeled with an explicit optional type, and you cannot use the inner value without first dealing with the empty case. A function that might not return a value says so in its type, and every caller is forced by the compiler to handle the empty branch. The billion-dollar mistake isn't discouraged -- it's unrepresentable. This matters doubly for generated code: an LLM trained on null-bearing languages will happily write code that dereferences a maybe-absent value, and in Simple that simply doesn't compile.

**Pattern matches are exhaustive -- and in high-robustness mode, everywhere.** A `match` must cover every variant of the type it inspects; a missing case is a compile error, not a silent fall-through. The high-robustness mode tightens this further: it turns the partial-handling escape hatches into errors too, so across the whole program every case of every matched type must be explicitly addressed. You dial the strictness up for the parts of the system that must not surprise you.

```simple
fn describe(x: Shape) -> str:
    match x:
        Circle(r):    "circle r={r}"
        Square(s):    "square s={s}"
        # In high-robustness mode, omitting Triangle is a compile error,
        # and so is a catch-all `_` that hides an unhandled variant.
```

The combination is the point. No-null means the *absent* case can't be ignored; exhaustive match means the *unexpected* case can't be ignored; high-robustness mode means neither can be ignored anywhere you've asked the compiler to insist. For a codebase being extended by a model that doesn't know what it doesn't know, "the compiler enumerates the cases you forgot" is worth more than any amount of review.

*(Note for accuracy: I've described no-null and exhaustive matching as the language's design intent and named a high-robustness mode. Confirm the exact keyword/flag name and the optional-type syntax against the current compiler before publishing -- I've kept the snippet schematic rather than asserting specific surface syntax I haven't verified.)*

---

## Failure 4: Losing the thread at scale

This is the deepest one. Past a certain size, an LLM simply cannot hold the system in context. It can't see the whole dependency graph, so it doesn't know that the `hal` layer must never call up into `services`, or that a module is already formally verified and shouldn't be rewritten. It improvises, and the architecture erodes.

Simple's response is to make the architecture **machine-checkable and bounded**, so the model never needs to hold the whole thing in its head.

**Minimal public surface.** Only explicitly exported symbols can be referenced across boundaries -- there is no `*` export. The public surface stays small and enumerable, which is exactly the surface the model has to reason about.

**Architecture rules as compile-time constraints.** Layer dependencies are declared and enforced when you build, using predicate-based pointcuts:

```simple
# Enforced at compile time, not in code review
forbid pc{ within(hal.*) }      "HAL cannot depend on services"
allow  pc{ within(services.*) } "Services can use HAL"
```

If the model writes a call that violates the layering, it doesn't merge -- it doesn't compile.

**MDSOC architecture support.** Virtual capsules, manifests, and an architecture-aware repository structure are first-class concepts, not conventions. The structure that tells the model "here is your boundary, here is what you may touch" is written down in a form the toolchain checks.

Together these keep the *context required to safely extend the system* small and verifiable -- which is the precondition for an LLM being able to "go next" without drift.

---

## And the verification layer underneath

Mistake-prevention runs deeper than linting. Simple integrates a **Lean 4 formal verification layer** -- deterministic Lean generation, proof-artifact inventory, Lean/Lake checking, cache invalidation, and verification-state reporting -- for the supported verification subset. Where you've verified something, the toolchain knows it's verified, which is the other half of "don't let the model rewrite proven code."

Memory safety has its own structural guards: **borrow checking** plus a set of **runtime families** the compiler keeps separate.

| Family | Allocation | Mutation | Async | Use case |
| --- | --- | --- | --- | --- |
| `common` | heap (default) | immutable | no | Pure functions, math, text |
| `nogc_sync_mut` | heap/arena/pool | mutable | no | File I/O, networking, FFI |
| `nogc_async_mut` | heap | mutable | yes | Async I/O, threads, actors |
| `gc_async_mut` | GC-managed | mutable | yes | GPU/CUDA, ML pipelines |
| `nogc_async_mut_noalloc` | stack only | mutable | yes | Baremetal, embedded, RTOS |

Importing a GC module into a no-GC context produces a diagnostic, and target presets (`Baremetal`, `Hosted`, `EmbeddedWithHeap`) automatically restrict module resolution to compatible families. You choose GC or no-GC per context, and the compiler stops you from accidentally mixing them.

Pointers are not one thing, either. Simple has **five pointer types** -- GC, unique, shared, weak, and **handle** -- so "a reference to something" carries its ownership and lifetime story in the type rather than leaving it implicit. The first four are the familiar managed/owned/shared/non-owning quartet. The fifth is the one that matters for baremetal.

A **handle** is an *index-as-pointer*: instead of holding a raw machine address, it holds an index into a table, pool, or arena that owns the actual storage. This is the classic embedded and high-reliability pattern, and it's a good fit for exactly the places a raw pointer is dangerous:

- **No raw addresses to corrupt.** On a target with no MMU, a stray raw pointer write can scribble anywhere; a handle is just an index that gets *resolved* through its pool, and the resolution can be bounds-checked.
- **It can't dangle into arbitrary memory.** A handle to a freed or not-yet-ready slot resolves to "absent," not to whatever now occupies that address -- which composes directly with the no-null/optional discipline from earlier.
- **It's relocatable and serializable.** Because it's a value-index rather than an address, the pool can move, snapshot, or restore its backing store without invalidating outstanding handles -- useful for arenas, save/restore, and the stack-only `nogc_async_mut_noalloc` baremetal family above.

The handle composes with the runtime families rather than competing with them: the family decides *where* storage lives (stack-only, arena, pool), and the handle is the bounds-checkable way to *refer* to it without a raw address. For LLM-scale code this is another bug class converted into a checkable lookup -- a raw pointer is one more thing a model gets subtly wrong at a million lines, and an index-handle the runtime can validate turns "memory corruption" into "this handle didn't resolve."

*(Accuracy note, consistent with the rest: I'm reading `handle` in the five-pointer list as this index/table-handle concept and describing its baremetal rationale. Confirm the exact semantics and the handle syntax against the current compiler before publishing -- I've kept this conceptual rather than asserting a specific surface form.)*

And the **macros are parser-friendly**: definition, expansion, validation, and hygiene are compiler features, not editor-hostile text substitution. Because macros are contract-first, tooling knows what a macro introduces *before* it expands -- which means the model (and your IDE) can reason about generated symbols instead of guessing.

---

## Living documentation, so the docs can't rot either

The same anti-drift instinct applies to documentation. The usual failure is that prose and code rot apart: the README shows an example, the API changes, nobody updates the README, and now the documentation is a lie. An LLM makes this worse -- it writes confident example code that never ran. **SDoctest** closes the gap by making the documentation itself executable. Two surfaces, one runner.

**Code embedded in Markdown.** Fenced examples in your `.md` files are extracted and run by the test runner; the printed result must match what the doc claims, or the build fails.

```simple
>>> factorial(5)
120
>>> factorial(0)
1
```

```sh
simple test --sdoctest README.md
```

If `factorial` changes so that `factorial(5)` no longer yields `120`, that README block fails like any other test. The sample code in your documentation is *alive* -- it can't drift from the implementation, because the moment it does, CI goes red.

**Code embedded in comments.** The same mechanism runs example code written inside source-level comments and docstrings. The usage example you put next to a function -- the one that normally goes stale the first time you touch the function -- is executed and checked against its stated output:

```simple
fn factorial(n: i64) -> i64:
    """
    Computes n!.

    >>> factorial(4)
    24
    >>> factorial(1)
    1
    """
    if n <= 1: 1 else: n * factorial(n - 1)
```

```sh
simple test --sdoctest src/math.spl   # run file-local doctest examples
simple test --sdoctest --tag slow      # filter doctests by tag
```

So both kinds of "documentation code" -- the prose-level examples in Markdown and the inline examples in comments -- are first-class tests. (`--doctest` is accepted as a compatibility alias, but `--sdoctest` is the name for the implemented path.) For a codebase an LLM is extending, this is one more case of turning a thing humans forget to check into a thing the toolchain checks every time: every example the model writes either runs and matches, or it isn't allowed in.

And feature documentation is **auto-generated from BDD specs** -- each spec carries feature metadata and executable assertions, so the docs describe what the tests actually verify. Documentation that lies is its own kind of LLM failure mode; this closes it.

---

## The development model: toolchain as reviewer

Everything above describes guards that *reject* bad generated code. The flip side is the feedback loop that makes writing a lot of code tractable in the first place -- so an LLM has a paved road to walk instead of an open field to wander.

The toolchain is meant to be driven, not just invoked. The MCP server exposes repo-native diagnostics, build, test, and version-control operations, and the LSP gives completions, hover, and go-to-definition. An LLM driving the toolchain through MCP gets the same machine-checked feedback a careful human would -- a lint here, a failing assertion there, a layer violation over there -- which is what lets it keep producing correct code without a person reviewing every line. The model proposes; the lint, the type checker, the mock ban, the duplication gate, and the architecture rules dispose.

That's the development model Simple is really proposing: **the toolchain is the reviewer, and the LLM is a fast producer inside a fence it can't climb over.**

> *I've deliberately not described the BDD spec framework's surface syntax here, because I want the article to show only syntax I can verify against the current compiler. If you want a spec example in this section, paste a real one from the repo and I'll drop it in.*

There are a few practical pieces that matter here because they make the feedback loop usable rather than merely strict. Simple has Tree-sitter outline/query tooling, LSP/MCP entrypoints, watch mode, and auto-build support, so "ask the toolchain what changed and what broke" is a normal workflow instead of a manual audit. The loader side is real too: mmap-backed loader support and executable-memory plumbing are part of the advertised surface, which matters for dynamic execution and embedding.

The project metadata story is also part of the anti-drift design. Simple Data Notation (SDN) backs project, test, todo, dashboard, and other textual databases in the repo. That means the state an agent needs -- requirements, tests, todos, traces, dashboards -- is stored in repo-native structured text rather than scattered across prose, ad hoc JSON, and memory.

---

## Custom blocks: math, deep learning, and rendered arithmetic

Simple has first-class **custom syntax blocks** for math and machine learning -- `m{}`, `loss{}`, and `nograd{}` -- that are parsed and evaluated as real language constructs, not strings handed to a library. You write the math the way you'd write it on paper, and the compiler understands it.

```simple
# A math block -- parsed, type-checked, evaluated
y = m{ a * x + b }

# A loss block participates in autograd
l = loss{ mean((y_pred - y_true) ** 2) }

# nograd{} suspends gradient tracking, then restores it
nograd{
    eval_metric(model, validation_set)
}
```

The part that's genuinely unusual is **rendering**: a math block has five rendering backends -- plain text, a debug form, Unicode, LaTeX, and Markdown. The same expression can show up as `α` in your terminal via the Neovim conceal preview, as LaTeX in generated documentation, and as ordinary source when you're editing. The editors lean on this: VSCode highlights and previews math blocks with nested-brace support, and Neovim renders inline Unicode (`frac(1,2)` -> `(1)/(2)`, `alpha` -> `α`, `sqrt(x)` -> `√(x)`). So the arithmetic you read is a *rendering* of the expression the compiler actually checks -- the notation and the semantics can't drift apart.

For deep learning specifically, the autograd path through `m{}` / `loss{}` / `nograd{}` is complete for the promoted torch-backed C/LLVM scope, including backward passes, detached-input failure handling, and `nograd{}` restore semantics. (Other backends for these blocks are deferred -- this is one of the bounded-scope features, not a universal claim.) The repo ships working DL examples on top of this: a pure-Simple XOR net, linear regression, iris classification, and progressive LoRA fine-tuning.

---

## From class templates to Lean proofs, automatically

Simple includes a **Lean 4 formal verification layer**, and the workflow is meant to be low-ceremony: the toolchain extracts proof obligations from your code and generates the Lean to discharge them, rather than asking you to hand-write Lean alongside every type.

The intended path is that a generic type or class -- its type parameters, its declared invariants, its method contracts -- is the source from which verification conditions are derived. The toolchain runs **deterministic Lean generation** over that, maintains a **proof-artifact inventory**, checks the proofs with **Lean/Lake**, invalidates the cache when the source changes, and reports verification state back to you. Because generation is deterministic, the same source always produces the same Lean, so a proof that passed yesterday isn't silently re-derived into something different today.

This closes the loop with the "don't let the LLM rewrite proven code" guard from earlier: a verified template carries its verification state in the inventory, the toolchain knows it's proven, and regenerating it has to reproduce the same obligations. The verification workflow is complete for its **supported subset** -- deterministic generation, inventory, Lean/Lake checking, cache invalidation, and state reporting are the parts I'd stand behind; treat "every class auto-verifies" as the direction, not a finished guarantee.

---

## Writing for FPGA

Simple has a **VHDL backend**: a documented, hardware-oriented subset of the language compiles to synthesizable VHDL-2008, validated through GHDL analysis and elaboration. It is strict and fail-fast -- constructs outside the supported subset are rejected at compile time rather than silently producing unsynthesizable output, which is exactly the behavior you want when the target is real silicon.

```sh
# Compile the hardware-oriented subset to synthesizable VHDL-2008,
# then analyze/elaborate with GHDL.
simple build --backend vhdl
```

The flow is proven against RV32 simulation: there are two operational GHDL RV32 lanes -- a **semihost** lane (GDB-backed, using ARM semihosting traps) and a **mailbox** lane (debugger-independent, MMIO at a fixed address with a RAM-sentinel mechanism to collect results). The mailbox lane matters because it doesn't need a debugger attached, which is what makes unattended/CI hardware simulation practical.

Be clear-eyed about scope: this is a hardware-oriented *subset* compiled to VHDL and validated in simulation, not a claim that arbitrary Simple synthesizes to an FPGA. The supported-construct matrix in the repo is the contract.

---

## Running tests on the target board

The same test you write for the host can be aimed at hardware. Simple's baremetal flow covers QEMU, semihosting, an MMIO mailbox, and remote baremetal execution, with several authoritative lanes -- a mix of stable and host-aware, including both the GHDL semihost and mailbox simulation paths.

```sh
# Host run
simple test path/to/feature_spec.spl

# Aimed at a board / simulator via the baremetal lanes
simple test --target baremetal path/to/feature_spec.spl
```

The idea is that a feature spec is the unit of work whether it runs on your laptop or on a dev board: the assertions are the same, the result-collection mechanism (semihosting trap or the MMIO mailbox with RAM-sentinel) carries the pass/fail back, and the remote baremetal flow handles getting the binary onto the target and reading the result. So "does this feature actually work on the hardware" becomes a test you run, not a manual bring-up ritual.

The honest qualifier: hardware-dependent lanes are host- and board-aware rather than universally turnkey -- the lane matrix in the repo says which boards and which paths are stable. But the through-line is real: one spec, host or target, same assertions.

On the same target, the **handle pointer** described earlier does the addressing: with no MMU underneath you, the index-into-a-pool model is how you refer to peripherals, buffers, and pool-allocated objects without exposing a raw address that a bad write could corrupt. The stack-only baremetal runtime family decides where that storage lives; the handle is the bounds-checkable way to reach it.

---

## It also happens to be a serious systems language

The four-failures thesis is the reason Simple exists, but the language isn't a toy built only to prove a point. The same source runs three ways -- interpreter, dynamic loader, and ahead-of-time compiler -- and the compiler path targets an LLVM backend, GPU compute via Vulkan, a VHDL backend for RV32 simulation, and baremetal with QEMU and semihosting.

```simple
import std.gpu

@gpu
fn vector_add(a: []f32, b: []f32, result: []f32):
    idx = gpu.global_id(0)
    if idx < len(result):
        result[idx] = a[idx] + b[idx]
```

There are working deep-learning examples (pure-Simple neural nets, LoRA fine-tuning, CUDA), editor support for VSCode and Neovim, and an MCP/LSP toolchain -- all written in Simple. Treat this section as "and it also does this," because it's not part of the LLM-scale argument; it's evidence that the guards above sit on top of a real language.

Interop is part of that story. Simple's supported C/C++ SFFI subset covers imports, exports, callback trampolines, layout verification, and round-trip proof tests, which gives the language a practical path into existing native systems without pretending every dependency will be rewritten.

Two other systems are worth naming with qualifiers. The LLVM family closure is complete for the declared public matrix -- rows are explicitly stable or unsupported, while `rust-llvm` remains a bootstrap-only seed path outside that public claim. AOP exists with predicate pointcuts (`execution`, `within`, `attr`), deterministic before/after/around advice, compile-time weaving by default, and scoped runtime interception; the support matrix is the contract, not "arbitrary aspect magic everywhere."

---

## Three ways to run, and an escape valve for the strictness

The same source runs three ways:

- **Interpreter** -- run a file directly, no build step. The fast inner loop for development and for the bulk of the test suite.
- **Loader** -- load and execute code dynamically, for embedding and for situations where you want to bring code in at runtime rather than ahead of time.
- **Compiler** -- compile ahead of time through the LLVM path (and onward to the GPU, VHDL, and baremetal targets above) for native performance and deployment.

You develop against the interpreter, then compile the same program when you need speed or a deployable artifact -- no rewrite, just a different mode over one language.

The mode that matters most for the article's thesis is **script mode**, which deliberately *relaxes* the strict rules. Everything earlier in this piece -- no primitives on public interfaces, exhaustive matching, the strictest robustness settings -- is what you want when an LLM is generating a million lines you'll never fully read. It's overkill when you're writing a 20-line throwaway to reshape a CSV. Script mode loosens the constraints so the language stays pleasant for small, human-written, one-off code.

This is not a contradiction of the strictness argument -- it's what makes the strictness *affordable*. A language that's maximally strict everywhere is exhausting and people route around it; a language that lets you dial strictness down for a scratch script and up for the system's load-bearing core gets to be uncompromising exactly where it counts. The same defaults-over-config-but-strong-when-it-matters philosophy that shapes the syntax also shapes how hard the compiler leans on you.

(One honesty note, consistent with the rest: confirm the exact invocation for each mode -- how you select interpreter vs. loader vs. compiler, and how script mode is enabled -- against the current CLI before publishing. I've described the modes and their intent, not asserted specific flag names.)

---

## Status, honestly

The toolchain is self-hosted: the compiler, standard library, and tools are Simple source you can read and modify, on top of a precompiled runtime. The project is at its **1.0.0-beta** milestone. The README's published full-suite snapshot from 2026-02-14 reports 4,067/4,067 tests passing in 17.4 seconds.

I want to be precise about what those numbers are: that's **test-suite throughput and pass rate**, not a language-vs-language runtime benchmark. Simple does not yet ship a "Simple vs Rust on benchmark X" comparison, and I'd rather say so than imply one. If you want raw performance claims, that's the next thing to measure, not something to infer from the test timings.

On features: the BDD spec framework, SDoctest, coverage, traceability, the mock policy, the self-hosted compiler, MDSOC manifests, parser-friendly macros, Tree-sitter outline/query tooling, SDN-backed project/test/todo databases, primitive-public-API linting, borrow-checking infrastructure, watch/auto-build support, mmap-backed loader support, baremetal build/test plumbing, and SFFI are all in the "safe to advertise" tier. The Lean verification workflow, the LLVM family closure, the runtime families, the AOP system, and the VHDL/baremetal lanes are real but best described within their bounded scope -- full in the declared matrix, deferred elsewhere. The repo's README breaks this down feature by feature; I'd point a skeptical reader straight at it.

**The GUI does not work yet.** I'm calling this out plainly because it's the most visible gap. There's a shared UI test protocol across the web backend and a TUI-web proxy, but that's a test contract, not a working rendering layer. The user-facing GUI is unfinished. Here's the plan, in the order I intend to build it:

1. **A lightweight TUI first.** Before anything graphical, a terminal UI that's small, fast, and dependency-light -- the thing that works everywhere, including over SSH and on baremetal-adjacent targets, and the easiest surface to make correct.
2. **One shared interface across TUI, GUI, and web.** A single UI contract that all three surfaces implement, so a component is written once and rendered as a terminal view, a native window, or a web page. The shared test protocol that exists today is the seam this is meant to grow into -- the goal is one `handle_test_request`-style contract driving every surface, not three parallel UIs that drift apart. (Notice this is the same anti-drift principle as the rest of the language, applied to UI.)
3. **A textual debugging GUI exposed three ways -- API, LLM (MCP), and CLI.** The debugger front-end should be drivable as a programmatic API, as an MCP tool an LLM can operate directly, and from the command line -- the same debugging surface whether a human, a script, or a model is at the controls. This matters for the million-line thesis: when generated code fails, the model needs to *debug* it through the same machine-checkable interface it uses to write it, not hand off to a human at a graphical window.

Treat (1)-(3) as roadmap, not shipped. I'd rather list the plan than imply a GUI exists.

---

## Try it

```sh
# From a source checkout
git clone https://github.com/simple-lang/simple.git
cd simple
export PATH="$PWD/bin:$PATH"
simple --version
```

> *Release-note cleanup before publishing: `VERSION` currently says `1.0.0-beta`, while the README's binary install block still points at the older `simple-lang/simple` v0.6.1 tarball. Do not publish a hardcoded binary URL until the release tag, asset filenames, and canonical repo path are reconciled.*

Source, examples, and the full feature breakdown: **github.com/simple-lang/simple**

If you've also tried generating large systems with an LLM and watched them rot in exactly these four ways, I'd like to hear whether these guards match the failures you hit -- or which ones I'm missing.
