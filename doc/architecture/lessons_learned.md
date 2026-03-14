# How I Wrote 1 Million Lines of Code with LLMs

I was writing 1M lines of code. Over time, it became 400K lines of test code and 100K lines of logic — all by relentlessly removing duplication and deleting the old Rust implementation. Here's what I learned about writing massive codebases with LLMs (mostly Claude, occasionally Codex).

---

## Remove Duplications — Relentlessly

This is the single most important discipline. Removing duplication often *adds* code to your codebase — helper functions, shared modules — but it pays for itself immediately.

LLMs love to produce duplicated code. The problem? They'll update *one* copy of the duplicated logic and add a feature there, then add a different feature to *another* copy. If you let these two branches of logic diverge for too long, merging them becomes nearly impossible.

My personal threshold: **5 lines or more** of duplicated code gets refactored.

Here's my duplication-hunting checklist:

1. **Cosine duplication check** — effective, but slow to run at scale.
2. **Semantic duplication check** — use an LLM or a dedicated tool to find and remove conceptual duplicates.
3. **Manual review of folders and files** — this is non-negotiable, especially after architectural refactoring. LLMs often fail to delete old files or quietly recover them from history.
4. **Architecture and file changes must be thoroughly propagated** — if you move something, make sure *everything* that references it gets updated.
5. **Don't forget documentation** — doc duplication is easily overlooked, and I've overlooked it many times myself, which always causes problems down the road.

A few more rules: don't create modules that do similar work. If you need something similar, either put it somewhere clearly separate or design your code so you don't need it at all. And when a branch or workspace is done, **immediately merge or rebase** before moving on.

---

## Keep Files Under 1,000 Lines

Don't let any file — source or Markdown — grow too large. My personal sweet spot is **around 800 lines**.

When files get too long, LLMs have to read too much context. When they read too much, they get noticeably dumber. Some files genuinely can't be broken up further — in those cases, manually review them to confirm they truly can't be separated.

These first two rules — removing duplication and keeping files short — are the most important. Follow them consistently, and you *can* scale to a million lines.

---

## Use the Best Model

Use the best model available — like Opus — for most work. At minimum, use Opus in plan mode.

Less intelligent models tend to produce duplicated source code and generate dummy or mock implementations instead of real ones. If you feel like you can't get good results from an LLM, reconsider whether the real issue is budget rather than capability. Money can solve *almost* all problems in this space.

---

## Use a Different Model to Verify

Codex is less efficient at writing long code, but it's surprisingly good at catching duplication and spotting dummy implementations. When you're building complex logic, verify it with a different model.

The landscape changes fast — Codex a month ago and Codex today are very different, especially for the largest models. They use tools properly now, though still not as efficiently as Claude.

Beyond verification, sometimes one model simply can't solve a problem that another model handles easily. If your primary model is stuck on implementing a feature, try switching to another large model before giving up.

---

## Don't Pollute Your Startup Context

The startup portion of context is not equal to the rest. LLMs pay disproportionate attention to it — often even more than humans do.

### Install as Few MCPs as Possible

Keep your MCP installation minimal unless you have a specific, compelling reason.

Often, just installing the language MCP is enough. LLM companies build their models to handle most tasks without extra tools. And when you do install MCPs, prefer the version suggested by the LLM company over the most popular community alternative — the official MCP has already been trained into the model, so it won't be forgotten or misused.

MCPs themselves consume context, and that startup context is precious real estate. Enable additional MCPs only on agents, as private tools.

### Keep CLAUDE.md / AGENTS.md as Short as Possible

Put the details in skills or agent files instead. Add searchable keywords so the right skill or agent gets found. Bloated instruction files lead to more mistakes, not fewer.

---

## Prefer System Tests Over Mock Tests

Every feature should be verified with an end-to-end system test. Build scripts or libraries to support system testing — don't fall back on mocks and stubs.

> This is actually one of the reasons I built my own language: to make it harder to cheat with mocks.

Don't allow system tests to use mocks. If a system test truly can't run without mocking something, use a container or VM instead. Or, if that's not feasible, create a completely separate codebase for those tests — isolated from your real system tests — and allow mocks only there.

You can still add integration and unit tests as you see fit. But do your own manual testing for each group of features. And use a different language model to audit for dummy implementations.

---

## Reduce Public Interfaces as Much as Possible

Use `__init__` or your language's package export mechanism to limit what's publicly visible. Don't use wildcard exports (`*`) — they lead to brainless, sprawling APIs.

> I designed my language to handle this: folder-based public visibility with feature-group-based friend access.

When an LLM has to look at too many public interfaces, it gets exponentially dumber. This is actually the reason you should install at least the language MCP, even though startup context is precious — it helps the model navigate your codebase without being overwhelmed.

---

## Use an Environment Similar to What the LLM Was Trained On

LLMs perform dramatically better in Unix-like environments. On Windows, they fill code with obviously wrong assumptions without even checking. If you need Windows, at minimum install MinGW or Linux-like tools to mimic a Linux environment.

As mentioned earlier, if the LLM company provides an MCP that competes with a more popular community alternative, use the official one — unless it's genuinely too buggy (which is unlikely).

Use Git. Yes, I use jj — if you look at this repository, you'll see it. I like jj, and I want to become more fluent with it, but honestly, the LLM experience is much better with Git.

---

## Don't Tell the LLM "Don't Write TODOs"

If you tell an LLM not to write TODOs, it will just write `NOTE` comments instead. Same laziness, different label.

Instead, tell it to **implement the feature** rather than leaving a TODO. That's much safer — you get actual code instead of deferred promises.

---

## Use a Strongly Typed, Compiled Language

Languages like Rust, Java, and Erlang share a quality: if it compiles, it *feels* like it will run correctly.

(I haven't actually tried Erlang, though — has anyone? LLMs might not produce good Erlang since it's not as popular as Rust or Java.)

I tried TypeScript but didn't have a good experience, though that might be because it was a few months earlier when LLMs were less capable. Just a few months ago, LLMs struggled to produce over 1,000 lines of code in one go — now they easily generate 10K to 100K lines. Languages designed for strong typing and robust implementation make LLMs produce much better long-form code.

> Rust is a great language for building your own language, but my project ended up more Rust-like than I intended. Rust's best and worst feature is its borrow checker — it's too difficult for beginners. So I limited borrowing to specific, controlled situations to keep things simple.

---

## Keep Your Eyes on It

Watch what the LLM does while it works. Use multiple panes. Have it show you example output of what it's building before it finishes.

The result format can vary wildly between cases, so verify early that what the LLM is trying to build matches what you actually wanted. If there's a fundamental misunderstanding, it will show up in these early previews — and those misunderstandings are *extremely* hard to find and fix after the fact.

This kind of drift happens because your prompts naturally get shorter and terser over time. It's inevitable. At the very least, check the LLM's building logic by reviewing example output early in the process.

---

## Do Your Research First

Before implementing a feature, research how the outside world has solved similar problems. What issues commonly arise in this domain? What are the standard solutions? What's the conventional approach?

Then look at what code and design already exist in your current codebase. Update your architecture docs and design documents. *Then* plan. *Then* implement.

---

## BDD (and TDD)

Implementation with system tests must involve TDD. BDD is even better — your tests double as feature documentation.

---

## TL;DR

- Minimal MCPs, minimal CLAUDE.md
- Remove duplications relentlessly
- Keep all content short
- Keep your eyes on it
- Research the problem domain and your current implementation before coding
- Use a strongly typed language — in most cases, that means Rust or Java — where passing the compiler feels like the code will just work
