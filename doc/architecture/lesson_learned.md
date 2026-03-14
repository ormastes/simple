# How I Wrote 1 Million Lines of Code with LLMs

I started this project at the end of November 2025, with a week of pre-interpreter work. By mid-March 2026 — roughly three and a half months — the compiler was fully working. Along the way, 1M lines of code became 400K lines of test code and 100K lines of logic, all by relentlessly removing duplication and deleting the old Rust implementation.

Everything here was learned with real money on real projects — mostly Claude, occasionally Codex. None of this is in any official documentation. I hope it helps anyone who's been trying to scale past a few thousand lines of LLM-generated code and keeps hitting a wall.

---

## Context Is the Enemy — Make `/clear` and `/compact` a Habit

As conversations grow longer, LLM performance degrades **exponentially** — not linearly. Past a certain point, the model becomes noticeably dumber.

Use `/clear` to reset your session at each natural work boundary whenever possible. When your current task is highly related to what you just finished and you need continuity, use `/compact` to summarize prior context and reclaim space instead. The thought "I'll just keep going, it's easier" is the single most expensive mistake you can make.

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

Use the best model available — like Opus — for most work. At minimum, use `opusplan` mode, which plans with Opus and executes with Sonnet. The quality difference compared to pure Sonnet is dramatic — because the quality of planning drives the quality of everything that follows.

The absurd mistakes you see in large tasks — calling APIs that don't exist, re-introducing a bug you just fixed — mostly come from smaller models like Sonnet. Opus makes mistakes too, but the frequency and severity are on a completely different level.

Less intelligent models tend to produce duplicated source code and generate dummy or mock implementations instead of real ones. If you feel like you can't get good results from an LLM, reconsider whether the real issue is budget rather than capability. Money can solve *almost* all problems in this space. If you use a smaller model for big coding work to save money, you *will* face the consequences at some point.

That said, working efficiently with LLMs means reducing token usage — which paradoxically often produces *both* better results and lower costs. The goal isn't to spend less; it's to spend *smarter*.

---

## Use a Different Model to Verify

Codex is less efficient at writing long code, but it's surprisingly good at catching duplication and spotting dummy implementations. When you're building complex logic, verify it with a different model.

The landscape changes fast — Codex a month ago and Codex today are very different, especially for the largest models. They use tools properly now, though still not as efficiently as Claude.

Beyond verification, sometimes one model simply can't solve a problem that another model handles easily. If your primary model is stuck on implementing a feature, try switching to another large model before giving up.

---

## Don't Pollute Your Startup Context

The startup portion of context is not equal to the rest. LLMs pay disproportionate attention to it — often even more than humans do.

### Install as Few MCPs as Possible

Keep your MCP installation minimal unless you have a specific, compelling reason. Install roughly **one MCP** — the one for your development language — and that's it. The reason is the same as keeping `claude.md` short: every MCP you install dumps tool schemas into your early context, consuming cognitive resources that should go toward actual work.

Often, just installing the language MCP is enough. LLM companies build their models to handle most tasks without extra tools. And when you do install MCPs, prefer the version suggested by the LLM company over the most popular community alternative — the official MCP has already been trained into the model, so it won't be forgotten or misused.

MCPs themselves consume context, and that startup context is precious real estate. If you genuinely need additional MCPs, install them on sub-agents rather than your main session — enable additional MCPs only on agents, as private tools.

### Keep CLAUDE.md / AGENTS.md as Short as Possible

This was the most counterintuitive lesson. Packing `claude.md` with verbose rules actually **hurts** performance. If Claude doesn't agree with a rule, it won't follow it anyway — so those ignored rules just eat up your precious early context for nothing.

**What to include:**
- Project-specific folder structure (skip this too if it's a conventional layout)
- Targeted corrections for mistakes Claude **repeatedly** makes
- Foundational context (e.g., "C++ bare-metal environment", "BDD development workflow")

**What NOT to include:**
- Common-sense coding rules
- Generic code style guides
- Behavioral directives telling Claude how to "act"

If you need complex instructions, separate them into skills or agent files. Add searchable keywords so the right skill or agent gets found. Here's a surprising finding: **writing no `claude.md` at all produces noticeably better results** than using a `claude.md` that Claude hastily generated for you.

---

## Verify Your Language MCP's LSP Is Actually Working

Whether or not you install a language MCP makes a decisive difference in LLM performance as your codebase grows. Most language MCPs analyze code internally through LSP (Language Server Protocol), and some support debugging through DAP (Debug Adapter Protocol) as well.

The key point: **the LSP must actually be working**. For example, in C++, if header dependencies are tangled or excessive includes prevent the LSP from functioning properly, the language MCP becomes useless — and the LLM can't perform at its best.

---

## Tame Your Folder Structure

Let the LLM choose folder names and organization in most cases — it usually makes reasonable choices. But intervene when it would create duplicate folders or files with overlapping responsibility.

One practical trick: **create a `temp/` folder at the project root.** LLMs have an irresistible urge to dump files in the root directory. A dedicated temp folder catches throwaway files and keeps your root clean.

Better yet, restrict file creation privileges at the root level. Lock down `doc/`, `src/`, and the project root so that new folders and files can't be casually created there. This forces the LLM to think about where things actually belong instead of littering the top level.

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

LLMs perform dramatically better in Unix-like environments. Just like humans lose productivity in unfamiliar surroundings, Claude struggles the same way. Since the vast majority of training data comes from Unix/Linux environments, performance degradation on Windows becomes more pronounced the harder the task.

If you need Windows, at minimum install MSYS2, Git Bash, MinGW, or other Linux-like tools to mimic a Unix environment.

As mentioned earlier, if the LLM company provides an MCP that competes with a more popular community alternative, use the official one — unless it's genuinely too buggy (which is unlikely).

Use Git. Yes, I use jj — if you look at this repository, you'll see it. I like jj, and I want to become more fluent with it, but honestly, the LLM experience is much better with Git.

---

## Speak English — Even If It's Broken

Prompt engineering matters less than people think. But if English isn't your primary language, here's one tip that genuinely makes a difference: **write your prompts in English anyway**, even if it's broken or grammatically rough. LLMs consistently produce better results from broken English than from well-written prompts in other languages.

---

## Don't Tell the LLM "Don't Write TODOs"

If you tell an LLM not to write TODOs, it will just write `NOTE` comments instead. Same laziness, different label.

Instead, tell it to **implement the feature** rather than leaving a TODO. That's much safer — you get actual code instead of deferred promises.

---

## Use a Strongly Typed, Compiled Language

For projects at scale — tens of thousands of lines and beyond — Claude's true strength shows in strongly typed languages like Rust, Java, and Erlang. When the compiler acts as a safety net, defects in LLM-generated code surface immediately and get fixed fast.

With dynamically typed languages, the bugs Claude introduces hide until runtime, and debugging costs grow exponentially as the codebase scales.

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

Don't jump straight into implementation. Have the LLM create a research document first — covering external references and analyzing the relevant parts of your current codebase. This single step dramatically improves the quality of the final output.

"Implement X" produces far worse code than "Before implementing X, write a research document first. Survey relevant external resources and map out the related parts of our current codebase." The research step is the difference between mediocre and excellent results.

Then look at what code and design already exist in your current codebase. Update your architecture docs and design documents. *Then* plan. *Then* implement.

---

## Ask for Options at the Plan Stage

When building a plan, ask Claude to "show me 2–3 possible directions for the expected outcome." This prevents the waste of receiving a finished result that went in a direction completely different from what you wanted — only to start over from scratch.

Locking in your preferred direction upfront saves both context and money.

---

## Use Agent Teams

Don't try to handle everything with a single agent. Agent teams — where specialized agents collaborate on different aspects of a task — produce noticeably better results.

As of early 2026, agent teams have stabilized and work very well. **Use agent teams as your default approach** rather than pushing everything through a single agent. They're more stable and more capable than simple multi-agent setups.

---

## BDD (and TDD)

Implementation with system tests must involve TDD. BDD is even better — your tests double as feature documentation.

---

## Appendix: Designing a Language for the LLM Era

Throughout this article, I've mentioned "my own language" — Simple — several times. Building a compiler was one of the motivations behind this project, but along the way, certain language design decisions turned out to be surprisingly well-suited for LLM-assisted development.

I'm not yet fully certain which of these concepts are genuinely helpful versus merely seeming so, but the results have been positive so far:

- **No mocks by design** — the language makes it structurally harder to cheat with mock implementations, pushing toward real system tests.
- **Folder-based visibility** — public interfaces are controlled at the folder level, with feature-group-based friend access. This naturally limits what an LLM has to consider.
- **Restricted borrowing** — Rust-style borrow checking exists but is limited to specific situations, keeping the language accessible to beginners (and to LLMs that struggle with complex ownership semantics).
- **SDN over JSON/YAML** — a custom data format that's simpler for both humans and LLMs to parse correctly.

The broader idea: languages designed with LLM ergonomics in mind — strong types, limited public surface area, compiler-enforced correctness — can meaningfully improve the quality of AI-generated code at scale. Whether this approach generalizes beyond my specific project remains to be seen, but so far the evidence is encouraging.

---

## TL;DR

The one principle that runs through everything: **treat Claude's context as sacred.**

- Use `/clear` between tasks, `/compact` when continuity matters
- Minimal MCPs, minimal `claude.md`
- Remove duplications relentlessly
- Keep all content short — files under 1,000 lines
- Tame your folder structure — use `temp/`, restrict root creation
- Keep your eyes on it
- Write prompts in English, even if it's broken
- Research the problem domain and your current implementation before coding
- Ask for directional options at the plan stage
- Use a strongly typed language — in most cases, that means Rust or Java — where passing the compiler feels like the code will just work
- Use agent teams as your default

The context window is the LLM's working memory. Focusing that limited resource entirely on the actual task is the key to getting the best results for your money.
