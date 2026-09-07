# Release 1.0.0-rc.1 — handover

**Written:** 2026-09-07, at the end of a two-day bootstrap/release session.
**For:** the agent or engineer taking the release forward.
**Short version:** the release *paperwork* is done and green. The release is
blocked on one thing only — **Stage 2 of the bootstrap does not link yet**, and
therefore no deployable artifact exists. That gap is now fully enumerated.

---

## 1. What is DONE

### Landed on `main` (PRs #437, #478, #479, #483, #489 — all merged)

**Release surface repaired.** `e274cd33719` ("chore: merge all share-history
worktree branches into main") was a single-parent whole-worktree snapshot that
silently rewound content across the release path. Casualties found and restored:

| file | what was lost |
|---|---|
| `src/app/release/main.spl` | 978 → 254 lines; **all 21 dispatch targets called but defined nowhere** — the CLI could not compile |
| `.github/workflows/candidate.yml` | 4 of the 5 staged-bootstrap steps its own contract check requires |
| `.spipe/policy/vcs.sdn` | the privileged self-review live-apply block |
| `.github/workflows/review-admission.yml` | `expected_head_sha` binding + invalidation ladder |
| `.github/workflows/pr-admission.yml` | the owner-attested convergence lane |
| 20 guidance surfaces, 4 spipe projections | scoped self-review rollout |
| `src/app/llm_caret/claude_full/**` | 99 resurrected duplicate modules that broke **every** whole-project `native-build` |

**`release/support.sdn` authored.** It never existed; `support-check` was
rejecting on a missing input, not a defect. Schema was derived from the reader's
own rejection messages, one at a time. `x86_64-unknown-linux-gnu` is the single
required target on all four channels (it is what `candidate.yml` actually builds
and what `release/` actually carries); `aarch64-unknown-linux-gnu` is declared
**experimental / not required** because it has no artifact and its bootstrap
does not complete.

**Perf fixes.** LLVM signature lookup 20,920,000 rows scanned → 1,500;
base64url 420× → 17.6× vs C; WFFI checked calls 2.00 → 0.00 allocations/call.

**Memory fixes.** Bootstrap worker count now clamped by `MemAvailable` (was
CPU-derived only — 10 workers × ~3.2 GB exhausted the box and the *linker*
failed); transient-scope reclamation extended to the per-module MIR arena and
the non-entry-closure fallback (**354×/355×** on native fixtures, and 2.3×
faster); a **use-after-free** fixed in `module_surfaces_freeze` (four `text`
fields re-assigned inside an ended scope; the crash surfaced 69 minutes later as
a SIGSEGV in an unrelated validator).

**Compiler miscompilations — one root pattern, five instances.**
*The seed's LLVM codegen resolved by NAME and ignored the receiver type.*

| # | what was resolved by name | consequence |
|---|---|---|
| 1 | `to_i64()`/`to_int()` on `text` | compiled to the **identity** — `--threads 1` became a raw pointer, so a "single-threaded" build ran 44 racing workers |
| 2 | struct field **offsets** | read offsets 56/88 of a **32-byte** struct (`size` is declared at 10 indices across 202 structs) |
| 3 | struct field **types** | a `text` field formatted as `i64` |
| 4 | user `to_text()` | hijacked by the builtin leaf-name shim |
| 5 | UFCS fallback | declared a **phantom extern** (`"text.split_whitespace"`) that was never a real symbol |

**`rt_hash_text` unified.** It had **five implementations producing three
different results** — FNV-1a in C, DJB2 in the Rust interpreter, DJB2 in the
Rust native runtime, DJB2 in the pure-Simple twin, and a Cranelift JIT inline
path that returned a **constant 0**. `FileFingerprint.content_hash` is written
by the interpreted worker and verified by compiled code, so the capsule receipt
could never validate. All lanes now FNV-1a.

**Guards added** (each proven to fail on its own pre-fix shape): snapshot-clobber
detection, module-name injectivity, bootstrap memory clamp, cross-lane hash
agreement, transient-scope boundaries, no-unwind-dependency, pure-vs-native I/O
effect comparison, AOT-failure-attributability.

### Local release check — GREEN

```
simple release version-check   -> {"status":"ok"}
simple release support-check   -> {"status":"ok"}   (all four channels, and with --observed-target)
check-release-policy-parity    -> PASS (12 surfaces)
check-release-version-consistency -> pass version=1.0.0-rc.1
check-github-policy-projection -> PASS
check-c-runtime-compiles-push  -> PASS — 134 file(s) compiled, 0 errors
check-guard-wiring             -> PASS — 0 NEW unwired
```

`candidate-check`, `promote-check` and `withdraw-check` reject **correctly**:
they require a candidate manifest and six sha256s that only a real candidate
build produces. They are gated, not broken.

---

## 2. What REMAINS

### The blocker: Stage 2 does not link — 139 undefined symbols

**Read `doc/08_tracking/bug/stage2_link_full_undefined_symbol_census_2026-09-07.md` first.**
It has a per-symbol table with declared / C / Rust columns.

Original count **246**. Each bootstrap run appeared to show only ~5 because
**LLD defaults to `--error-limit=20`** and the diagnosis tool cuts to "First 5".
Do not chase them one run at a time — that wasted about an hour here.

| bucket | count | status |
|---|---|---|
| fixed (math/atomic/time/abi) | 32 | ✅ merged |
| cranelift JIT bridge | 75 | ✅ merged as **named traps** — dead code in this lane (default backend is `llvm`, `bootstrap-from-scratch.sh:573`) |
| **Rust-only misc** | **90** | 30 done (PR #492); **56 remain**, each named in the census |
| sqlite lane wiring | 24 | ❌ excluded by design; it is a **caller-wiring** bug, not a missing symbol |
| no reference semantics | 15 | ❌ `rt_file_view_*_v1`, `rt_pinned_archive_*_v1`, `rt_native_build` — nothing to mirror; do not guess |
| UFCS dotted | 7 | partially addressed by #489 |
| lenient unresolved global | 3 | `GenericTemplate.is_err` (zero implementers), `Unit` (called as `Unit()`; the real literal is `()`) |

### Memory: the 37 GB immortal heap

Self-hosted, every allocation compiled-Simple code makes is registered in
`HEAP_ALLOCATION_REGISTRY` and never unregistered — measured `[heap]` Rss
**37,171,428 kB** in one brk mapping. Scopes fix this *where they apply*.

**There is a written, gated, NOT-merged change** on branch
`work/mir-bootstrap-transient-census` that removes the `ambient_bootstrap_enabled()`
guard and promotes the `_bootstrap_mir_*` / `_bootstrap_fn_*` registries. Its
census is thorough (every write site grepped) and its conclusion is that they
are promotable. **I deliberately did not merge it**, because it removes a guard
on the path the bootstrap itself runs and it has **no native RSS measurement and
no rebuilt-binary proof** — a census is evidence, not a measurement. Merge it
only after producing both.

---

## 3. What to CARE about

**Verify claims by measurement, not by exit code.** This session repeatedly
produced confident wrong answers that a single check would have caught:
- "the `.so` has zero unwind deps" — from grepping `ldd` for the string
  *unwind*. `libgcc_s` **is** the unwinder and does not contain that string.
- "`SIMPLE_LINKER=lld` works" — read from a passing exit code. The env var is
  not consulted on that path at all; `SIMPLE_LINKER=bogus-linker` also exits 0.
- "110M allocations, zero frees" — the counters were **unbacked externs
  returning nil**.

**A preserved binary bakes in its compiler AND its runtime.** No `src/**` edit
is observable on it without a rebuild. Probe `print`s producing zero output is
**not** evidence your code is unreached. This misled three agents.

**Stage 2 links the *Rust* runtime, not the C one.** A C-only symbol is
undefined there. Root cause: `runtime.c` and `runtime_native.c` are **not in
`runtime/build.rs`'s C-source whitelist**. Three separate defects this week
traced to this.

**`text`-taking runtime functions must be registered in the seed's `(ptr,len)`
text-ABI tables** (`codegen/instr/calls.rs` `text_arg_indices`,
`codegen/runtime_sffi.rs` `RUNTIME_FUNCS`) — otherwise codegen collapses two
text args into one word **after** the link succeeds. Worse than a link error.

**Exactly one `#[no_mangle]` per symbol.** Two are a hard
`symbol is already defined` that breaks the whole seed build.

**Never validate with a cranelift-built Stage 2** — it SEGVs at
`hir 1/1 step 2/6`, an unrelated defect.

**Whole-worktree "sync" commits are the single largest source of damage here.**
`e274cd33719` alone rewound seven surfaces with no conflict and no failing check.
`check-no-stale-snapshot-rewind.shs` now detects that shape (it FAILs on that
commit, PASSes on 19 ordinary ones including four real reverts) — but it is
**advisory**, and it misses small critical losses: it does not catch the
`self_review_policy.spl` rollback, which lost 49 of 640 live lines (7%, under
its 25% floor).

**One unresolved policy question, for a human.** `check-self-review-policy`
fails on `main`: the v2 migration is half-landed — the evaluator moved to
`spipe-self-review-policy-db/2` (broker-signed evidence required) but the gate
and the `.sdn` projection still grep for the old `self_attested` contract. An
agent had "restored" the weaker `grant/1` evaluator **and deleted the spec case
asserting the stronger behaviour**; that was reverted. **Do not resolve this by
editing the gate** — choosing which policy version is authoritative is an owner
decision.

**Operational notes.** Detach long runs (`setsid`) and write results to a file —
the harness kills foreground waiters on spurious "low memory" (it appears to read
`free` rather than `available`); a pane-attached build dies with the pane. Never
`pgrep -f` a pattern that appears in your own command line — it matches itself
and hangs or self-terminates; bracket a character (`simple-baselin[e]`). A failed
bootstrap **does not reap its own workers**: a 42 GB orphan holding the output
lock made the next three runs fail 30 seconds in with a misleading
`failure_root=stage2`.

---

## 4. The path to a real release

1. Land the remaining **56** Rust-only misc symbols. PR #492 closed 30 of 90.
   The census names each remaining one and why the skipped ones were skipped:
   the `rt_simd_*` (22) and fd-based `rt_io_file_*` (12) families need
   per-symbol reference checks; the capability-sandboxed group needs
   `security_runtime.rs`, not a single-function mirror. Four symbols
   (`rt_file_atomic_write_mode`, `rt_file_list_dir`, `rt_file_mode`,
   `rt_fs_read_text`) have **no implementation on either side** — a different
   problem, do not paper over them.
2. Decide the sqlite caller-wiring (24) and the 15 no-semantics symbols — both
   need an owner decision, not more implementation.
3. Get Stage 2 to link, then Stage 3 self-host, then Stage 4 + `--deploy`.
   Sequence that works: `--full-bootstrap --stop-after-stage2` (trust root) →
   planner receipt (`--target=//bootstrap:stage4 --reason=release-trust-verification`)
   → `--full-bootstrap --bootstrap-receipt=<path> --deploy --full-cli --mode=one-binary --strategy=adhoc`.
   Each step must run against **one unchanging tree**; a rebuilt parent
   invalidates an existing receipt (`parent-stage2-sanity-admission-mismatch`).
4. With a deployed binary: run the release-bound whole-suite test
   (`bin/simple test test --whole --mode=interpreter`; it needs `--no-cover-check`
   to get past a preflight gate, and is ~11 h at ~22 files/min for 17,124 files).
5. Then `candidate-create` → `candidate-admit` → `promote-check` → the real
   `gh release`. **Ask before publishing.**
