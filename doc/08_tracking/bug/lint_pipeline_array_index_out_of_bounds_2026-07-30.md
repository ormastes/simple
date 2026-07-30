# `bin/simple lint` crashes on any non-empty input: array index out of bounds

Date: 2026-07-30

## Symptom

```
$ bin/simple lint <any-file.spl>
...
error: semantic: array index out of bounds: index is N but length is 0
```

This reproduced identically on completely unrelated files (originally observed
on `src/compiler/35.semantics/lint/_SimdOpportunityLint/arithmetic_checks.spl`
and `byte_checks.spl`), blocking `bin/simple lint` for every session working
in this repo today.

## Reproduction boundary

`bin/simple` currently resolves (via `bin/simple` -> `bin/release/aarch64-apple-darwin-macho/simple`)
to a **Rust-built bootstrap-seed binary**, not the pure-Simple self-hosted
binary the repo's own rules require (`file` reports a Mach-O executable that
prints `WARNING: this Rust-built Simple binary is a bootstrap seed only`).
That binary tree-walks (interprets) the pure-Simple compiler source under
`src/compiler/**` to run `bin/simple lint`. This matters because it means the
crash lives in **interpreted pure-Simple source**, not in the Rust seed
itself — confirmed by getting a Rust backtrace via `SIMPLE_INTERP_OOB_DEBUG=1`
(a debug hook already present at
`src/compiler_rust/compiler/src/interpreter/expr/collections.rs:506`) and
reading off the AST identifiers of the indexing expression that faults
(`recv=Identifier("expr_tag") idx=Identifier("eid")`,
`recv=Identifier("decl_tag") idx=Identifier("idx")`, etc.) — these are Simple
source-level array names, not anything in the Rust seed.

Narrowing the trigger:

| Input | Crashes? |
|---|---|
| `bin/simple lint --help` (no target file) | No |
| Empty file (`printf '' > f.spl`) | **No** |
| `fn main():\n    pass` | Yes |
| `val x = 1` | Yes |
| `val a = 1\nval b = 2\nval c = 3` | Yes |
| Any file with a real top-level decl (fn or val) | Yes |

So the crash is **not** about the target file's content/complexity — it fires
on the smallest possible non-empty, syntactically valid file with at least one
top-level declaration. A file with zero declarations (blank file) never
reaches the faulting code path at all (lint bails out earlier with a plain
"Lint failed" message, no parse of file content).

## Root cause

There are (at least) two distinct arena/array-indexing bugs on this same
"stale index into a parse-time arena array" family, both in
`src/compiler/10.frontend/**`, which stores the AST as a set of parallel
global arrays indexed by integer id (arena pattern: `expr_tag`, `decl_tag`,
`stmt_expr`, etc., declared in `src/compiler/10.frontend/core/_AstExpr/nodes.spl`
and `src/compiler/10.frontend/core/_Ast/decl_nodes.spl`).

### Bug 1 (fixed): unguarded arena index in yield/placeholder helpers

`expr_contains_yield` / `stmt_contains_yield`
(`src/compiler/10.frontend/core/_Ast/module_state.spl:695-719`, called from
the interpreter at **function-call time**, long after parsing, via
`src/compiler/10.frontend/core/interpreter/eval_calls.spl:359` and
`.../interpreter/_EvalOps/call_method_eval.spl:379` to detect generators) and
the three placeholder-lambda scanners in
`src/compiler/10.frontend/desugar/placeholder_lambda.spl`
(`detect_placeholder_mode:93`, `count_placeholders:252`,
`replace_placeholders:361`) only guarded against `eid < 0` (the documented
"no expr" sentinel, e.g. `stmt_expr.push(-1)` in `ast_stmt.spl:210`). None of
them guarded against `eid`/`idx` being **non-negative but beyond the current
length** of the arena array — which happens because `ast_reset()`
(`module_state.spl:453`) clears `expr_tag`/`decl_tag`/etc. back to `[]` for
every subsequent parse (`parser_init_with_path` calls it unconditionally,
`parser.spl:229`), while some ids captured before a reset are read back
later. Fixed by bound-checking `eid >= expr_tag.len()` (and
`sid >= stmt_expr.len()`, `idx >= decl_tag.len()`) alongside the existing
negative check, returning the same "not found / no expr" answer the negative
branch already returns. This is the *documented, legal* half of the
instructions here: a genuinely out-of-range id is treated the same as "no
such expr", which is what the pre-existing `eid < 0` branch already did for
the sibling sentinel case — not a new silent-swallow of a real error.

### Bug 2 (root-caused, NOT fixed — out of safe scope for this change)

After fixing Bug 1, `bin/simple lint` on the most trivial possible file
(`val x = 1`) still crashes, now at `decl_tag[idx]` (confirmed via the same
`SIMPLE_INTERP_OOB_DEBUG=1` technique: `recv=Identifier("decl_tag")
idx=Identifier("idx")`). Direct instrumentation (temporary `print`s, since
removed) proved the following sequence for a `val x = 1`-only file, in the
same lint invocation:

```
[decl_alloc]        idx=0 tag=4 decl_tag.len()=1   <- during parse (decl_nodes.spl)
[module_get_decls]  count=1     decl_tag.len()=0   <- right after parse, in the
                                                       lint driver (module_state.spl)
```

`ast_module_decl_count_get()` (a separately-tracked counter slot) correctly
reports 1 declaration was parsed. But by the time `module_get_decls()` (called
from `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:48`, right
after `parse_module_silent_checked` returns) reads `decl_tag`, the SAME global
array reports length 0 — for the identical global variable, with no
intervening `ast_reset()` call traced (`SIMPLE_TRACE_AST_RESET=1` shows
exactly one reset for the target file's own parse, which is *before*
`decl_alloc` runs, not after).

This means `decl_tag` (a plain module-level `var` declared in
`src/compiler/10.frontend/core/_Ast/decl_nodes.spl:225`) is not reliably
visible with its latest value when read from a **different** module
(`module_state.spl`) than the one that wrote it (`decl_nodes.spl`), under this
interpreter. This is not a hypothesis of last resort: the codebase already
documents and partially works around exactly this limitation elsewhere —
e.g. `ast_decl_prefer_arena()` in `decl_nodes.spl:152-157` falls back to a
`rt_env_get` mirror with the comment *"Interpreter module variables may not
persist between calls"*, and there is a whole opt-in "arena harden" /
"generation diagnostics" subsystem added **the day before this bug report**
(`module_state.spl:48-165`, dated 2026-07-29, `SIMPLE_AST_GEN_HARDEN` /
`SIMPLE_AST_GEN_CHECK`, off by default) built specifically to turn stale-arena
reads into a clean diagnostic instead of a crash — but it is not wired into
`decl_get`/`module_get_decls`/most of the ~30 direct `decl_tag[idx]` call
sites across `src/compiler/35.semantics/lint/*.spl`, and is disabled by
default, so it did not help here.

**Why this is not fixed in this change:** the real defect is cross-module
global-variable visibility for a plain `var` under the interpreter (or,
alternatively, a still-unidentified extra write that clears `decl_tag` alone
without also clearing `ast_module_decl_count_slot`, since a full `ast_reset()`
would have zeroed both). Either way, the fix is not a local bounds-check: it
is either an interpreter-level global-state bug (and the interpreter lives in
`src/compiler_rust/`, explicitly out of scope for this pure-Simple change), or
a much larger sweep of ~30 call sites (`decl_tag[idx]` in `unused_vars.spl`,
`closure_capture.spl`, `match_exhaustiveness.spl`, `deprecated.spl`,
`stub_impl.spl`, `required_comment.spl`, `argument_count.spl`,
`duplicate_typed_args.spl`, `ignored_return.spl`, `use_resolution.spl`,
`collection_patterns.spl`, `star_import.spl`, `primitive_api_arena.spl`,
`unreachable_code.spl`, and `decl_get`/`decl_nodes.spl` itself) that would
need the same treatment as Bug 1 plus a decision about what a "can't resolve
this decl" fallback should mean for each of ~14 different lint checks. That
is real, non-trivial design work, not a minimal patch, and risks papering
over the actual defect (global state loss) rather than fixing it.

## Fix applied (Bug 1 only)

- `src/compiler/10.frontend/core/_Ast/module_state.spl`
  - `decl_get(idx)` (line ~671): added `idx < 0 or idx >= decl_tag.len()` guard,
    returning `make_core_decl(0, -1)` (tag 0 matches no real `DECL_*` constant;
    they all start at 1) instead of indexing out of range.
  - `expr_contains_yield(eid)` (line ~704): guard extended from `eid < 0` to
    `eid < 0 or eid >= expr_tag.len()`.
  - `stmt_contains_yield(sid)` (line ~723): guard extended from `sid < 0` to
    `sid < 0 or sid >= stmt_expr.len()`.
- `src/compiler/10.frontend/desugar/placeholder_lambda.spl`
  - `detect_placeholder_mode(eid)` (line 93), `count_placeholders(eid)` (line
    252), `replace_placeholders(eid)` (line 361): same `eid >= expr_tag.len()`
    guard added.

Category: **unhandled-but-legal state**, not a wrong index computation — the
ids themselves (`eid`/`sid`/`idx`) are the correct ones that were minted at
parse time; what changed underneath them is the arena's current size. The fix
treats "id no longer resolves in the live arena" the same way the pre-existing
code already treated "id is the -1 sentinel": there is nothing there, so
report "not found" / "no yield" / "no placeholder" rather than crash.

## Verification status

**Fix NOT fully empirically verified — honest limitation.** `bin/simple` is
the deployed stage-4 binary; a background loop elsewhere owns rebuilding and
redeploying it, which this session must not fight for the build directory or
CPU, so no rebuild was performed here. However, this binary currently
interprets pure-Simple source **directly from disk on every invocation**
(confirmed empirically: editing the `.spl` source and immediately re-running
`bin/simple lint` on the same target changed observable behavior — see the
`SIMPLE_DEBUG_DECLS`/guard-change probes during investigation) — so the Bug 1
fix *was* exercised live, from source, no redeploy needed:

- Before the fix: `bin/simple lint <trivial .spl file>` crashed at
  `expr_tag[eid]` (`recv=Identifier("expr_tag") idx=Identifier("eid")` via
  `SIMPLE_INTERP_OOB_DEBUG=1`).
- After the fix: that specific crash signature is gone; `bin/simple lint`
  progresses further and now fails at the **different, Bug 2** site
  (`decl_tag[idx]`), confirming Bug 1 is genuinely fixed and was reached on
  every one of the minimal repro files.
- **`bin/simple lint` still does not succeed end-to-end** on trivial input —
  Bug 2 (root-caused above, not fixed) still crashes it. This is a partial,
  honestly-partial fix: it removes one confirmed defect and root-causes a
  second, larger one, but does not unblock the `lint` command by itself.

No full bootstrap, cargo build, or binary redeploy was run or is implied by
this verification.

## Follow-up (not done here)

- Decide whether to fix Bug 2 by (a) hardening the interpreter's cross-module
  global-`var` visibility (Rust seed, `src/compiler_rust/`, out of scope for a
  pure-Simple change and for this task), or (b) wiring the existing
  `SIMPLE_AST_GEN_CHECK`/`ast_gen_check_index` generation-diagnostics
  machinery (`module_state.spl`, added 2026-07-29) into `decl_get` and the
  ~30 direct `decl_tag[idx]` lint call sites, with an agreed default value for
  "can't resolve this decl" per check, and enabling it by default for the
  `lint` CLI path specifically.
- Re-run `bin/simple lint` on a trivial file after whichever fix lands to
  confirm the command no longer crashes at all.
