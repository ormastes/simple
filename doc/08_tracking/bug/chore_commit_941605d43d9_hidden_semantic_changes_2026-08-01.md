# Audit: semantic compiler changes hidden inside "chore" commit `941605d43d9`

**Date:** 2026-08-01
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
measured and BOTH CLEARED — see "Follow-up verdicts" at the end
**Commit:** `941605d43d930af46fa3a18084f5cce9be1972e6`
**Subject:** `chore: sync evidence showcase and parser framework lane updates`
**Authored:** Sat Aug 1 03:26:31 2026 +0000 — ancestor of HEAD (`ca8ff9e003d`)
**Parent:** `29ddb89dd3c`
**Scope:** 59 files, +4222 / -287

## Why this audit exists

Two separate investigations on 2026-08-01 each stumbled onto a real semantic
compiler change inside this commit *by accident*: the interpreter implicit-self
guard, and the `peek_indented_operator_continuation` parser change that
regressed multi-line operator chains tree-wide when first built. Neither is
mentioned in the subject or anywhere in the commit message. This audit
enumerates the rest **before a bootstrap compiles them**.

**Headline: 20 behaviour-capable changes. 5 of them are Rust seed changes that
have NEVER RUN and will first take effect on the next `cargo` seed rebuild.**

## Seed-compilation status (decisive evidence)

The shipped seed is `src/compiler_rust/target/bootstrap/simple`
(154,095,400 bytes, mtime `2026-08-01 03:43:05`).

The mtime is **newer** than the commit and is therefore *not* evidence the
changes are compiled in — it is the timestamp of the byte-identical restore a
parallel lane performed after an accidental rebuild. Content probes settle it:

| Probe string | In seed? |
|---|---|
| `creates a new local and leaves` (new, `node_exec.rs`) | **ABSENT** |
| `is implicit only in the parameter list` (new, `node_exec.rs`) | **ABSENT** |
| `cannot assign to const` (pre-existing, same function) | present |
| `peek_through_newlines_and_indents` (pre-existing, `parser_helpers.rs`) | present |

Pre-existing format strings from the *same* crates are present while the new
ones are absent ⇒ **the seed binary predates this commit. All five Rust changes
below are uncompiled.**

Do not rebuild the seed to check this. Note also that a plain
`cargo build --profile bootstrap -p simple-driver` DROPS LLVM (154 MB → 32 MB).

## Ranked by blast radius (highest first)

### 1. `src/compiler_rust/parser/src/parser_helpers.rs:458` + `expressions/binary.rs:46,387` — additive-operator line continuation now requires indent
**UNCOMPILED. Fires on the next seed rebuild. Highest blast radius in the commit.**

New `peek_indented_operator_continuation()` (50 lines) is a variant of
`peek_through_newlines_and_indents()` that returns the next meaningful token
**only if at least one `Indent` was crossed**. `parse_binary_multi!` gains an
`@impl` arm parameterised on the peek function, and `parse_term` (the `+`/`-`
level, and *only* that level) is switched to the `indent_required` variant.

Intent (per the in-diff comment): a same-indent `-1` line after `return 15` is
a new statement, not a continuation; the old behaviour glued them into
`return (15 - 1)` == 14. See
`doc/08_tracking/bug/if_chain_last_arm_returns_previous_value_2026-07-28.md`.

Blast radius: **every `+`/`-` binary expression in the entire tree that spans a
line break.** This is exactly the change already observed to regress multi-line
operator chains tree-wide on first build. Any `+`/`-` continuation written at
the *same* indent as its left operand — a legal and common formatting — silently
stops being a continuation and becomes a separate statement. Silent wrong
results, not parse errors. Note the guard returns `None` on `Dedent`/`Eof` and
caps lookahead at 100 tokens; `*`/`/` and all other levels are untouched.

**No test.** Nothing in the commit exercises leading-operator continuation at
either indentation.

### 2. `src/compiler_rust/compiler/src/interpreter_eval.rs:1531` — glob-imported `main` no longer enters `functions`/`env`/`MODULE_GLOBALS`
**UNCOMPILED. Not mentioned by either prior investigation. Second-highest radius.**

Previously a glob-imported `main` was excluded only from the flat `functions`
map. Now it is `continue`d out of the loop entirely, so it also never reaches
`env` or `MODULE_GLOBALS`. Rationale: it leaked into the `entry_main` /
`main_to_run` auto-invoke fallback and into the final
`env.get("main") -> as_int()` exit-code fallback (failing with
"cannot convert function to int").

Blast radius: **every `use mod.*` in the AST interpreter.** A named import
(`use mod.{main}`) is explicitly still allowed through — that asymmetry is
deliberate but undocumented outside this diff. Any code that relied on a
glob-imported `main` being callable by bare name now gets an unresolved name.

**No test.**

### 3. `src/compiler_rust/compiler/src/interpreter_eval.rs:1563` — module dict no longer bound under the reserved name `main`
**UNCOMPILED. Not mentioned by either prior investigation.**

New `is_path_derived_main` guard: when `binding_name == "main"` **and** the
import target is `Glob` or `Group(_)`, the module `Dict` is no longer inserted
into `env` or `MODULE_GLOBALS` under that name. Reason: for Glob/Group the
binding name is derived from the last path segment (the file happening to be
called `main.spl`), not chosen by the importer, and it collides with the
`env.get("main") -> as_int()` exit-code fallback — failing every such import
with "cannot convert dict to int". `Single`/`Aliased` imports are untouched.

Blast radius: any spec doing `use compiler.tools.lint.main.{...}` — there are
~10 such spec files in `test/`. Qualified access `main.Foo` after a Glob import
of a `main.spl` now resolves to nothing.

**No test.** (Related historical doc:
`doc/08_tracking/bug/interp_lint_main_then_frontend_dict_to_int_2026-07-28.md`.)

### 4. `src/compiler_rust/compiler/src/interpreter/node_exec.rs:569` — implicit-self field assignment is now a hard error
**UNCOMPILED. This is the change investigation #1 found.**

In `exec_assignment`, when `is_first_assignment` and `env.get("self")` is an
`Object` whose `fields` contain `name`, the interpreter now returns
`INVALID_ASSIGNMENT` instead of minting a fresh shadowing local. Message:
``invalid assignment: `{name}` is a field of `{class}`; a bare `{name} = ...`
creates a new local and leaves `self.{name}` unchanged``.

Blast radius: **every method body in the tree that assigns a bare field name.**
Previously a silent no-op; now a hard compile error. Aligns the AST interpreter
with HIR ("unresolved name"), MIR ("assignment target has no local binding"),
native codegen, and the pure-Simple interpreter ("undefined variable") — so it
is a *correctness* improvement, but it converts silent-wrong into
fail-to-build, and the count of affected sites is unknown until it runs.

**Has tests** — the only Rust change in this commit that does:
`test/01_unit/compiler/interpreter/implicit_self_field_assign_spec.spl` (new,
134 lines) and an 80-line update to
`test/.../interp/implicit_self_assignment_characterization_spec.spl`.

### 5. `src/compiler/70.backend/backend/vulkan_backend.spl:1002,1012,1029,1039` — four match arms changed from tail-expression to explicit `return`
**Live now (pure-Simple compiler path). Semantic, not cosmetic.**

Four functions — `shared_array_operand_id`, `shared_array_operand_size`,
`shared_pointer_operand_id`, `storage_buffer_operand_id` — had the shape
`if d.has(local.id): d[local.id] else: 0` as the tail of a `case` arm. Each is
rewritten to `if d.has(...): return d[...]` / `return 0`.

If the inline `if/else` tail-expression was not producing a value in a match arm
(the shape the `if_chain_last_arm_returns_previous_value` bug describes), these
four functions were returning wrong IDs/sizes, meaning **the Vulkan/SPIR-V
codegen backend was emitting wrong shared-array and storage-buffer bindings**.
Nothing in the commit message says the Vulkan backend was touched.

**No test.** No Vulkan/SPIR-V spec appears in this commit.

### 6. `src/lib/nogc_async_mut/io/tls_handshake.spl:456` — ALPN extension read reverts a documented workaround to `slice()`
**Live now. Cross-file coupled change; correctness depends on #7.**

A deliberate byte-by-byte copy loop, with a comment citing
`doc/08_tracking/bug/byte_at_reads_zero_from_slice_result_2026-07-28.md`
explaining that `byte_at()` reads zeros out of a `slice()` result, is deleted
and replaced with `return slice(extensions, pos, pos + ext_data_len)`.

`slice`/`byte_at` here resolve through `use std.tls.utilities.{...}` →
`_TlsUtilities/hex_encoding.spl`, i.e. the file changed in #7. **This revert is
only safe because of #7 — and #7's own root cause is still OPEN** (see #7). If
the annotation fix is incomplete on any backend, ALPN negotiation silently
returns an all-zero extension and always lands on `""` — the exact regression
the deleted comment was guarding against. The bug doc was flipped to
`**Status:** Fixed 2026-08-01` in this same commit.

**No test for the ALPN path itself** (the new spec covers `_TlsUtilities`, not
`find_alpn_extension_data`).

### 7. `src/lib/nogc_sync_mut/tls/_TlsUtilities/hex_encoding.spl:330,343` — type annotations added to `byte_at` and `slice`
**Live now. The enabling fix for #6, sitting on an OPEN root cause.**

`fn byte_at(data, index):` → `fn byte_at(data: [i64], index: i64) -> i64:` and
`fn slice(data, start, end):` → `fn slice(data: [i64], start: i64, end: i64) -> [i64]:`,
plus annotations on three locals.

These are not cosmetic. The commit also files
`doc/08_tracking/bug/untyped_fn_result_erased_to_zero_2026-08-01.md`
(**Status: Open**, Severity High): an untyped function's trailing-expression
result is erased to `0`, and untyped *params* with a declared return type give
back the raw tag-boxed word (`value << 3`). Annotating is the workaround, not
the fix. **Any other untyped function in the tree has the same defect** — this
commit fixes exactly two of them.

**Has a test:** `test/.../tls/tls_utilities_slice_byte_at_spec.spl` (new, 48
lines) plus an 8-line update to `tls_utilities_negative_index_guard_spec.spl`.

### 8. `src/lib/nogc_sync_mut/tls/_TlsUtilities/text_ops.spl:294,302` — two placeholder stubs replaced with real implementations
**Live now. Propagates across four library tiers.**

- `fn len(collection):` returned the literal `0` ("Placeholder - should return
  length") → now `fn len(collection) -> i64: collection.len()`.
- `fn append(list, item):` returned `list` unchanged ("Placeholder - should
  append item") → now actually `push`es and returns the new list.

Any TLS code path that called these was silently getting `0` and a
never-growing list; it now gets real values. That is a behaviour change in both
directions depending on what downstream logic was tuned against the stubs.
Re-exported through `gc_sync_mut`, `nogc_async_mut`, and `gc_async_mut`
`_TlsUtilities/text_ops.spl` facades — so the change reaches all four tiers.

Note `len`'s parameter is **still untyped** (`fn len(collection) -> i64`), which
per the bug filed in #7 is precisely the "declared return, untyped param" shape
flagged as returning a raw tag-boxed word on indexed reads.

**No test.**

### 9. `src/compiler/90.tools/lint/main.spl:11` + `_LintMain/entry_and_fixes.spl:236` — lint CLI entry renamed `main` → `lint_main`, wildcard re-export narrowed to an explicit list
**Live now. Public API surface change of the lint facade.**

`export use ..._LintMain.entry_and_fixes.*` is replaced by an explicit
11-symbol group import, and `fn main() -> Int` becomes `fn lint_main() -> Int`.
Rationale in-diff: a library facade re-exporting a CLI `main` is the confirmed
trigger shape for the test-runner's phantom file-level-failure defect
(`doc/08_tracking/bug/test_runner_wildcard_imported_main_phantom_failure_2026-08-01.md`).

Verified: no consumer outside `90.tools/lint/` referenced `main` from this
facade, and the explicit list preserves the previous export surface, so this
appears safe. But it is an **irreversible rename of a public symbol landed under
a chore label**, and it is load-bearing for #10. Any *new* wildcard-added symbol
in `entry_and_fixes.spl` will now silently fail to export until the list is
updated by hand.

**No test** for the export surface itself (the existing lint specs import
`Linter`/`lint_cli_source` by name and keep working).

### 10. `src/os/smf/dynsmf_session.spl:86` — dynSMF manifest entry for `lint_tool` changes its exported symbol
**Live now. Downstream of #9; a stale runtime artifact breaks silently.**

`exports: ["main"]` → `exports: ["lint_main"]` for the `lint_tool` entry
(`build/dynsmf/lint_tool.smf`). Correct given #9, but any **already-built**
`.smf` on disk still exports `main`, so the manifest and the artifact disagree
until the SMF is regenerated. That mismatch surfaces as a lazy-load failure at
runtime, not at build time.

**No test.**

### 11. `src/lib/gc_async_mut/gpu/engine2d/engine.spl:27,2089,2103` — two new public `Engine2D` methods plus a widened import
**Live now.**

`draw_gradient_rect_stops(...)` and `draw_radial_gradient_rect_stops(...)` added
to `class Engine2D with DrawIrRenderTarget`, dispatching across the
virtio-gpu / baremetal / cuda / emu backends; the `backend_emu` import gains
`emu_draw_linear_gradient_stops, emu_draw_radial_gradient_stops`.

Verified both callees exist: `backend_emu.spl:658` and `:698`. Additive, so low
regression risk — but note the virtio-gpu and baremetal arms bind `vg`/`bm` and
then ignore them, passing `self.backend` instead (copied from the neighbouring
`draw_radial_gradient`; consistent with the existing pattern, likely a
pre-existing wart rather than new).

**No test** for the two new methods.

### 12. `src/lib/common/ui/draw_ir_transform.spl` — DELETED (145 lines)
**Live now. Verified safe.**

Repo-wide search for `draw_ir_transform` returns **zero** references in `src/`
or `test/`. No dangling importer. Recorded here only because deleting a library
file under a chore label is invisible in the subject line.

### 13. `scripts/check/check-dangling-references.shs:212,234` — the awk indexer now treats `export use m.{A as B}` as DEFINING `B`
**Live now. Changes what a repo-wide verification gate reports.**

New `in_export_use` state machine (multi-line-aware) emits `B` as a definition
for every `A as B` alias inside an `export use` block; a plain `use m.{A as B}`
still contributes nothing. Fixes 5 false `NvfsHostedDriver` findings
(`doc/08_tracking/bug/..._alias_reexport_false_positive_2026-07-28.md`, updated
in this commit). `--help` line range bumped 66→71.

Blast radius: this is a **fail-open change to the verification layer** — it can
only *remove* findings, never add them. Given the standing
`repo_verification_layer_is_fail_open` history, a gate that got quieter under a
chore label deserves the note. The awk `match()` on
`NAME[ \t]+as[ \t]+NAME` will also match the literal word `as` appearing between
two identifiers anywhere inside an `export use` block.

**No test** (no spec covers this script's awk indexer).

### 14. `scripts/check/codex-run-guard.shs:104` — rollout-file resolution gains a content-scanning fallback
**Live now. Tooling only, no compiler impact.**

The single `find -name "rollout-*$SID*.jsonl"` is replaced by a
`resolve_rollout()` function: first a widened filename glob (`*${_sid}*.jsonl`,
note the `rollout-` prefix is now dropped), then a fallback that `grep -Fq`s
every `rollout-*.jsonl` under `$HOME/.codex/sessions` for
`"session_id":"$SID"` or `"id":"$SID"`.

The widened glob can match non-rollout `.jsonl` files, and the fallback is an
O(sessions) full-content scan on every guarded resume. Affects the poison-rollout
refusal path only.

**No test.**

### 15–20. New, currently inert modules (no non-test importers)

Large additions that compile-check but are not yet reachable from product code.
Listed for completeness — they enter the build graph on the next full build and
so can break it, but they cannot change existing behaviour.

| # | Path | Lines | Only importer |
|---|---|---|---|
| 15 | `src/lib/common/ui/gpu_web_event_model.spl` | +802 | `test/01_unit/lib/common/ui/gpu_web_event_model_spec.spl` |
| 16 | `src/lib/gc_async_mut/gpu/browser_engine/gpu_web/dom/{__init__,dom_arena_build,dom_arena_types}.spl` | +867 | `test/01_unit/lib/gpu_web/ingest/dom_arena_spec.spl` |
| 17 | `src/lib/common/structural/parse/{__init__,contracts,dialect,model,output_plan}.spl` | +396 | `test/03_system/app/compiler/feature/parser_framework_spec.spl` |
| 18 | `src/lib/nogc_async_mut/structural/parse/{__init__,action_sink,auto_profile,incremental,parallel_lex,runtime,scalar,structural_index}.spl` | +263 | same as above |
| 19 | *(deleted)* `test/01_unit/compiler/lint/coll007_probe_spec.spl` | −27 | — |
| 20 | `test/01_unit/lib/layout/web_layout_incremental_oracle_spec.spl` | +238 | new spec, no src change |

#19: a test was **deleted** in this commit. Deleting a spec under a chore label
removes coverage silently; confirm the replacement
(`test/01_unit/compiler/lint/collection_array_rebuild_spec.spl`, present in the
working copy) actually covers the same lint before treating this as a wash.

## Summary tables

### Uncompiled — first take effect on the next Rust seed rebuild

| # | File:line | Change |
|---|---|---|
| 1 | `parser_helpers.rs:458`, `binary.rs:46,387` | `+`/`-` continuation now requires indent |
| 2 | `interpreter_eval.rs:1531` | glob-imported `main` fn suppressed entirely |
| 3 | `interpreter_eval.rs:1563` | path-derived `main` module dict not bound |
| 4 | `node_exec.rs:569` | implicit-self field assign is now a hard error |

A bootstrap compiles all four at once. #1 is the one already observed to regress
multi-line operator chains tree-wide; #2 and #3 change module-import semantics
for every `use x.*` in the AST interpreter and were found by neither prior
investigation.

### Behaviour-capable changes lacking any test

15 of 20: #1 (parser continuation), #2 and #3 (interpreter import semantics),
#5 (Vulkan backend), #6 (ALPN slice revert), #8 (text_ops stubs), #9 (lint
export surface), #10 (dynSMF manifest), #11 (Engine2D gradient stops), #13
(dangling-reference gate), #14 (codex run guard), and the five inert new
modules #15–#18 which have spec coverage but no product caller.

Only #4 (implicit-self guard) and #7 (`_TlsUtilities` annotations) ship with
tests.

### Open root causes this commit works around rather than fixes

- `doc/08_tracking/bug/untyped_fn_result_erased_to_zero_2026-08-01.md` —
  **Open, High.** #7 annotates two functions; every other untyped function in
  the tree still has the defect.
- `doc/08_tracking/bug/test_runner_wildcard_imported_main_phantom_failure_2026-08-01.md`
  — #9/#10 rename around it.

## Recommendation

Before the next bootstrap, decide deliberately about #1. It is the single change
in this commit with tree-wide silent-wrong-result potential, it has no test, and
it is already known to have regressed multi-line operator chains once. #2 and #3
should get specs before they are compiled, since they change import semantics
for every glob import in the AST interpreter.

Do not let this land unremarked again: a semantic parser, interpreter, or
codegen change belongs in its own commit with a `fix:`/`feat:` subject, never
inside a `chore: sync` sweep.

## Follow-up verdicts 2026-08-01 — the two bootstrap-gating changes

A bootstrap redeploy was held because it would have compiled 20 first-time
changes at once, making any failure unattributable. The two with the largest
blast radius were measured. Both cleared; the hold is lifted on audit grounds.

### vulkan_backend.spl return-shape — INERT, safe

Sole source change in the commit. Four identical edits at lines 999 / 1008 /
1026 / 1035 (`shared_array_operand_id`, `shared_array_operand_size`,
`shared_pointer_operand_id`, `storage_buffer_operand_id`), each rewriting
`case Copy(local) | Move(local):` from an implicit tail expression
`if d.has(local.id): d[local.id] else: 0` into `if d.has(local.id): return
d[local.id]` + `return 0`, while LEAVING the `case _:` arms as implicit tail
`0`. So each `match` now mixes an explicit-`return` arm with an implicit-value
arm — that mix was the actual risk, since a nil-instead-of-0 fallback would
flip callers' `== 0` / `!= 0` guards into wrong bindings or spurious errors.

Emitted SPIR-V is BYTE-IDENTICAL with and without the hunk: both hash
`0d00845b9dd51af641cd92d84580aa19`, diff empty. Measured with a standalone
driver importing the real `VulkanCodegenBackend` and calling `compile_kernel`
across four scenarios covering all four functions (Workgroup shared GEP via
Copy; the same via Move, i.e. the second or-pattern alternative; a
storage-buffer descriptor kernel; and a Const base hitting the wildcard arm).
No `use std.spec`, deliberately — that would have demoted the driver to the
interpreter and produced a false green.

Non-vacuity proven twice: neutering `shared_array_operand_id`'s hit path to
`return 0` flips both shared scenarios to "base must come from a StorageBuffer
argument or GpuSharedAlloc"; and neutering the UNTOUCHED `case _:` arm of
`storage_buffer_operand_id` from `0` to `123` changes the wildcard error to
"immutable StorageBuffer base cannot produce a mutable GEP destination",
proving the implicit-tail wildcard arm is live, exercised, and still yields 0
under the mixed-arm shape.

Note for anyone re-checking: `compile --native` REJECTS `PatternMatch` outright
("constructs that require the interpreter"), so these functions cannot take a
standalone-native path in the seed at all.

### interpreter_eval.rs glob-import `main` hunks — SAFE to compile

Both hunks exist to protect one line, the exit-code fallback at
`interpreter_eval.rs:1845` (`env.get("main").unwrap_or(Int(0))` -> `.as_int()?`),
reached only when the entry file declares no `main`. Hunk A (:1531) `continue`s
a glob-imported `main` FUNCTION out of `env`/`MODULE_GLOBALS` as well as the
flat `functions` map; hunk B (:1563) stops binding the module Dict under `main`
when the binding name is merely path-derived (i.e. the file is `main.spl`).

They only REMOVE an `env` key whose sole present effect is to make the program
die at :1845. Every affected import is already fatally broken today — measured
on the real module, not a toy: `use compiler.tools.lint.main.{Linter}` prints
`linter ok` then exits 1. The withdrawn capabilities have ZERO consumers (every
`main.` hit in the tree is a `".../main.spl"` path string or a comment), and
the one live glob site, `src/app/wm_compare/main.spl` imported by
`_WmCompareMain/run_modes.spl`, declares its own `fn main` at :443 — so hunk A
removes a collision, not a capability.

Corrections to this audit's own earlier text: the blast radius is not ~10 specs
but **62 canonical spec files** plus production `src/` (`src/app/io/`,
`src/app/cli/`, six `src/compiler/90.tools/lint/_LintMain/*.spl`).

Caveat, recorded not buried: hunk B's `Single`/`Aliased` carve-out leaves
`use pkg.main` still failing with `cannot convert dict to int`. The fix is
INCOMPLETE, not wrong. And the A-side evidence was measured against the
preserved pre-commit seed binary, so it controls for these two hunks plus every
other uncompiled change in this commit — including the parser continuation
change. If a later cargo run contradicts these numbers, that confound is the
first place to look, not the hunks.

### Still uncompiled

The remaining Rust seed changes in this commit have still never run. Two of
them now have their own entries: the parser continuation regression (fixed in
`fba46571d6a`) and the implicit-self hint. The rest await the next seed
rebuild, and this audit remains the checklist for attributing any failure.
