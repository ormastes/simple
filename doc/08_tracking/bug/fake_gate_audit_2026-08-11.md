# Fake-gate audit — specs that cannot detect a violation (2026-08-11)

**Status:** OPEN — inventory complete, 1 fixed, 1 root cause proven, remainder filed.

A *fake gate* is a spec that is structurally incapable of failing, or that
measures something other than what its name claims. It is worse than no spec:
it is cited as evidence.

Three specimens were found by accident on 2026-08-10 (`cli_help_alignment_spec`
literal-vs-literal; `multiarch_audit_report` hardcoded output; four interpreter
source-grep specs). This audit searched for the rest systematically.

Detector: `scripts/check/` has no gate for this yet — see "Follow-up" below.
The scan used for this pass is recorded in the Method section.

---

## Method, and a correction to the first-pass numbers

A first-pass grep for `expect(` / `assert_` / `to_equal` reported **1,099**
assertion-free spec files. **That number is wrong** and is recorded here so it
is not re-quoted. Three assertion idioms in this tree do not match it:

- the **paren-less** form `expect path.ends_with(".spl") == true`
- `check(...)` / `check_msg(...)` (165 + 83 uses in the sampled subset alone)
- `should_equal(...)` / `should_contain(...)` / `should_be_true(...)`

The paren-less form was **verified to be a real assertion**, not a no-op: a
probe spec asserting `expect 1 == 2` and `expect "hello.spl".ends_with(".ZZZ")
== true` returned `Results: 1 total, 0 passed, 1 failed`, exit 1. It fails
correctly. Any audit that treats `expect X == Y` as a fake gate is wrong.

Corrected scan (all idioms, excluding `test/fixture*`):
**125 spec files contain no assertion of any kind; 56 of those declare `it`
blocks** (28 unique + their `test/unit` mirrors).

---

## Pattern inventory

### P1 — Literal-vs-literal (assert a property of a string the spec just wrote)

The confirmed specimen shape. **`test/01_unit/app/tooling/command_dispatch_spec.spl`
is the largest instance found and is the one fixed in this change.**

| file | lines | what it purported to test | what it actually tested |
|---|---|---|---|
| `test/01_unit/app/tooling/command_dispatch_spec.spl` (+ `test/unit/` mirror) | 46-98 (was 39-91) | `describe "Simple app files exist"` — 12 `it` blocks, one per migrated command | Each bound `val path = "src/app/<tool>/main.spl"` then asserted `path.ends_with(".spl")`. True by construction for any string. **Never touched the filesystem.** |

The rest of that same file (~100 further `it` blocks: guard naming, flag
detection, path resolution) is the *same* shape — it authors a list of strings
and asserts properties of its own literals. It measures no product code. Only
section 1 is fixed here because only section 1 made a checkable claim about the
repository; the remainder needs a redesign, not a patch. **Filed, not fixed.**

### P2 — Kill-switch constant (whole spec gated behind a `false`)

New pattern, not in the original three. A module-level or block-level constant
is set to `false` and every assertion sits behind `if <const>:`, with an `else`
that prints `SKIP`. Permanently green; the runner reports the `it` blocks as
passing examples.

| file:line | evidence |
|---|---|
| `test/02_integration/compiler/core_interpreter_intensive_spec.spl:11` (+ `test/integration/` mirror) | `val _can_run = false`; 6 `it` blocks; **imports commented out**; calls `run_expr_ok` / `run_ok` which are **never defined anywhere in the file or repo** |
| `test/02_integration/compiler/c_backend_e2e_spec.spl:15` (+ mirror) | `val _can_run = false` |
| `test/01_unit/app/tooling/coverage_spec.spl:20,30,134` (+ mirror) | `val enabled = false` ×3 |
| `test/01_unit/app/tooling/startup_spec.spl:99` (+ mirror) | `val enabled = false` |
| `test/01_unit/compiler/backend/stub_elimination_spec.spl:35` (+ mirror) | `val enabled = false` |
| `test/01_unit/lib/gpu/engine2d/ffi_dispatch_spec.spl:47` (+ mirror) | `val available = false` |
| `test/01_unit/app/mcp_unit/logger_rotation_spec.spl:29` (+ mirror) | `val logger_available = false` |
| `test/03_system/feature/usage/cli_args_file_spec.spl:87` (+ `test/feature/` mirror) | `val prefetch_enabled = false` |
| `test/05_perf/pure_dl_perf.spl:76` (+ `test/perf/` mirror) | `val ffi_available = false  # Set to true when FFI is actually available` |

**11 unique files, 22 sites with mirrors.** A broader `print "SKIP"` scan
matched **143 files** — that superset needs triage.

### P3 — Scaffold bodies (`pass` with the assertion in a comment) — SSDOC-ORA-001

56 spec files declare `it` blocks and contain **zero** assertions. The dominant
shape is a `pass` body with the intended oracle commented out directly above it:

```
it "converts to text":
    # SimdElementType.I32.to_text() == "i32"
    pass
```

Largest instances (`it`-block count, unique file — each also has a `test/unit`
mirror):

| its | file |
|---|---|
| 61 | `test/01_unit/compiler/native/simd_check_spec.spl` |
| 61 | `test/01_unit/app/test_runner/quickcheck_spec.spl` |
| 61 | `test/01_unit/app/interpreter/ast_convert_expr_spec.spl` |
| 55 | `test/01_unit/compiler/semantics/const_keys_spec.spl` |
| 41 | `test/01_unit/compiler/macros/macro_check_spec.spl` |
| 31 | `test/system/coupling_analysis_spec.spl` |
| 25 | `test/01_unit/compiler/mir/mir_opt_benchmark_spec.spl` |
| 15 | `test/03_system/feature/usage/gc_managed_default_spec.spl` |
| 8 | `test/03_system/feature/usage/context_blocks_spec.spl` |
| 7 | `test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl` |

That is **≈380 green "examples" that assert nothing**, in the top 10 files alone.

### P4 — Source-grep-as-behaviour

246 spec files (excluding fixtures/mirrors) read source with
`rt_file_read_text` and assert only `to_contain` / `index_of` on the text. Not
all are illegitimate — a *structural regression pin* is a valid artifact when it
says so. The illegitimate case is one that stands in for behavioural coverage
that is believed to exist.

**The four named interpreter specs — root cause now proven, see below.**

---

## Root cause behind the four interpreter grep-specs — MEASURED, not assumed

`evalops_export_and_text_at_spec.spl`, `dict_literal_dispatch_spec.spl`,
`text_byte_at_dispatch_spec.spl` and `option_result_method_dispatch_spec.spl`
are `rt_file_read_text` + `to_contain`. Three of the four carry an explicit
"ENGINE NOTE" saying a behavioural version *cannot* be written because a spec
that imports the interpreter fails to compile.

**That excuse was tested and is TRUE.** A minimal probe:

```
use compiler.frontend.core.interpreter.{core_interpret_expr, val_get_int}
describe "probe": 
    it "evaluates 1 + 2 * 3":
        expect(val_get_int(core_interpret_expr("1 + 2 * 3"))).to_equal(7)
```

→ `error: semantic: variable 'cache_initialized' not found`
→ `error: test-runner: spec executed nothing (zero-examples)`, exit 1.

This is the known cross-module module-level-global defect (`value.spl`'s
globals). It is a **compiler defect, not a spec defect**, and it is the reason
these four specs are structural. They should NOT be rewritten as behavioural
specs until it is fixed — doing so produces a spec that cannot load at all.

Two corrections to the original report of specimen 3:

1. `val_struct_upsert_field` is **not** an uncalled function. It has three live
   call sites (`_EvalOps/access_literal_assign_eval.spl:656`,
   `_EvalOps/call_method_eval.spl:661`, `eval_stmts.spl:314`), a definition at
   `value.spl:288` and an export at `__init__.spl:169`. It "never runs" only in
   the sense that the whole pure-Simple interpreter is unreachable from the
   spec harness — which is the finding below.
2. `text_byte_at_dispatch_spec.spl` and `option_result_method_dispatch_spec.spl`
   are **not** purely structural: each opens with a genuinely behavioural `it`
   block that executes on the host engine. Only `dict_literal_dispatch_spec.spl`
   is 100% source-grep with no behavioural block and no engine note.

### The finding that matters

**The pure-Simple core interpreter has ZERO executing test coverage.** The only
spec that drives it (`core_interpreter_intensive_spec.spl`) is kill-switched to
`false` with undefined helpers, and any spec that tries to drive it directly
dies on `cache_initialized`. Every "interpreter" spec in `test/01_unit/compiler/
interpreter/` is a source-text pin standing in for that void.

Unblock condition: fix cross-module module-level global initialisation so an
importer of `compiler.frontend.core.interpreter` can call `core_interpret_expr`.

---

## Fixed in this change

### `test/01_unit/app/tooling/command_dispatch_spec.spl` (+ byte-identical `test/unit/` mirror)

The 12 tautological `it` blocks are replaced by one that reads the filesystem,
carries a manual-first docstring, a `# @req` tag, and **two in-spec controls**
so it cannot pass vacuously:

- negative control: `assert_false(app_entry_exists("src/app/__no_such_app__/main.spl"))`
- positive control: `assert_true(app_entry_exists("src/app/lint/main.spl"))`
- non-vacuity: `assert_equal(checked, 12)`

**It is RED, and that is the correct artifact** — it immediately exposed a real
drift the fake gate had hidden for its entire life:

```
✗ has a main.spl on disk for every command dispatch routes to Simple
  assert_equal failed: expected , got src/app/formatter/main.spl src/app/depgraph/main.spl
Results: 100 total, 99 passed, 1 failed
```

`src/app/formatter/` **does not exist at all**, and `src/app/depgraph/` exists
but has **no `main.spl`** (only `render_adapter.spl`, `test_*.spl`). The spec's
own header still claims "Migrated Commands (12 total)". Per
`.claude/rules/testing.md` this is left RED and filed rather than weakened.

**Fail-closed proof:** both controls pass (so the probe discriminates present
from absent in both directions) while the real assertion fails naming exactly
the two genuine misses. Two failed injection attempts are recorded below because
they are themselves measurement traps worth keeping.

---

## Measurement traps hit while doing this audit

1. **A spec can fail for a reason that is not your assertion.** The first run of
   the rewritten spec was RED and was briefly read as "the oracle works". The
   actual message was `semantic: function 'step' not found` — `step()` needs
   `use std.spec.{step}` and the block never reached its assertions. Always read
   the failure *message*, never just the exit code or the ✗.
2. **`use std.spec` / `use std.io_runtime` can blow the daemon budget.** Adding
   either import to this spec turned the whole file into
   `reason=daemon-worker-timeout budget_ms=15191` / `26063` — zero `it` blocks
   run, exit 255. Resolved by using the `rt_file_read_text` extern (no import)
   and plain `# STEP:` comments. **A modern-SSpec rewrite can silently cost you
   the entire file.**
3. **Creating files to inject a violation perturbs the module graph.** Writing
   `src/app/formatter/main.spl` (containing `fn main()`) to force a GREEN made
   the run exit 255 outright — the known wildcard-imported-`main` phantom
   failure. Injection must not add entry points.
4. **The daemon is flaky under load.** Identical invocations produced
   `daemon-worker-timeout` (16s), then `daemon-no-response` (120s), then a
   clean `Results: 100 total`. Re-run before concluding.

---

## Follow-up (not done here)

- **No automated gate exists for any of this.** The five pre-push guards do not
  look at spec content. A sixth guard should fail-close on: a spec file with
  `it` blocks and zero assertions; a module-level `val <x> = false` that gates
  every assertion; and `expect(<literal>).to_equal(<literal>)`.
- Triage the 143-file `print "SKIP"` superset.
- Fix or delete the 56 assertion-free `it`-declaring spec files (SSDOC-ORA-001).
- Redesign the remaining ~100 literal-only `it` blocks in
  `command_dispatch_spec.spl`.
- File the missing `src/app/formatter/main.spl` and `src/app/depgraph/main.spl`
  (or correct the dispatch table's migrated-command list) to clear the new RED.
