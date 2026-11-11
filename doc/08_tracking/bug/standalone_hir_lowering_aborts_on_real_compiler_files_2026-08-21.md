# Standalone parse+lower aborts on real compiler files (`split` on i64)

Date: 2026-08-21
Reporter: agent A5+Y2 (Any hardening)
Status: FIXED 2026-11-11 (lane p3-comp9) — root-cause fix 2a7a98dafd34 is an ancestor of
the release tip; regression pin
test/01_unit/compiler/hir/standalone_lowering_real_compiler_files_spec.spl passes 2/2 on
the tracked seed (46fe8f6b6def, interpreter, no-cache). See dated addendum below.

## Symptom

Lowering a real compiler source file to HIR outside the driver — i.e.
`parse_full_frontend(...)` followed by `HirLowering.lower_module(...)` — aborts
the whole process:

```
error: semantic: method `split` not found on type `i64` (receiver value: 32)
```

No caller code is on the stack; the failure is inside the seed's own
parse/lower path.

## Reproduce

```simple
use compiler.frontend.{parse_full_frontend}
use compiler.common.config.{Logger}
use compiler.hir.hir_lowering.*
use compiler.hir.hir_lowering.module_surface_types.{ModuleSurfacesByName}
use compiler.hir.hir_types.{HirModule}

fn probe_run(path: text) -> i64:
    val content = rt_file_read_text(path) ?? ""
    val pm = parse_full_frontend(content, path, "m", Logger(level: 0))
    var lowering = hirlowering_for_module("", ModuleSurfacesByName.empty())
    val hm: HirModule = lowering.lower_module(pm)
    hm.functions.len()
```

- `src/compiler/00.common/assurance/policy_names.spl` → lowers fine.
- `src/compiler/00.common/assurance/unsafe_capabilities.spl` → aborts as above.

The probe contains no `split` call of its own, which is how the failure was
attributed to lowering rather than to the caller.

Two other standalone-lowering limits were observed in the same session and are
probably the same family: a fixture containing an `enum` plus an enum-literal
construction aborts with `undefined field 'symbol': cannot access field on value
of type 'nil'`, and a fixture containing a `struct` aborts with
`class HirFunction has no field named is_generic_template`.

## Consequence

Any tool that wants typed HIR for one file at a time — the Any-escape census
(`scripts/check/check-any-escape-census.shs`), and any future per-file semantic
audit — cannot process the compiler's own sources in a single process: one bad
file kills the run.

## Current mitigation, not a fix

The census invokes the driver ONE PROCESS PER FILE and classifies an aborted
file as UNANALYZABLE — counted, named in the verdict, and never counted as
clean. That bounds the blast radius; it does not make the file analyzable. The
unanalyzable count is part of the recorded baseline so it cannot drift silently.

## Addendum 2026-11-11 — P3 comp9 lane triage (worktree simple-p3-comp9-20261111, base 77be2266752d)

**Verdict: FIXED.**

- Root cause: the `split`-on-`i64` abort was traced same-day (2026-08-21) to a
  parser local `arm_body_flat: [i64]` in `src/compiler/10.frontend/core/parser_stmts.spl`
  shadowing the `[text]` module global of decl_nodes; the seed interpreter's
  mutating-method write-through copied the local's ints into the global by NAME, so the
  next `arm_body_flat[idx].split(",")` ran on an `i64`. Fix commit `2a7a98dafd34`
  ("fix(seed,frontend,driver): stage1 build stall — ... parser local shadowed a module
  global (split-on-i64 abort) ...") renamed the local and made the write-through skip
  `env.is_local`. Verified an ancestor of the lane base (77be2266752d), not merely of
  the filing-time main.
- Regression pin already in tree:
  `test/01_unit/compiler/hir/standalone_lowering_real_compiler_files_spec.spl`
  (header cites this bug doc; landed via merge 9e7e7a526ed, PR #7597). It runs the
  exact historical repro — `parse_full_frontend` + `HirLowering.lower_module` on
  `src/compiler/00.common/assurance/unsafe_capabilities.spl` (the historical trigger,
  "same-content copies at other paths always worked; this exact path did not") plus the
  `policy_names.spl` control.
- Behavioral evidence (tracked seed bin/simple.exe @ 46fe8f6b6def,
  `SIMPLE_LIB=src ... test ... --mode=interpreter --no-cache`):
  `standalone_lowering_real_compiler_files_spec.spl` → outcome=OK, executed=2 passed=2
  failed=0. The process-abort class of bug cannot fake green: completion is the signal.

Residual (left open as follow-up, not blocking this row): the two sibling limits
observed in the same session — an enum + enum-literal fixture aborting with
`undefined field 'symbol'`, and a struct fixture aborting with
`class HirFunction has no field named is_generic_template` — have no exact fixture
text recorded in this doc, so they could not be re-probed here. They were filed as
"probably the same family", which the split-on-i64 root cause does not obviously
explain; if they reproduce, file them as their own rows.

Disposition: FIXED. Header flipped OPEN → FIXED 2026-11-11 (lane p3-comp9).
