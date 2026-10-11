# Any rules (opt-in lints)

Robustness item 7b. Part 7a (PR #2829) made a *written* `Any` distinct from
the parser's fallback and banned it in robust compiled code as a hard error
(`E-ANY-COMPILE-001`). 7b is the warn-first half: three lint families that
name `Any` debt in the compiler's own source before a stage-2 build trips on it.

## What it prevents

| Code | Family | Reports |
|---|---|---|
| `W-ANY-DECL-001` | `written_any_decl` | A written `Any`/`any` in a declaration (parameter, return type, field, `val`/`var`) of a file under `src/compiler/**`. Suggests the concrete type when the initialiser, the returns or the field default show one (`write `i64``). |
| `W-HIR-INFER-003` | `any_fallback_use` | A binding whose type fell back by inference (callee returns an unresolved type or `Any`, untyped `[]`/`{}`, unannotated alias of an `Any` value) used as an arithmetic or comparison operand, passed to a typed parameter, or returned from a typed function. Reported at the use. |
| `W-ANY-USE-001` | `any_receiver_use` | `for` over a value whose type is `Any`. |
| `W-ANY-USE-002` | `any_receiver_use` | A method call on an `Any` receiver. |

`for` over an `any` value and method dispatch on an `any` receiver are known
stage-2 failures: the element/receiver type is erased, so native code has
nothing to dispatch on.

`W-HIR-INFER-003` extends `W-HIR-INFER-001/002` (frontend-diag lane), which
already cover receiver, `for`, index and field uses and report at the
declaration. A binding those codes track is never reported a second time by
`W-ANY-USE-*`.

## How it reports

```
$ SIMPLE_ANY_RULES=warn simple lint src/compiler/x/y.spl
src/compiler/x/y.spl:5:12: warning[W-ANY-DECL-001]: written `Any` in the parameter `a` of `pick`: ...
src/compiler/x/y.spl:17:13: warning[W-HIR-INFER-003]: in `f`: `z` is used as an arithmetic operand, ...
src/compiler/x/y.spl:7:15: warning[W-ANY-USE-001]: in `pick`: `for` iterates over `a`, an `any` value ...
```

Warnings never change the exit code (unless `--deny-all` or a `deny` level).

The rules need a lowered HIR module, which `simple lint` does not build. When
opted in, lint runs `<self> check <file>` with `SIMPLE_ANY_RULES=<mask>` and
relays the report. The same run is available directly:

```
SIMPLE_ANY_RULES=dfr simple check src/compiler/x/y.spl    # d decl, f fallback, r receiver
```

`check` needs a worker binary (`bin/release/<triple>/simple` or
`SIMPLE_BINARY`). The child writes its report to the file named by
`SIMPLE_ANY_RULES_OUT` (the check entry truncates worker stdout at 12 000
characters). If that report has no `any-rules: checked` sentinel, lint reports
`W-ANY-NOTRUN` ("NOT CHECKED") as an error: the run exits non-zero, so it is
never taken for, or cached as, a clean file.

## Level switch

The rules are opt-in. All three families are `allow` in every lint profile,
including `robust` and `critical`: `src/compiler/simple.sdn` is `critical`,
and a profile-implied switch made a plain compiler-file lint 2.5x slower.
Off skips the work: lint starts no checker process, and `check` without
`SIMPLE_ANY_RULES` does not scan or walk. They apply to files under
`src/compiler/**` only; elsewhere nothing runs even when opted in.

| Want | How |
|---|---|
| on, warning | `SIMPLE_ANY_RULES=warn simple lint ...`, or `<family>: warn` under `lints:` in `simple.sdn` |
| on, error | `SIMPLE_ANY_RULES=deny`, or `<family>: deny` in `simple.sdn` |
| off (default) | nothing to do; `SIMPLE_ANY_RULES=off` also overrides a `simple.sdn` level |

A declaration or use inside an `unsafe:` / `danger:` block is not reported
(same carve-out as `E-ANY-COMPILE-001`).

## Baseline

`sh scripts/check/check-any-warn-rules-ratchet.shs` measures the 40 modules in
`scripts/check/any_warn_rules_scope.txt` against
`scripts/check/any_warn_rules_baseline.txt`. It is shrink-only: growth fails,
a lower count passes and is reported, and `--generate-baseline` refuses to
raise a count. Set `SIMPLE_BIN` to the binary to measure with.

## Adding a case

- New use position for `W-HIR-INFER-003`: call `any_note_typed_use` from the
  matching `walk_expr` arm in
  `src/compiler/35.semantics/lint/hir_frontend_diagnostics.spl`, behind
  `if self.any_rules`.
- New declaration slot for `W-ANY-DECL-001`: extend `scan_written_any` in
  `src/compiler/35.semantics/lint/written_any_scan.spl`.
- Add a must-flag and a must-not-flag fixture to
  `test/01_unit/compiler/lint/frontend_diag/any_warn_rules_acceptance_spec.spl`.

## Known limits

- Single-file lowering does not resolve imports. A value returned by an
  imported function is not seen as fallback-typed, so `W-HIR-INFER-003`
  undercounts; full-closure coverage needs the driver typecheck pass, which
  does not run these rules yet.
- `W-ANY-DECL-001` is a source scan (HIR cannot tell written from fallback
  `Any`, and its type spans are zero). It does not look at enum variant
  payloads, lambda parameters or `for` binders, and two methods with the same
  name in one file share suggestions.
- Type suggestions cover literals, typed locals/parameters, comparisons and
  calls to functions declared in the same file; parameters get none.
- `W-ANY-USE-002` flags every method, including ones that work on any value.
- Output is capped at 50 Any-rule findings per file (one summary line for the
  rest); the report file and the ratchet count all of them.
- When opted in under the seed interpreter the rules cost one extra `check` per compiler
  file: measured 62 s against 24 s with `SIMPLE_ANY_RULES=off` on
  `10.frontend/core/collection_feedback.spl`.
