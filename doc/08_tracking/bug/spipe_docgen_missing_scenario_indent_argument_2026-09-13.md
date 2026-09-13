# `spipe-docgen` fails on every spec: missing argument for parameter `scenario_indent`

- **Filed:** 2026-09-13
- **Area:** app / spipe_docgen (`src/app/spipe_docgen/`)
- **Status:** FIXED 2026-09-13.

## Fix

`parser.spl:1097` now passes the `continuation` array, derived in place from
the lines the caller handed in, so the public 2-argument shape of
`scenario_at_is_unconditional_pending` is preserved (three call sites in
generator.spl plus `spec_kw_line_spec.spl` depend on it). The signature side
was NOT reverted: the history shows `continuation` was added deliberately in
PR #373 so a fixture's column-0 string body no longer ends a scenario early,
and four of the five call sites already pass it.

Verified: all six specs in `test/02_integration/ui/web_showcase/` generate with
`Stubs: 0/6 (0%)`, `6 complete`. New end-to-end scenario:
`test/01_unit/app/spipe_docgen/docgen_end_to_end_spec.spl`.

## Symptom

```
$ bin/simple spipe-docgen test/02_integration/ui/web_showcase/catalog_cpu_determinism_spec.spl \
      --output doc/06_spec --no-index
error: semantic: function expects argument for parameter 'scenario_indent', but none was provided
EXIT=1
```

## It is not caused by the spec being generated

The identical error appears for a long-standing, unmodified spec:

```
$ bin/simple spipe-docgen test/02_integration/ui/widget_interact_model_spec.spl \
      --output doc/06_spec --no-index
error: semantic: function expects argument for parameter 'scenario_indent', but none was provided
EXIT=1
```

So this is a defect in the docgen program itself — a call site that does not
pass `scenario_indent` to a function that requires it — not a property of any
particular spec file. It reproduces on the first spec tried and on the control
spec, i.e. every invocation attempted.

## Root cause (located)

`src/app/spipe_docgen/spipe_docgen/parser.spl` — the declaration takes four
parameters:

```
1837: fn find_scenario_body_end(lines: [text], continuation: [bool], start: i64,
                                scenario_indent: i64) -> i64:
```

and the call site passes three, omitting `continuation`, so `scenario_indent`
lands with no argument:

```
1096:     val scenario_indent = count_leading_indent(scenario_line)
1097:     val end_index = find_scenario_body_end(lines, scenario_index + 1, scenario_indent)
```

This is a static arity mismatch in docgen's own source, so it is independent of
which binary runs it and of any default-parameter behaviour. The fix is to pass
the `continuation` array at line 1097 (or to give the parameter a default, if
the second positional argument is genuinely optional for this call).

## Environment

`bin/simple` here is the Rust bootstrap seed (it prints the "bootstrap seed
only" warning). The run also degrades to the interpreter first:

```
[jit-fallback] unresolved external symbol 'cli_current_exe_path':
  whole module dropped to the interpreter
```

That fallback is a separate, non-fatal issue; the fatal error is the missing
argument, which is a static semantic error and would occur under any backend.

## Impact

The five specs added in `test/02_integration/ui/web_showcase/` could not have
their `doc/06_spec` pages generated, so their stub count is unverified. The
specs themselves run and pass — only documentation generation is blocked.

## Next step for the owner

Find the `scenario_indent` parameter in `src/app/spipe_docgen/` and the call
site that omits it. Worth checking whether the parameter was recently given a
non-default value, since docgen is reported as working in earlier sessions.
