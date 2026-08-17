# Aliased import `escape_json as _shared_escape_json` dropped in wildcard re-export graph

- **ID:** text_advanced_aliased_import_dropped_escape_json_2026-08-17
- **Status:** FIXED (workaround in `.spl`; resolver root cause still OPEN)
- **Severity:** P1 — hard failure of a whole CLI, and a silent trap for any
  stdlib module using an `as` alias
- **Area:** `src/lib/common/text_advanced.spl`, compiler name resolution
- **Filed:** 2026-08-17

## Symptom

`src/lib/common/text_advanced.spl:26` declared

```
use std.text.{escape_json as _shared_escape_json}
```

and `fn escape_json` at `:651` called `_shared_escape_json(s)`.

Reproduced (rc read on the line after the command, not through a pipe):

```
$ bin/simple run src/app/cli/query_visibility.spl symbols \
    src/lib/common/text.spl --requester src/lib/common/text.spl
rc=1
[INFO] JIT compilation failed, falling back to interpreter: semantic: function `_shared_escape_json` not found
error[E1002]: function `_shared_escape_json` not found
  = help: check the function name or import the module that defines it
```

## Why it hid

Importing the module **directly** resolves fine. Both of these ran `rc=0` and
printed the correct `a\"b`:

- `use common.text_advanced.{escape_json}`
- `use std.common.text_advanced.{escape_json}`

The failure only appears when the module is reached through the wildcard
re-export chain used by the CLI (`src/app/cli/_QueryVisibility/symbol_resolution.spl:2`
does `use app.cli.query_visibility.*`). Under that path the `as` alias binding
is not registered in the module scope, while the un-aliased local declaration
`escape_json` is — so the alias name is simply absent.

## Root cause

Two layers:

1. **Resolver (OPEN, compiler lane's scope):** an `as`-aliased import binding is
   lost when a module is pulled in through a wildcard re-export chain. Only the
   plain name survives. This is a general hazard for every `use X as Y` in the
   stdlib, not specific to `escape_json`.
2. **`src/lib/common/text_advanced.spl` (FIXED here):** the module relied on
   that alias for a load-bearing public function used by 8+ modules
   (`json/builder.spl`, `ui/access_query.spl`, `ui/web_render_api.spl`,
   `ui/semantic_contract.spl`, `ui/access_cli_grammar.spl`, `app/devhub/*`).

## Fix applied

The alias import was removed and `escape_json` in `text_advanced.spl` now
carries the run-copying implementation locally (same algorithm and same output
as `src/lib/common/text.spl:29`). The original dedupe rationale is recorded in
a comment at the old import site together with this doc's path, so the
delegation can be restored once the resolver keeps aliases across wildcard
re-exports.

## After

```
$ bin/simple run src/app/cli/query_visibility.spl symbols \
    src/lib/common/text.spl --requester src/lib/common/text.spl
rc=0
(0 occurrences of E1002 / _shared_escape_json; full JSON symbol list emitted)
```

## Specs

`test/01_unit/lib/common/text_advanced_escape_json_alias_spec.spl`

- **reproducing:** `escape_json` resolves and escapes `"`, `\`, `\n`, `\r`,
  `\t` correctly, and leaves clean strings untouched.
- **class detection:** a spec body runs interpreted and imports the module
  directly — the exact path that never reproduced the bug — so the detection
  examples shell out to a real `bin/simple run` of the CLI and assert no
  `E1002` / `not found` in its output, plus a tree-wide check that no owned
  stdlib module reintroduces an `escape_json as` alias.
