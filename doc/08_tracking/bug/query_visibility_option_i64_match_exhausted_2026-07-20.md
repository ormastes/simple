# query_visibility / lsp_query CLIs crash: `Option<i64>` match exhausted on a raw i64

**Date:** 2026-07-20
**Component:** identifier/char-boundary resolution helper shared by
`src/app/cli/_QueryVisibility/symbol_resolution.spl` and (transitively)
`src/lib/nogc_sync_mut/lsp/lsp_query.spl`'s symbol-lookup path
**Severity:** High — every subcommand of the `query_visibility` and
`lsp_query` CLIs crashes before producing output, so all consumers (LSP
visibility surfaces, workspace-symbol queries) fail identically
**Found by:** whole-suite triage campaign, `test/02_integration/app/`
cluster, confirmed via direct reproduction on
`bin/release/x86_64-unknown-linux-gnu/simple` (both `bin/simple run` and
`bin/simple test` paths)

## Symptom

```
error: semantic: invalid pattern: match expression exhausted without matching any pattern for i64 value 34; arms [25:9 Enum { name: "Option", variant: "Some", payload: Some([Identifier("idx")]) }, 27:9 Literal(Nil)]
```

(exact `i64 value` differs per call site/input — `34` for `query_visibility`,
`25` for `lsp_query` — but the arm shape is identical: a `match` written for
`Option<i64>` with `case Some(idx): ...` / `case Nil: ...` arms is being
evaluated against a bare, already-unwrapped `i64`, so neither arm matches
and the match exhausts.)

Preceding the crash in every repro, the log shows deprecated-generics
warnings pointing at the same shape of code:

```
--> .../symbol_resolution.spl:110:70
110 |         if idx >= 0 and idx < chars.len() and not is_ident_char(chars[idx]) and idx > 0 and is_ident_char(chars[idx - 1]):
```

i.e. an identifier/word-boundary scan over `chars[idx]` that looks up a
character index via something typed `Option<i64>` (find-style lookup) and
then match-unwraps it — the match unwrap is the thing that's broken.

## Minimal repro

```sh
cd /home/ormastes/dev/pub/simple
bin/simple run src/app/cli/query_visibility.spl symbols \
  src/compiler/10.frontend/testdata/visibility_query_fixture.spl \
  --requester src/compiler/35.semantics/testdata/visibility_query_fixture.spl
# exit 1, empty stdout, stderr ends with the match-exhausted error above (i64 value 34)

bin/simple src/lib/nogc_sync_mut/lsp/lsp_query.spl symbols \
  src/lib/nogc_sync_mut/lsp/main.spl
# exit 1, empty stdout, stderr ends with the match-exhausted error above (i64 value 25)
```

## Affected specs (same root cause, consolidated here)

- `test/02_integration/app/query_visibility_surfaces_spec.spl` — all 6
  examples fail (`symbols`, `hover`, `completions`, `document symbols`,
  `semantic-tokens` full and scoped-range — every subcommand calls into the
  same broken resolver)
- `test/02_integration/app/query_visibility_workspace_symbols_spec.spl` —
  all 3 examples fail (reachable symbols, boundary-private filtering, ranked
  order — all go through the same `symbols` subcommand)
- `test/02_integration/app/lsp_query_visibility_symbols_spec.spl` — the 1
  example fails (`lsp_query.spl symbols`), same exhausted-match signature at
  a different call-site line, confirming the shared helper is the common
  root, not a `query_visibility.spl`-only bug

10 examples across 3 spec files, all attributable to this one defect.

## Root-cause hypothesis

The `Option<i64>` lookup that feeds this match (something like "find index
of X in chars, return `Some(idx)`/`Nil`") is losing its `Option` wrapper
somewhere between production and the `match` — the match consumer receives
the bare `i64` payload instead of the `Option<i64>` enum, so the pattern
matcher can't match either the `Some(idx)` or `Nil` arm and reports
"exhausted." This has the same flavor as other tag/box-unwrap mismatches
noted in this codebase's interpreter (e.g. `.?`'s identity-passthrough
defect in `optional_query_operator_identity_passthrough_2026-07-20.md`) —
worth a joint look by whoever owns Option/enum tag-boxing in the
interpreter, though the exact mechanism here (pattern-match arm dispatch,
not `.?`) was not root-caused further; out of scope for this triage pass
(no Rust seed source changes attempted).

## Note

Left the 3 spec files unmodified — they are correct as written and
correctly detect this defect; nothing to fix on the test side.

## Re-verification 2026-08-17 (lane m5a_app_cli) — DOES NOT REPRODUCE; superseded by a different blocker

Ran the doc's own minimal repro verbatim against the deployed `bin/simple`
(Rust seed) in `/mnt/data/worktrees/simple-main`:

```
bin/simple run src/app/cli/query_visibility.spl symbols \
  src/compiler/10.frontend/testdata/visibility_query_fixture.spl \
  --requester src/compiler/35.semantics/testdata/visibility_query_fixture.spl
rc=1
```

stdout empty (as documented), **but stderr no longer contains the
match-exhausted error** — `grep -c exhausted` on the captured stderr is 0.
The run now dies with a completely different, earlier failure:

```
error[E1002]: function `_shared_escape_json` not found
  = help: check the function name or import the module that defines it
```

So the `Option<i64>` match-exhausted defect is **not reproducible by content
or by execution**: `src/app/cli/_QueryVisibility/symbol_resolution.spl` contains
no `Option<i64>` match at all (grep for `Option`, `Some(`, `match ` returns
only unrelated lines). Classified **already-fixed / stale** for the documented
symptom.

**New blocker surfaced (out of this lane's scope — `src/lib`, not
`src/app/cli`):** `src/lib/common/text_advanced.spl:26` does
`use std.text.{escape_json as _shared_escape_json}` while the *same module*
also declares `fn escape_json` at line 651, whose body calls
`_shared_escape_json(s)`. The aliased import is not resolvable at that call
site — a self-shadowing / import-alias resolution defect. Both `escape_json`
definitions exist (`src/lib/common/text.spl:29`, `text_advanced.spl:651`).
Until that is fixed, every `query_visibility` subcommand still exits 1 with
empty stdout, so the CLI remains user-visibly broken for a *different* reason.
The three cited integration specs will therefore still be RED, and must not be
read as evidence for the Option<i64> defect.
