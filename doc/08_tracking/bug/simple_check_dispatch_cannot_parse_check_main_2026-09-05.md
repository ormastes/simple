# `simple check` fails to parse its own entrypoint on every input (2026-09-05)

## Status
OPEN. Blocks the acceptance checkbox
`bin/simple check src/app/editor/ passes with zero HIR type-inference failures`
(`test/03_system/plan_acceptance/editor_markdown_editing_subsystem_spec.spl`,
REQ-EDITOR-MD-008) and, by extension, any lane that gates on `simple check`.

## Symptom
The `check` subcommand aborts before it looks at its target, on ANY target:

```
$ src/compiler_rust/target/debug/simple check /tmp/tiny.spl
error: compile failed: parse: in "/Users/ormastes/simple/src/app/check/main.spl":
       Unexpected token: expected expression, found Colon
```

`/tmp/tiny.spl` is a two-line hello world, so the failing file is the
entrypoint `src/app/check/main.spl`, not the target. The exit code is 1 and the
message is identical for `simple check src/app/editor/`.

## What rules it out
The same file parses cleanly on the `run` path, by both relative and absolute
path:

```
$ src/compiler_rust/target/debug/simple run src/app/check/main.spl --help          # OK, prints help
$ src/compiler_rust/target/debug/simple run /Users/ormastes/simple/src/app/check/main.spl --help  # OK
$ src/compiler_rust/target/debug/simple compile src/app/check/main.spl            # OK
```

Truncating the file to 40/80/120/160/200/240/280/320 lines and running each
prefix produced zero `found Colon` errors, so the construct is not isolatable by
prefix under the `run` parser either. The defect is therefore in the parser mode
the `check` DISPATCH path uses, not in `src/app/check/main.spl`'s text as the
normal parser sees it.

## Binary identity
`src/compiler_rust/target/debug/simple`, 120103640 bytes, mtime 2026-09-04
18:13:37 (debug Rust seed built from current source). The deployed
`bin/simple` cannot be used to cross-check: it resolves to
`bin/release/aarch64-apple-darwin-macho/simple`, which is the BOOTSTRAP CLI and
answers `error: unknown command 'check'`.

## Impact
Two independent blockers stack on REQ-EDITOR-MD-008:
1. the deployed `bin/simple` has no `check` subcommand at all (stale stage4
   deployment), and
2. even the current-source debug seed cannot run `check` on any input.

## Next step
Find which parser the `check` dispatch arm invokes (it differs from the `run`
path's) and why it rejects a colon that the normal parser accepts. Do not
"fix" `src/app/check/main.spl` by rewriting source the normal parser already
accepts -- that would move the defect, not repair it.
