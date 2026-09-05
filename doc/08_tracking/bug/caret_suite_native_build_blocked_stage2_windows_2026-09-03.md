# Caret suite cannot native-build with the Phase-2 (Stage-2-admitted) Windows compiler

Date: 2026-09-03
Binary: `build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-admitted/simple.exe`
sha256 `fcf473728180d790bc6e15892c59cadf2f12600b4825575b30e3ff91c20bcf86` (verified)
Env: `. scripts/setup/windows-msvc-bootstrap-env.shs` sourced.

All four caret-suite components fail `native-build`. None of the failures is in
the caret sources themselves except B5 (fixed here); the rest are stdlib /
compiler-frontend gaps in the Stage-2 compiler.

## Repro

```
simple.exe native-build src/app/llm_caret/main.spl              -o out.exe  # rc=1
simple.exe native-build src/app/llm_caret/agent_manager_view.spl -o out.exe # rc=1
simple.exe native-build src/app/slang_pack/main.spl              -o out.exe # rc=1
simple.exe native-build src/app/hosted_apps/smux_client.spl      -o out.exe # rc=1
```

## STATUS UPDATE 2026-09-03 (later the same day)

Measured against the same Stage-2-admitted binary. Read this before acting on
the root-cause list below — three of its entries are now wrong or resolved.

| id | status |
|---|---|
| B1 | **Fixed in source**, `fa87eda863b`. Parser defect, not stdlib. The class/struct member loop recognised only `@layer_field(...)`; a member-position twin of the module-decl `@unsafe` arm was added, capturing the metadata rather than skipping it (310 annotated methods across src/std + src/lib depend on it, so a stdlib workaround does not scale). Native proof pends a self-hosted rebuild — the parser is compiled into the stage binary. |
| B2 | **Fixed and proven**, `f556f23aca4`. One missing type in an existing import line in `src/app/io/context_ops.spl`. 5 hir-fatals before, 0 after. |
| B3 | **Re-diagnosed — NOT a missing import.** `Id` is the type PARAMETER of `struct PostingList<Id>`; there is nothing to import. Superseded by `hir_generic_type_param_unresolved_cross_module_2026-09-03.md`, which carries a 14-line two-module repro. Deliberately not patched: the fix lands in the resolver file another session is editing for devhub. |
| B4 | **Still open. Partly mis-stated in an earlier revision of this row — corrected here.** It disappeared from the `slang_pack` build after the B2 fix, but that is because slang's module closure never lowers `cli_util.spl`, not because B2 caused it. The `agent_manager_view` build, whose closure DOES include it, still reports `unresolved name: cwd` after the B2 fix. `cwd` is a plain `fn` in `src/std/nogc_sync_mut/io/env_ops.spl:93`, re-exported by `io/__init__.spl:93` in the same bare-`export` form as `file_exists`/`file_read`, which resolve — so the shape of the export is not the discriminator. Untested hypothesis: the paren-form `use std.io (cwd, file_exists, file_read)` at `cli_util.spl:4` (238 uses tree-wide vs 8,754 brace-form) resolves differently, and the other two names happen to be reachable through another module in the closure (`cwd` is also `pub fn` in `io_runtime.spl:421`). Not confirmed: the obvious cheap fixture cannot discriminate, because an ad-hoc sibling-module import fails first with `missing importing module surface` under BOTH forms. |
| B6 | **Fixed in source**, `55bc4cfdd0a`. Not a "bare `int` alias" problem — `int` has no alias anywhere; it was simply missing from `lower_named_kind`'s primitive arms while the seed resolves it (`"i64" \| "int"`, calls.rs:528) and this compiler's own SFFI reader already canonicalises `"int" -> "i64"`. Exact twin of the documented `float` gap. Native proof pends the same rebuild. |
| B7 | Unchanged, owned elsewhere. Same corruption class also masks the AOT backend error — see below. |
| B8 | Unchanged, still filed. |

**The repro commands at the top of this file are misleading and should not be
reused as written.** A bare `native-build` fails on a TWO-LINE HELLO WORLD on
every Windows compiler binary on this host. `SIMPLE_BOOTSTRAP=1` is the single
knob that fixes it (bisected). With the full sanctioned invocation, hello world
builds and prints `hello`, rc=0. Every measurement in the original list was
taken through the broken invocation. Details and the working command line:
`native_build_requires_simple_bootstrap_env_windows_2026-09-03.md`.

After the B2 fix, slang's ONLY remaining hir-fatals are 11 x
`unresolved type: Id` (B3). Agent manager's are 12: the same `Id` set plus the
one `unresolved name: cwd` (B4). The `Result` / `Option` / `Dict` / `list`
`dep-origin-unresolved` lines in the log are advisories, not fatals.

Known edge in the B1 fix, stated rather than left to be found:
`parser_reset_pending_unsafe()` fires on the three METHOD branches of the
member loop, so an `@unsafe` placed immediately before a FIELD would carry its
pending annotation to the next method. Every occurrence in the tree is
attribute-directly-before-method, so this is not reachable today.

## Root causes (distinct)

- **B1 parser: `@attr(...)` in a class body is rejected.**
  `[parser_error] line 136:5: unexpected token in class body` /
  `kind 171 text '@'` at `src/std/nogc_sync_mut/atomic.spl:136`
  (`@unsafe(reason: ..., capabilities: [ffi])` on a method). Blocks caret at
  phase 1 — caret never reaches HIR.
- **B2 HIR: `unresolved type: SqliteConnection`** in all five `src/app/io/*.spl`
  modules (`mod`, `cli_ops`, `env_ops`, `process_ops`, `process_env_ops`).
  Poisons `app.io.*`, which caret / agent manager / slang all import.
- **B3 HIR: `unresolved type: Id`** — 11 errors across
  `src/std/common/search/types.spl` and `ranking.spl`.
- **B4 HIR: `unresolved name: cwd`** at `src/std/nogc_sync_mut/cli/cli_util.spl:11:5`.
- **B5 HIR (caret source, FIXED here): `untyped function returns a value`** —
  `agent_manager_view.spl` `fn main():` ended with `return ()`. Removed the
  `return ()`; interpreter lane re-verified identical output afterwards.
- **B6 HIR: `unresolved type: int`** — 385 errors, 5 poisoned modules, across
  `src/os/apps/smux/{smux_remote,api,contract,service,buffer}.spl`. The bare
  `int` alias does not resolve in the Stage-2 frontend. Blocks smux entirely.
- **B7 diagnostics: `phase 3 FAILED (diagnostics unreadable: error array did not
  survive transport)`** printed on every HIR failure — the structured error
  array is lost between phases; only the `[hir-fatal]` trace lines are usable.

## Interpreter-lane defect found in the same pass

- **B8 `rt_stdin_read_line` boxed-result truncation panic.**
  `bin/simple.exe run src/app/hosted_apps/smux_client.spl < cmds` prints
  `smux_remote_main: service started, session=default` then PANICs:
  `rt_value_raw_i64: refusing to truncate a non-float heap-boxed InterpCall
  result (tag=1) to a raw i64` at `runtime/src/value/sffi/value_ops.rs:116`.
  Exit 127, crash report written. `rt_stdin_read_line() -> text?` returns a
  boxed optional that the JIT call path unboxes as i64.
  Related: `doc/08_tracking/bug/jit_rt_tls13_sha256_returns_empty_2026-08-05.md`.
