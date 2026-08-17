# impl-to-free-fn refactor damage: family declared closed but ~60 zero-definition sites survive

- **Filed:** 2026-08-08
- **Severity:** High (dead call sites in live compiler passes; silent no-ops / unresolved calls)
- **Status:** PARTIALLY FIXED — re-measured 2026-08-17 (see "Re-measurement"
  below): **25 oracle hits, of which 12 are actual refactor damage**. 7 are
  `fuzz.spl`'s missing-module defect, 5 are known regex false positives, 1 is a
  Class C stdlib gap. Quote both numbers (oracle-25 / family-12) or the next
  reader chases 13 non-issues. **The family is NOT closed.**
  (Superseded figures, 2026-08-08: oracle-40 / family-27.)
- **Found by:** adversarial review of `b0c98541d2a`, `bc052a4470d`

## Update 2026-08-08: oracle rebuilt, 24 sites restored

The oracle below was re-implemented **fail-closed with an injection test** (the
08-07 doc's oracle failed open three ways; this one is proven to move by exactly
one on an injected known-bad symbol and back on restore — probe landed at
`easy.spl:321`, count 64 -> 65 -> 64, round-trip byte-identical).

**Precise-extraction count is 64, not ~60.** An earlier pass that emitted every
underscore-named call on a matching line reported 91; tightening extraction to
only the callee whose first argument re-passes its own prefix (`<X>_<Y>(<X>`)
drops the 27 incidental hits (`outline_*.spl` etc). Use the tightened form.

### What the oracle can and cannot prove

- **Proves:** the called name has ZERO `fn`/`me` definitions in `src/`.
- **Does NOT prove:** that a call binds to the *right* function. `mod.spl:207`'s
  `args_len(args)` has a definition (`src/app/ui.tauri/tauri_entry.spl:15`,
  `[text] -> i64`) while `args` is `[MacroArg]` — under the flat bare-name
  function table this binds the WRONG function silently. The oracle is
  structurally blind to this class. **A zero-survivor oracle run is therefore
  NOT proof the family is closed.**
- **Does NOT prove:** semantic correctness of any restore.

### Disposition classes

- **Class A — mechanical, target confirmed to exist.** Fixed in this pass.
- **Class B — the body itself was deleted; restoring requires inventing
  semantics.** Deliberately NOT fixed. A wrong body is worse than a missing one:
  it makes a dead check look live while enforcing invented rules.
- **Class C — not this family.** Excluded, filed separately where warranted.

### Fixed in this pass (24 sites, 17 files)

| file:line | was | restored to | evidence |
|---|---|---|---|
| `macro_check/hygiene.spl:222` | `scope_bind(scope,...)` | inlined `scope.bindings[name] = ident` + write-back | see note — a helper here would be a silent no-op |
| `macro_check/hygiene.spl:239,290` | `scope_lookup(scope,...)` | `hygienescope_lookup(...)` | **function newly written** — see note |
| `macro_check/hygiene.spl:337` | `ident_add_mark(ident,...)` | `markedident_add_mark(...)` | target at `hygiene.spl:64` |
| `macro_check/template.spl:277` | `param.kind_to_text(kind)` | `param.kind.to_text()` | `TemplateParam.kind` field at `:82`; `kind.to_text()` already used at `:167` |
| `macro_check/template.spl:300` | `kind_to_text(kind)` | `kind.to_text()` | same |
| `macro_check/mod.spl:207` | `args_len(args)` | `args.len()` | wrong-binding class; `args` is `[MacroArg]` |
| `exhaustiveness_validator.spl:117` | `pattern_get_severity(pattern)` | `pattern.severity` | field at `:63`; `match self.severity:` is the file's own idiom at `:72`,`:77`, and no accessor normalizes it (`is_error` at `:71` just matches it) |
| `exhaustiveness_validator.spl:405` | `pattern_is_error(pattern)` | `pattern.is_error()` | method at `:71` |
| `predicate_parser.spl:125` | `tokens_len(tokens)` | `tokens.len()` | `tokens: [Token]` |
| `blocks/validators.spl:100,109` | `key_len` / `elements_len` | `.len()` | list/text receivers |
| `blocks/validators.spl:143` | `query.raw_lower(raw)` | `query.raw.lower()` | `.raw` field used at `:42` |
| `blocks/testing.spl:84` | `error.message_contains(message,...)` | `error.message.contains(...)` | shape (d); the very next line `:85` already interpolates `{error.message}` |
| `monomorphize/util.spl:112` | `elems_first(elems)` | `elems.first()` | list receiver |
| `semantics/binary_ops.spl:120,123` | `*_wrapping_mul(x, y)` | `x.wrapping_mul(y)` | integer receivers |
| `macro_contracts.spl:104` | `existing_symbols_contains(...)` | `.contains(...)` | collection receiver |
| `smf_mmap_native.spl:106` | `result_reserve(result, length)` | `result.reserve(length)` | |
| `type_system/effects.spl:228` | `scc_contains(scc, callee)` | `scc.contains(callee)` | collection receiver |
| `visibility_checker.spl:111` | `checker_check_symbol_access(checker,...)` | `checker.check_symbol_access(...)` | method exists in file |
| `common/type_mapper.spl:23` | `mapper_map_type(mapper,...)` | `mapper.map_type(...)` | method exists in file |
| `vulkan_backend.spl:100` | `backend_compile(backend,...)` | `backend.compile(...)` | method exists in file |
| `win_vfs_driver.spl:145,157` | `tree_readdir` / `tree_read` | `tree.readdir()` / `tree.read()` | methods exist in file |
(`gc_analysis/mod.spl`'s `_1` sites are **diagnosed but NOT landed** — see the
shape (e) section below.)

**Note on `hygienescope_bind`/`hygienescope_lookup`:** neither existed. The
08-07 doc's "candidate restore" column guessed them as pre-existing targets;
that was wrong.

- **`hygienescope_lookup` was written** — body reconstructed from the field type
  (`bindings: Dict<text, MarkedIdent>`) as `contains_key` + index read (the
  native `.get()` prohibition applies since `MarkedIdent` is a struct). It is a
  pure read, so taking `self` by value is harmless. A reconstruction, not a
  recovery.
- **`hygienescope_bind` was deliberately NOT written.** `HygieneScope` is a
  struct (value type), and this file's convention for
  `fn <type>_<method>(self: Struct, ...)` is to **return a new struct**, never
  mutate in place — see `markedident_add_mark`/`markedident_remove_mark`
  (`:64`, `:69`), both of which construct and return a fresh value. A void
  `bind` helper mutating `self.bindings` would therefore have died inside the
  callee and the caller's write-back would have stored an unchanged scope —
  converting one dead check into a differently-dead check. The bind is inlined
  at the call site with the repo's ADR-004 write-back idiom
  (`var scope` → mutate → store back) instead.

## NEW: shape (e) — deleted match-arm bodies. `gc_analysis/mod.spl` does not parse.

A **fourth damage shape** exists that none of the sweep regexes catch: `case`
arms whose body was deleted, leaving `case _:` immediately followed by a dedent.
`gc_analysis/mod.spl` has **4 such arms**, and they make the whole module
**unparseable**:

```
src/compiler/55.borrow/gc_analysis/mod.spl:250:1: error[PARSE001]: NOT LINTED:
source did not parse - every AST-based lint was skipped for this file
(unexpected token in expression: Dedent '')
```

This is **pre-existing on `origin/main`**, not introduced by any restore: the
empty `case _:` at local line 250 is byte-identical to `origin/main`'s line 246
(the 4-line offset is a comment added while investigating), and a lint of
origin's own blob reproduces it.

Consequences, which matter more than any single call site here:

- **The module is wholly non-functional.** Nothing in it can have been running.
- This **supersedes** this doc's earlier claim that `gc_types_contains` /
  `gc_types_push` at `:119,120,124` were "fixed in the commit that adds this
  doc" — those fixes live in a file that has never parsed.
- **The `_1` shape is diagnosed but deliberately NOT landed.** `_1`/`_2` lift
  into lambdas only inside *parenthesised pipe* expressions
  (`syntax_quick_reference.md`, "Placeholder Lambdas in Pipes"), so the bare
  `_1` at `:129,132` is an unbound identifier. The intended form is determined
  — not guessed — by the sibling call for the *same* constructor parameter at
  `:111`, `RootAnalysis.create(\t: false)` (verified with `cat -A` to be a
  literal backslash-t lambda, not a tab), giving
  `\t: self.is_gc_type(t)`. It is held back because a file that does not parse
  cannot verify the fix: no lint, no spec, no oracle can exercise it. Landing it
  would put a signature on a file that stays dead.

**To make `gc_analysis/mod.spl` live again**, the 4 empty `case _:` arms must be
given bodies first — that is Class B work (what should each arm do?), and it
gates the `_1` fix behind it.

Any future sweep of this family must add a shape (e) detector: a `case` label
followed immediately by a dedent.

### Still open — Class B (body deleted, semantics must be invented)

Do NOT "restore" these by pattern-matching a name; each needs its behaviour
decided and a test.

- `macro_check/template.spl:165` `kind_can_follow(kind, prev_kind)` — the
  `# FragmentKind Methods (was: impl FragmentKind:)` block at `template.spl:36`
  is **empty**. This is resurgent **shape (a)**, which the 08-07 doc declared
  had "zero instances remain" — that claim is false. Writing a macro follow-set
  rule from nothing is a semantic invention; left dead deliberately.
- `type_system/effects.spl:117,309,353,361` — `effect_is_sync` /
  `effect_value_is_async` / `effect_value_is_sync` /
  `callee_effect_value_is_async`. `Effect` here (`:18`) is a bare
  `Sync`/`Async` enum with no methods; `is_sync`/`is_async` methods exist only
  on *different* Effect types in `00.common/effects.spl` and
  `00.common/effects_phase3a.spl`. Which one is intended is ambiguous.

### Still open — Class C (not this family)

- `exhaustiveness_validator.spl:474` `std.sys_exit(sys, 1)` — a `std.`-qualified
  stdlib call, not a folded receiver. No `sys_exit` exists anywhere; the stdlib
  offers `exit(code)` (`io_runtime.spl:214`). Missing stdlib binding, separate bug.
- `src/lib/nogc_sync_mut/fuzz.spl:164,169,199,231,246,291,299` `rng_next_range` —
  **not refactor damage.** `fuzz.spl:16` imports `std.random_utils`, a module
  that **does not exist anywhere in the tree**, so every one of its imported
  names (`rng_create`, `rng_next`, `rng_next_range`, `random_choice`) is dead.
  The whole module is non-functional. Separate defect; do not "fix" by inventing
  an RNG.
- `syscall_spm.spl` (4), `backend_metal_msl.spl` (1) — known regex false
  positives already listed at the bottom of this doc (docstring text; embedded
  MSL shader source). Do not touch.

### Still open — remaining Class A (not yet done, mechanical)

`resolution.spl:95,97,129,130,157`; `desugar_async.spl` (both copies);
`visibility_checker.spl:270,272`; `blocks/registry.spl:26,182`;
`blocks/definition.spl:60,61`; `blocks/text_transforms.spl:37`;
`parser/recovery.spl:215`;
`test_batch.spl:69`; `snapshots.spl:147`; `markdown.spl:164`.

`blocks/testing.spl:294` `value_type_name(value)` is **also still open** — note
that `:84` in the same file WAS fixed this pass, so the file is not untouched.
It is held back because the in-file `type_name` method count is zero; the
receiver's type was NOT resolved, so the disposition (mechanical rename vs
Class B deleted body) is undetermined. Resolve the receiver type before editing.

## Summary

`b0c98541d2a` ("restore folded-receiver method calls, shape (d) refactor
damage", 8 files) and `bc052a4470d` ("restore cycle_detector.spl free-function
calls", 1 file) both present themselves as closing the impl-to-free-fn
refactor-damage family. They do not. A fail-closed tree-wide sweep finds ~60
surviving call sites of the same two damage shapes whose callee has **zero
`fn`/`me` definitions anywhere in `src/`**.

Six of the survivors are in files those two commits *edited* — the sweeps were
per-line, not per-file.

## Damage shapes

1. `recv.<X>_<Y>(<X>, ...)` — folded receiver, first argument re-passed.
2. `<X>_<Y>(<X>, ...)` — bare free-function form (the `bc052a4470d` cluster).

## Oracle (fail-closed, reproducible)

```sh
# all fn/me definition names tree-wide (deliberately over-broad => fail-closed)
/usr/bin/grep -rEoh '\b(fn|me)[[:space:]]+[a-zA-Z0-9_]+' src/ --include=*.spl \
  | /usr/bin/sed -E 's/.*[[:space:]]//' | sort -u > defs.txt

# shape 1
/usr/bin/grep -rEn '[a-z0-9_]+\.([a-z0-9_]+)_[a-z0-9_]+\(\1[,)]' src/ --include=*.spl
# shape 2
/usr/bin/grep -rEn '(^|[^.a-zA-Z0-9_])([a-z0-9_]+)_[a-z0-9_]+\(\2[,)]' src/ --include=*.spl
```
For each hit, extract the callee name and reject it if it appears in `defs.txt`.
A callee with **zero** definitions is a surviving damage site. Use `/usr/bin/grep`
(ugrep is the default `grep` here) and `-r` (not `-R`) so the `mir`/`hir`/
`driver`/`backend` symlinks are not followed into double counts.

## Surviving sites

### In files the two reviewed commits edited (missed line-by-line)

**The "candidate restore" column is UNVERIFIED and must be confirmed per row
before use.** The oracle proves only that the *called* name has zero
definitions; it says nothing about what the correct target is. This repo's
free-function convention is `<lowercased-type>_<method>(self, ...)`, so the
right restore is often a *differently-prefixed free function*, not a dotted
call — e.g. `hygiene.spl:337`'s `ident_add_mark(ident, ...)` restores to
`markedident_add_mark(ident, ...)` (defined at `hygiene.spl:64`), NOT to
`ident.add_mark(...)`. Likewise `HygieneScope`'s helpers are named
`hygienescope_*` (`hygiene.spl:116,127`), so `scope_bind`/`scope_lookup`
probably restore to `hygienescope_bind`/`hygienescope_lookup` — confirm the
target exists before editing.

| file:line | dead call (zero definitions tree-wide) | candidate restore (UNVERIFIED) |
|---|---|---|
| `src/compiler/35.semantics/macro_check/hygiene.spl:222` | `scope_bind(scope, name, ident)` | `hygienescope_bind(scope, name, ident)`? |
| `src/compiler/35.semantics/macro_check/hygiene.spl:239` | `scope_lookup(scope, ident.name)` | `hygienescope_lookup(scope, ident.name)`? |
| `src/compiler/35.semantics/macro_check/hygiene.spl:290` | `scope_lookup(scope, name)` | `hygienescope_lookup(scope, name)`? |
| `src/compiler/35.semantics/macro_check/hygiene.spl:337` | `ident_add_mark(ident, self.current_mark)` | `markedident_add_mark(ident, self.current_mark)` (target CONFIRMED at `hygiene.spl:64`) |
| `src/compiler/35.semantics/macro_check/template.spl:165` | `kind_can_follow(kind, prev_kind)` | ? |
| `src/compiler/35.semantics/macro_check/template.spl:277` | `param.kind_to_text(kind)` | ? |
| `src/compiler/35.semantics/macro_check/template.spl:300` | `kind_to_text(kind)` | ? |
| `src/compiler/35.semantics/macro_check/mod.spl:207` | `args_len(args)` — sole tree-wide definition is `src/app/ui.tauri/tauri_entry.spl:15` (`[text] -> i64`), an unrelated app module. Under the flat bare-name function table this can resolve to the WRONG function rather than fail (see `9918298a7240`). | ? |
| `src/compiler/70.backend/backend/exhaustiveness_validator.spl:117` | `pattern_get_severity(pattern)` | ? |
| `src/compiler/70.backend/backend/exhaustiveness_validator.spl:405` | `pattern_is_error(pattern)` | ? |
| `src/compiler/70.backend/backend/exhaustiveness_validator.spl:474` | `std.sys_exit(sys, 1)` | ? |

`macro_check/mod.spl:206`'s `validator.params.keys().len()` — the one place
`b0c98541d2a` deliberately changed semantics — is **CORRECT**: `params` is
`Dict<text, TemplateParam>` (`template.spl:124`), so `Dict.len()` would have
returned -1 under native codegen.

### Elsewhere (never swept)

`src/compiler/55.borrow/gc_analysis/mod.spl:119,120,124` — `gc_types_contains`
/ `gc_types_push` (**fixed in the commit that adds this doc**).

**Same file, DIFFERENT damage shape, still open:**
`src/compiler/55.borrow/gc_analysis/mod.spl:129` and `:132` pass a bare `_1`
placeholder — `RootAnalysis.create(self.is_gc_type(_1))`. `_1` is not bound in
either scope; this looks like a lambda/closure argument mangled by the same
refactor (`\x -> self.is_gc_type(x)` collapsed to a positional placeholder that
the language does not support here). Not covered by either regex shape above,
so a sweep that only chases `<X>_<Y>(<X>)` will not surface it. Deliberately
left unfixed here because the intended closure form is a guess.

Still open:

- `src/compiler/30.types/type_system/effects.spl:117` `callee_effect_value_is_async(callee_effect_value)`; `:228` `scc_contains(scc, callee)`; `:309` `effect_is_sync(effect)`; `:353` `effect_value_is_async(effect_value)`; `:361` `effect_value_is_sync(effect_value)`
- `src/compiler/00.common/dependency/resolution.spl:95` `mp_segments(mp)`; `:97` `segs_len(segs)`; `:129,130,157` `fs_has_file(fs, ...)`
- `src/compiler/35.semantics/visibility_checker.spl:111` `checker_check_symbol_access(checker, ...)`; `:270` `symbol_table_lookup(symbol_table, name)`; `:272` `symbol_table_get(symbol_table, sym_value)`
- `src/compiler/15.blocks/blocks/validators.spl:100` `key_len(key)`; `:109` `elements_len(elements)`; `:143` `query.raw_lower(raw)`
- `src/compiler/15.blocks/blocks/testing.spl:84` `error.message_contains(message, expected_message)`; `:294` `value_type_name(value)`
- `src/compiler/15.blocks/blocks/registry.spl:26,182` `blk_lexer_mode(blk)`
- `src/compiler/15.blocks/blocks/definition.spl:60` `parser_set_mode(parser, ...)`; `:61` `parser_parse_expr(parser)`
- `src/compiler/15.blocks/blocks/easy.spl:113` `pattern_trim(pattern)`
- `src/compiler/15.blocks/blocks/text_transforms.spl:37` `vars_items(vars)`
- `src/compiler/00.common/predicate_parser.spl:125` `tokens_len(tokens)`
- `src/compiler/70.backend/backend/common/type_mapper.spl:23` `mapper_map_type(mapper, mir_type)`
- `src/compiler/70.backend/backend/vulkan_backend.spl:100` `backend_compile(backend, mir_module)`
- `src/compiler/35.semantics/semantics/binary_ops.spl:120` `result_wrapping_mul(result, base)`; `:123` `base_wrapping_mul(base, base)`
- `src/compiler/35.semantics/macro_contracts.spl:104` `existing_symbols_contains(existing_symbols, item.name)`
- `src/compiler/40.mono/monomorphize/util.spl:112` `elems_first(elems)`
- `src/compiler/10.frontend/desugar/desugar_async.spl:44` `response_text(response)`; `:227` `future_expr_poll(future_expr, waker)` — and the duplicate copy at `src/compiler/90.tools/desugar_async.spl:42,225`, plus `:122` `analysis.suspension_points_len(suspension_points)`
- `src/compiler/99.loader/loader/smf_mmap_native.spl:106` `result_reserve(result, length)`
- `src/lib/nogc_sync_mut/fuzz.spl:164,169,199,231,246,291,299` `rng_next_range(rng, ...)`
- `src/app/cli/commands/test_batch.spl:69` `dir_list_recursive(dir)`
- `src/os/kernel/fs/win_vfs/win_vfs_driver.spl:145` `tree_readdir(tree, path)`; `:157` `tree_read(tree, path)`
- `src/compiler_rust/lib/std/src/tooling/dashboard/snapshots.spl:147` `date_diff_days(date, today)`
- `src/compiler_rust/lib/std/src/spec/formatter/markdown.spl:164` `path_file_exists(path)`

Known false positives of the regex (do NOT "fix" these): `me fn
cluster_to_sector` in `fat32_core.spl` (real method, the oracle's def regex must
allow `me fn`); `queue_send`/`queue_recv`/`queue_poll`/`queue_close` in
`src/os/kernel/ipc/syscall_spm.spl` (docstring text, not code); `lut_lookup` in
`backend_metal_msl.spl` (embedded MSL shader source); `is_lowercase`, `to_u64`
(builtins).

## Failure scenario

`hygiene.spl:239`'s `scope_lookup(scope, ident.name)` resolves to nothing.
Macro-hygiene identifier resolution therefore never finds an existing binding, so
`check_hygiene` on a macro expansion that shadows an outer name reports no
conflict where it should — a silently-skipped semantic check, not a crash.
Unresolved calls are only WARNINGS in pure-Simple, so a clean build is not
evidence against this.

## Why the sweeps missed them

Both commits sized the family from a hand-maintained tracking doc
(`impl_to_free_fn_refactor_family_sweep_2026-08-07.md`, "23 sites / 8 files")
plus a `self.`-scoped grep. Neither ran a definition-existence oracle over the
whole tree, so anything on a non-`self.` receiver or in an unlisted file was
invisible. `b0c98541d2a`'s own message notes the doc "undercounted" — that
observation was applied to four extra lines, not turned into a systematic sweep.

## Fix plan

Run the oracle above, restore each site, and re-run the oracle to zero before
declaring the family closed. Do NOT size the family from `unresolved call` build
warnings — that diagnostic samples rather than enumerates.

## Related

- `b0c98541d2a`, `bc052a4470d` (the two incomplete restorations)
- `doc/08_tracking/bug/impl_to_free_fn_refactor_family_sweep_2026-08-07.md`
- `.claude/rules/code-style.md` (native-codegen Dict pitfalls, applied by both commits)

## Update 2026-08-08 (session 3): the 6-site reconciled list closed 5/6

Per `doc/08_tracking/bug/two_standing_limits_independently_verified_2026-08-08.md`,
the reconciled genuine-survivor list was `template.spl:165`,
`effects.spl:117,353,361`, `recovery.spl:215`, `blocks/testing.spl:294` (6
sites). **5 of 6 fixed and landed** (commit `cd5286d33ec`):

- `effects.spl:117,353,361` — `Effect.is_async()`/`.is_sync()` recovered (not
  invented): `infer_promise_type_info` at `effects.spl:~316` already calls
  `infer_function_effect(func, env).is_async()`, pinning the method shape.
  Added `effect_is_async`/`effect_is_sync` free functions and restored the 3
  call sites to the `if val x = opt.?:` binding idiom
  (`doc/07_guide/quick_reference/syntax_quick_reference.md` § Existence
  Check) — the dangling `..._value` names were literally this idiom's
  binding names, dropped by the refactor.
- `recovery.spl:215` — same missing-binding shape, restored with
  `.get(0).unwrap().is_lowercase()` (precedent: `erlang.spl:54`). Also fixed
  the identical damage 4 lines away at `:170` (a bare dangling identifier,
  not a call — outside the oracle's regex shape, so never counted, but the
  same bug in the same function), using the file's own established
  `(next_lexeme ?? "") == "..."` idiom (`:193`,`:203`).
- `blocks/testing.spl:294` — `value_type_name(value: BlockValue)` added as a
  free function, mirroring the file's own `const_value_to_string(value:
  ConstValue)` precedent immediately below it. Zero callers exist tree-wide
  (dead test helper) — no calling convention to verify against beyond that
  in-file precedent.

**NOT fixed — `template.spl:165` `kind_can_follow(kind, prev_kind)`.**
Unlike the other 5, there is no sibling call site or in-repo prior
implementation pinning the semantics. Rust's macro_rules follow-set rules
(the file's own stated basis) constrain a fragment specifier against a
*following raw token*, not against another `FragmentKind` as this
`(kind, prev_kind)` signature requires — applying them here would be
translating the concept across a different domain, not recovering it, i.e.
inventing. The function body also references three OTHER undefined
identifiers in the same few lines (`prev_kind_value`, `has_sep`,
`sep_value`) that gate any real verification regardless of the
`kind_can_follow` fix. Left dead, per this family's own stated policy: a
wrong body is worse than a missing one. Two ways forward, neither taken:
(a) implement Rust's actual follow-set table projected onto fragment-vs-
fragment adjacency (a judgment call, needs a domain expert or an actual
spec written first), or (b) delete the check and the empty "FragmentKind
Methods" block outright. Recommendation: (b) is lower-risk until a spec
exists, since (a) ships an unverifiable invented rule.

**New adjacent finding, NOT fixed (separate defect, out of this family's
scope):** `effects.spl` calls `env_get(env, key)` and `env_contains(env,
key)` seven times as an in-file convention for `Dict<text, Effect>` access.
`env_contains` has **zero** definitions tree-wide, so it should have been a
survivor — but it escaped the oracle's shape-2 regex (`<X>_<Y>(<X>,...)`)
because the argument at its one non-underscore-suffixed call site is
`env_mut`, not `env`, and the regex backreferences the literal argument
text. `env_get(env, key)` (2-arg, `Dict<text,Effect>` lookup) escaped the
**definition**-existence half of the oracle because 17 unrelated 1-arg
`env_get(key: text) -> text` definitions exist elsewhere under the same
bare name — a second, distinct blind spot from the first (arity/type is
never checked, only name). Confirmed both are broken by isolated
`bin/simple compile` probes with a throwaway 2-arg stub: without a stub,
`effects.spl` fails at `env_get`; with `env_get` stubbed, it fails at
`env_contains`; with both stubbed, `infer_mutual_effects`'s whole
`env_get`/`env_contains`/`Dict<text,Effect>` cluster **as written cannot be
the flat bare-name-table `env_get` the file appears to assume** — under
this repo's rule against `.get()` on struct/enum-valued dicts (`Effect` is
an enum), the likely-correct restore is a locally-scoped
`effect_env_get`/`effect_env_contains` pair using
`contains_key`+index-read, not a reused bare `env_get` name (reusing it
would recreate the exact wrong-binding hazard documented for `args_len`
elsewhere in this family). Not fixed here — outside the assigned 6 sites,
and it makes `infer_function_effect`, `needs_await`, and `needs_await_typed`
(the 3 functions my 3 fixes live in) still functionally dead pending that
separate fix, even though their own unresolved-call errors are now gone.

RED->GREEN: grepped tree-wide `fn`/`me` definitions against an isolated
`origin/main` archive (MISSING for all 4 added names) vs. the fixed tree
(DEFINED); per-file `bin/simple compile` before/after shows the target
unresolved-identifier error is gone and the next error is unrelated
pre-existing damage. Push guards `check-no-conflict-tree-push`,
`check-no-conflict-markers-push`, `check-tree-size-push` all PASS on the
explicit landed range.

## Re-measurement 2026-08-17 — oracle 40 -> 25; and the oracle itself was fail-OPEN

Re-ran the tightened oracle against current source. **Two findings.**

### Finding 1: the documented oracle under-counts definitions (`me fn`)

The oracle's definition-extraction line

```sh
/usr/bin/grep -rEoh '\b(fn|me)[[:space:]]+[a-zA-Z0-9_]+' src/ --include=*.spl
```

is **wrong for the `me fn NAME` form**. `grep -o` matches non-overlapping, so on
`    me fn cluster_to_sector(...)` the alternation matches `me fn` first and the
trailing `sed 's/.*[[:space:]]//'` yields the literal name **`fn`** — the real
name is never emitted. **341 definitions were missing from `defs.txt`.** Every
one of them makes its call sites look like zero-definition survivors, i.e. the
oracle was fail-OPEN in the *false-positive* direction (it invents damage, it
does not hide it — so no previously-closed row is at risk, but the survivor
count was inflated). Confirmed instance: `fat32_core.spl:355,382`
`self.cluster_to_sector(cluster)` was reported as a survivor while
`fat32_core.spl:319` reads `me fn cluster_to_sector(cluster: u32) -> u64:`.

Corrected extraction:

```sh
/usr/bin/grep -rEoh '\b(fn|me)[[:space:]]+(fn[[:space:]]+)?[a-zA-Z0-9_]+' src/ --include=*.spl \
  | /usr/bin/sed -E 's/.*[[:space:]]//' | sort -u > defs.txt
```

Definition count: 100,070 -> 100,411.

### Finding 2: corrected count is 25 (was 40)

With the corrected `defs.txt`, the tightened extraction (emit only the callee
whose first argument re-passes its own prefix, `<X>_<Y>(<X>`) yields **25**
surviving zero-definition call sites, down from the 08-08 figure of 40.

Oracle self-test (fail-closed, run before accepting the count):

| injected line | expected | observed |
|---|---|---|
| `zzq_frobnicate(zzq, 1)` — zero-def, prefix re-passed | +1 | 27 -> 28 ✓ |
| `parse_or(parse, 1)` — callee HAS a definition | +0 | 27 ✓ |
| `zzq_frobnicate(other, 1)` — zero-def, prefix NOT re-passed | +0 | 27 ✓ |

(Self-test was run against the pre-correction 27-baseline; the correction to
`defs.txt` then moved the baseline to 25.)

### The 25 survivors

| file:line | callee | class |
|---|---|---|
| `src/compiler/10.frontend/desugar/desugar_async.spl:44` | `response_text` | A |
| `src/compiler/15.blocks/blocks/definition.spl:60` | `parser_set_mode` | A |
| `src/compiler/15.blocks/blocks/definition.spl:61` | `parser_parse_expr` | A |
| `src/compiler/15.blocks/blocks/easy.spl:113` | `pattern_trim` | A |
| `src/compiler/15.blocks/blocks/registry.spl:26,182` | `blk_lexer_mode` | A |
| `src/compiler/90.tools/desugar_async.spl:42` | `response_text` | A |
| `src/compiler_rust/lib/std/src/spec/formatter/markdown.spl:164` | `path_file_exists` | A |
| `src/lib/gc_async_mut/gpu/engine2d/engine.spl:1229,1234,1239,1244` | `vulkan_*` (4 distinct) | A |
| `src/compiler/70.backend/backend/exhaustiveness_validator.spl:474` | `sys_exit` | C — stdlib gap |
| `src/lib/nogc_sync_mut/fuzz.spl:164,169,199,231,246,291,299` | `rng_next_range` | C — missing module |
| `src/os/kernel/ipc/syscall_spm.spl:396,406,419,423` | `queue_*` | false positive (docstring) |
| `src/lib/gc_async_mut/gpu/engine2d/backend_metal_msl.spl:986` | `lut_lookup` | false positive (MSL shader source) |

**12 Class A (actual refactor damage)** + 8 Class C + 5 known false positives.

`engine.spl:1229-1244` (4 sites) is **newly surfaced** — not listed in the
08-08 "remaining Class A" set.

### Scope note: `src/compiler/00.common/**` is CLEAN

**Zero of the 25 survivors are under `src/compiler/00.common/**`** — the path
this doc names as its primary location. `predicate_parser.spl:125`, the one
`00.common` site the 08-08 pass recorded as fixed, is confirmed fixed in current
source: `if new_pos < tokens.len():`. (8 raw regex hits fall in `00.common`, all
of which resolve to real definitions and are dropped by the def-filter.)

Consequently **all 12 remaining Class A sites belong to other lanes**
(`10.frontend`, `15.blocks`, `70.backend`, `90.tools`, `src/lib`, `compiler_rust`)
and were deliberately not edited in this pass.
