# lint_coll006 — COLL006 false positive on integer accumulators

**Status:** FIXED (uncommitted working copy, 2026-07-28)
**Owner file:** `src/compiler/35.semantics/lint/collection_patterns.spl`

## Root cause
`is_string_concat_assign_expr` matched any `x = x + <non-array-literal>` inside a
loop, with no type evidence. Registered as Deny at
`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:57`, so every integer
loop counter became a lint **error**.

## Fix (not a severity downgrade — severity is unchanged at CRITICAL/Deny)
COLL006 now requires positive *text* evidence. The lint runs on the freshly
parsed arena AST, before type inference, so the only available type facts are
syntactic:
- declared annotations: `stmt_type_tag[s] == TYPE_TEXT`, `decl_param_types[i] == TYPE_TEXT`
- text-valued expressions: string literal, interpolated string, a conservative
  list of text-returning methods (`to_text`, `join`, `trim`, `substring`, ...),
  or a `+` whose either side is text-valued

New helpers: `is_text_returning_method`, `is_text_valued_expr`, `name_in_list`,
`fn_param_text_names`, `collect_text_var_names` (whole-body pre-pass so
declaration order does not matter). `check_collection_patterns` threads the
resulting `text_vars` list into `check_fn_body` / `check_loop_body`.

The same pass also fixed a **false negative**: the prepend form `s = x + s` is
equally O(n^2) and was never reported.

## Evidence (`build/coll6_repro/`)
Repro files must live outside `build/` when linting (`bin/simple lint` skips
`build/`); runs were made from `/tmp/coll6/` copies.

| target | before | after |
|---|---|---|
| `nostring.spl` (7 lines, no string at all) | 2 COLL006 errors | 0 |
| `yesstring.spl` (`s = s + "x"` + `i = i + 1`) | 2 | 1 (the real one) |
| `mixed.spl` (text + i64 + f64 accumulators) | 3 | 1 (the real one) |
| `src/os/apps/ssh_client/ssh_known_hosts.spl` | 5 | 0 |
| `src/os/port/sqlite/sqlite_vfs_impl.spl` | 3 | 0 |
| `src/os/kernel/memory/vmm_shared.spl` | 13 | 0 |
| `src/lib/common/config_core/schema.spl` (known false negative) | 0 | **1** (now caught) |

Code histograms before/after are otherwise identical — no new findings of any
rule. (A LEADOP001 delta seen in one early pair was independent flake: it also
disappears with the unmodified HEAD rule file.)

## Sibling matchers — same missing type check
- **COLL002 `is_contains_call`** — matches *any* `.contains()` by name; fires on
  `Dict`/`Set` (O(1)) and on `text.contains(sub)`. Real false-positive class,
  but severity HIGH => Warn, so it does not break the gate.
- **COLL004 `is_loop_invariant_call`** — flags `.len()/.is_empty()/.first()/.last()`
  on any non-loop-var ident, even when that receiver is mutated in the loop
  (`out.push(..); out.len()`), i.e. not actually invariant.
- **COLL007 `is_array_rebuild_pop`** — matches any `x = x[..]` slice of the same
  variable, not specifically `x[0..len-1]`; `s = s[1..]` (cursor advance) and
  text slices are mislabelled "rebuild to remove last element".
- **COLL008 `check_unbounded_globals`** — treats *every* module-level `var` as a
  global array (the code comments admit it) and flags any `.push()` on it.
- **COLL001 `is_concat_assign_expr`** — sound: requires an `EXPR_ARRAY_LIT` on
  the RHS, which is unambiguous. Only gap is a false negative
  (`arr = arr + other_arr`).

None of the siblings is Deny-registered, so COLL006 was the only gate-breaker.

## Not done
- Not committed / not pushed (lane scope).
- Sibling fixes above are reported only.
