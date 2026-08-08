# R2 primitive-use check — implementation draft

## ✅ RESOLVED 2026-06-16 — text-based, integrated on the LSP/build path

R2 is **done**. The arena approach below was abandoned (it hit two infrastructure walls — see
"Bootstrap attempt result"). The breakthrough: the `primitive_api` check already existed as a
**text-based** lint on the compiled CLI engine
(`compiler.tools.fix.rules.impl_.lint_primitive_api.check_primitive_api`, wired in
`90.tools/lint/_LintMain/lint_checks.spl:225`, with easyfix wrapper suggestions = the auto-fix feature).
The only gap was the **LSP/build path** (`query_lint`), which never surfaced it.

Fix (landed in `src/app/cli/query_lint.spl`): a tier-gated text emitter `_emit_primitive_api_text`
that reuses `param_tag`'s exported signature parsers (no parser, no `parse_module`, no arena — so
it dodges BOTH walls). It mirrors the canonical lint exactly (pub fns, params + return, pure-math
exemption, excludes `bool`). `primitive_api` was already in `_governed_lint_codes()`, so the
existing `_DIAG_SEVERITY_OVERRIDE` map routes severity by tier.

**Verified end-to-end** through the real `bin/simple run src/app/cli/query.spl check <file> --format json`:

| tier | result |
|------|--------|
| `@lint_profile(reliable)` | `primitive_api` severity **1** (deny) on `x:i64` param + `f64` return; `label:text` NOT flagged |
| `@lint_profile(lib)` | severity **1** (deny) |
| `@lint_profile(moderate)` | severity **2** (warn — P0 downgrades deny→warn) |
| no profile | **silent** (legacy LSP behavior unchanged — zero default-path change) |
| pure-math `add(a:i64,b:i64)->i64` | **silent** (exemption); mixed `mix(i64,f64)->i64` flagged |

Remaining R2 nice-to-have (separate, needs a compiled-path change + bootstrap): extend coverage
from pub-only to **internal** fns under the reliable tier — change the canonical
`lint_primitive_api` + `query_lint` emitter to also scan non-pub `fn`/`me` when reliable.

---

## Original arena draft (superseded — kept for history)

Implemented the reliable-tier arena-AST primitive check in `src/app/cli/query_lint.spl`,
verified the logic, then **reverted from the live file** because end-to-end verification hit a
flaky interpreter module-load failure (below). The code is correct-by-construction; it needs
the load issue isolated, then re-applied + verified via `_collect_lint_diagnostics_json`.

## Findings (resolve these to land — they de-risk the rest)
1. **`_run_ast_lint_passes` is DEAD** — `grep` shows **zero callers**; the LSP/build collect
   path (`_emit_source_lint_diagnostics`) only runs `_emit_basic_line_lints` +
   `_emit_text_heuristic_lints`. So all its AST checks (ARG001, COLL, STUB…) are inactive in
   LSP. Wire the primitive check via a **separate tier-gated entry called from
   `_emit_source_lint_diagnostics`**, not `_run_ast_lint_passes`.
2. **Open type-representation item RESOLVED:** `decl_get_param_types(idx)` / `decl_get_ret_type(idx)`
   return type **tags**; `type_tag_name(tag)` resolves them (`type_tag_name(1) == "bool"`,
   confirmed). Import `type_tag_name` from **`compiler.core.ast`** (it re-exports it,
   `__init__.spl:663`) — importing `compiler.core.types` directly conflicts in `query_lint`'s graph.
3. **BLOCKER — flaky module load.** With the R2 additions, `bin/simple run` importing
   `app.cli.query_lint` intermittently fails with `error[E1002]: function LintConfig not found`
   (or produces no output) — yet `bin/simple check query_lint.spl` is clean (parse-OK) and the
   imports load fine in a minimal standalone combo. Smells like the interpreter's module-load is
   order/count-sensitive once `query_lint`'s already-large import graph grows. **Likely fix:** put
   the primitive check in its **own new module** (e.g. `src/compiler/35.semantics/lint/primitive_api_arena.spl`)
   exporting `check_primitive_api_arena(decl_indices) -> [..]`, and import just that into
   `query_lint` — keeping query_lint's import set minimal. Then verify.

## Verification (once it loads)
`_collect_lint_diagnostics_json("@lint_profile(reliable)\n\nfn calc(x: i64, label: text) -> f64:\n  1.0\n")`
→ expect `primitive_api` at severity 1 for `x:i64` and the `f64` return (not `label:text`);
without the tier → none (gated). Run from a file **inside the repo** (not `/tmp`) for stable
module resolution.

## Implementation (copy-paste ready)
Imports (extend the existing `compiler.core.ast` line; do NOT add `compiler.core.types`):
```simple
use compiler.core.ast.{ast_reset, module_get_decls, decl_tag, decl_name, decl_get_param_names, decl_get_param_types, decl_get_ret_type, DECL_FN, type_tag_name}
```
Tier flag — set in `_load_lint_config_for` (`val tier_on = cfg.profile.? or cfg.levels.len() > 0`; `_LINT_TIER_ACTIVE = tier_on`):
```simple
var _LINT_TIER_ACTIVE = false
```
The check + live entry (call `count = count + _emit_primitive_api_tier(source, file)` in `_emit_source_lint_diagnostics` before `_clear_lint_config_overrides()`):
```simple
fn _is_bare_primitive_type_name(n: text) -> bool:
    (n == "i8" or n == "i16" or n == "i32" or n == "i64"
     or n == "u8" or n == "u16" or n == "u32" or n == "u64"
     or n == "f32" or n == "f64" or n == "bool")

fn _emit_primitive_api_arena(decl_indices: [i64], lines: [text], file: text) -> i64:
    var count = 0
    for idx in decl_indices:
        if decl_tag[idx] != DECL_FN:
            continue
        val fname = decl_name[idx]
        val ptypes = decl_get_param_types(idx)
        val pnames = decl_get_param_names(idx)
        val rtype = decl_get_ret_type(idx)
        val rtname = type_tag_name(rtype)
        # pure-math exemption: all params + return one shared primitive
        var all_same_prim = _is_bare_primitive_type_name(rtname)
        var k = 0
        while k < ptypes.len():
            val tn = type_tag_name(ptypes[k])
            if tn != rtname or not _is_bare_primitive_type_name(tn):
                all_same_prim = false
            k = k + 1
        if all_same_prim and ptypes.len() > 0:
            continue
        val line_num = _find_fn_line_in_source(lines, fname)
        var pi = 0
        while pi < ptypes.len():
            val tname = type_tag_name(ptypes[pi])
            var pname = "?"
            if pi < pnames.len():
                pname = pnames[pi]
            if pname != "self" and _is_bare_primitive_type_name(tname):
                _diag_emit_or_collect("{\"severity\":2,\"code\":\"primitive_api\",\"message\":\"bare primitive '{tname}' in parameter '{pname}' of '{fname}' — wrap in a domain type\",\"line\":{line_num},\"col\":1,\"end_line\":{line_num},\"end_col\":1,\"tags\":[],\"source\":\"simple-lint\"}")
                count = count + 1
            pi = pi + 1
        if _is_bare_primitive_type_name(rtname):
            _diag_emit_or_collect("{\"severity\":2,\"code\":\"primitive_api\",\"message\":\"bare primitive '{rtname}' return type of '{fname}' — wrap in a domain type\",\"line\":{line_num},\"col\":1,\"end_line\":{line_num},\"end_col\":1,\"tags\":[],\"source\":\"simple-lint\"}")
            count = count + 1
    count

fn _emit_primitive_api_tier(source: text, file: text) -> i64:
    if not _LINT_TIER_ACTIVE:
        return 0
    ast_reset()
    parse_module(source, file)
    val decls = module_get_decls()
    if decls.len() == 0:
        return 0
    val lines = source.split("\n")
    _emit_primitive_api_arena(decls, lines, file)
```
Severity is then governed by the R1-step-3 override map (moderate→suppress, lib/reliable→deny on `primitive_api`).

## Bootstrap attempt result (2026-06-16) — BOTH integration paths blocked by infrastructure
The CLI-engine route was attempted under explicit authorization: wired
`check_primitive_api_arena` into the **compiled** `90.tools/lint/_LintMain/lint_checks.spl` (tier-gated,
before the config filter) and ran `bin/simple build bootstrap`. **Stage 1 failed** (`native-build
--source src/app … exit 248`): because `query_lint` is script-run, the parser was never in the
compiled binary's closure; importing `compiler.core.parser` + AST into the compiled lint engine
pulled the whole parser into the CLI native-build closure for the first time, bloating it past
the build timeout. `bin/simple` was unharmed (stage1 builds to `bootstrap/stage1/`, never
deployed; md5 identical to pre-attempt backup). Reverted.

**Conclusion:** R2's arena check (landed, correct) cannot be integrated into *either* lint
engine this session without infrastructure work outside pure-Simple lint code:
- LSP/`query_lint` (script-run) → interpreter `parse_module` crash (`interp_parse_module_arena_visibility_crash_2026-06-16`).
- CLI/`main_part2` (compiled) → importing the parser bloats the bootstrap native-build → fails.
Real next step is one of: fix the interpreter crash (unblocks the LSP path cleanly), or give the
arena lint a parser-free way to obtain decls / raise the native-build timeout/closure budget.
