> **RESOLVED 2026-08-18.** The split is closed in favour of the SENTINEL
> contract, which is what `find`/`rfind`/`index_of` have always actually
> implemented (`-1` = miss) and what the interpreter deliberately kept. A
> repo-wide audit found exactly **6** wrong consumers, all of them the three
> copies of `std.path`: `src/lib/nogc_sync_mut/path.spl:23,37`,
> `src/lib/gc_async_mut/path.spl:23,37`,
> `src/lib/nogc_async_mut_noalloc/path/baremetal_path.spl:54,71`. Each matched
> `Some(idx)/nil` on the sentinel, so the `Some` arm always won and bound
> `idx = -1`, leaving the `nil` arm dead. Every other stdlib consumer
> (`dependency_tracker/graph.spl`, `test_runner_execute.spl`,
> `editor/extensions/contract.spl`, `web/browser_session.spl`,
> `blink/layout/block_flow.spl`) already tested `< 0` correctly, so no
> repo-wide migration was needed and no MIR lowering change was made.
>
> RED: `dirname("foo.txt")=[]`, `extension("README")=[README]`,
> `stem("README")=[]`. GREEN: `Results: 4 total, 4 passed, 0 failed` on both
> `test/01_unit/lib/path/path_rfind_sentinel_not_found_spec.spl` (independently
> proven RED at `4 total, 1 passed, 3 failed` with the fix stashed — the single
> pass is its positive control) and
> `test/01_unit/lib/path/text_search_sentinel_contract_spec.spl`.
> TODO-DB row 559 closed.

# rfind: sentinel (-1) vs Optional contract split across stdlib call sites

- Date: 2026-08-18
- Area: compiler (MIR lowering) + lib (stdlib call sites)
- Priority: P1
- Origin: todo_db.sdn row 559 — "Preserve Optional not-found semantics when
  bootstrap MIR lowers rfind on an erased text receiver."
- Status: OPEN (root cause identified; fix deliberately NOT applied — see
  "Why no unilateral fix")

## Reproduction (Cranelift JIT, seed `bin/simple`)

Binary identity, recorded before AND after the run (unchanged across it):
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
`59581296 2026-08-18 00:21:41.473315499 +0000`.

Probe: annotated receiver (`val s: str = "abc/def/ghi"`) and erased receiver
(`val e = "abc/def/ghi".replace("x","y")`), needle present and absent.

```
ann found: 7
ann nf: -1
erased found: 7
erased nf: -1
empty needle: 11
empty hay: -1
BAD: ann nf not nil
BAD: erased nf not nil
```

Findings:
- Not-found returns the raw sentinel **-1**, never nil/None.
- The **erased and annotated receivers behave IDENTICALLY**. The row's framing
  ("erased receiver loses the semantic") is not what is happening: nothing is
  lost by erasure, because the Optional was never produced on either path.

## Root cause (lowering site)

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
- line 2331 — the text-special dispatch arm accepts `rfind`
- line 2387 — `case "rfind": "rt_string_rfind"`
- lines ~2402-2415 — `ts_dest_ty` falls to the default `case _: MirType.i64()`
- lines 2435-2441 — only `parse_f64` calls `remember_local_hir_type(...,
  HirTypeKind.Optional(...))`. `find`/`rfind` get **no** Optional HIR type and
  no -1 -> nil adaptation.

So the lowered result is a plain `i64` carrying `-1`. That is what the runtime
owner `rt_string_rfind` returns.

## The interpreter agrees — this is not a cross-engine divergence

`src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl:259-268`
returns `val_make_int(s.last_index_of(r_needle))`, i.e. raw i64 with -1 on a
miss. Its in-source comment records that a previous `?? -1` Optional-ish
treatment was **deliberately removed**, because it was dead on a miss and
actively CORRUPTED a genuine hit at index 3 (index 3 collides with the nil
sentinel, `TAG_SPECIAL = 0b011`).

Both engines therefore implement the same -1 contract. Per-engine result:
- Cranelift JIT (`bin/simple run`): -1 on miss (executed, quoted above).
- Tree-walk interpreter (`bin/simple test`): -1 on miss (SOURCE-VERIFIED only;
  a spec run was not launched — host was at load ~67 with earlyoom actively
  SIGTERMing `simple` processes, see the capacity note below).

## The actual defect: stdlib call sites disagree with each other

88 `.rfind(` call sites under `src/`. Two mutually exclusive conventions are
BOTH live, and the sentinel one is the one the compiler implements:

Sentinel style (correct against today's lowering):
- `src/lib/nogc_sync_mut/fs/path.spl:69-71` — `if last_sep < 0: return nil`

Optional style (SILENTLY WRONG against today's lowering):
- `src/lib/nogc_sync_mut/path.spl:23-27` —
  `match last_sep: Some(idx): idx / nil: return "."`
  With a raw `-1`, the `nil` arm can never be taken, so `dirname("noslash")`
  falls into `Some(idx)` with `idx = -1` and returns
  `clean_path.substring(0, -1)` instead of `"."`. Exactly the
  "plausible wrong result" class the row warns about.

Roughly 6 such Optional-shaped `rfind` uses exist under `src/lib/`.

## Why no unilateral fix

Flipping `rfind` alone to a real Optional in the lowering would:
1. break every `< 0` / `== -1` sentinel call site (the majority of the 88),
2. desynchronise `rfind` from `find` / `index_of`, which share the same
   documented -1 contract, and
3. re-open the index-3 / nil-sentinel corruption that the interpreter comment
   above records as an already-landed, deliberate fix.

This is a repo-wide API contract decision, not a one-line lowering patch. The
two candidate resolutions:

- **A (sentinel wins, smaller):** keep -1 everywhere; fix the ~6 Optional-shaped
  stdlib call sites to test `< 0`; add a lint that rejects `match <rfind>:
  Some(..)`.
- **B (Optional wins, larger):** move `find`/`rfind`/`index_of` together to a
  canonical Optional representation that does not alias index 3 with the nil
  tag, update all 88 sites, and update both engines in the same change.

Either way `find` and `index_of` must move with `rfind`; doing `rfind` alone is
how the split was created.

## Capacity note

Host was saturated during this investigation (125 GB total / ~33 GB available,
load ~67, 83 concurrent `simple` processes, earlyoom issuing SIGTERM at
`badness 1005`). A spec run was therefore not attempted: an exit-143 kill is not
a test result. Deferred command for whoever picks this up:

```
bin/simple test test/01_unit/lib/text/rfind_optional_spec.spl
```
