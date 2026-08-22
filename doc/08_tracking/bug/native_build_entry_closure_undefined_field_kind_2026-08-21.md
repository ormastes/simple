# native-build --entry-closure fails with span-less `undefined field 'kind'`

Filed: 2026-08-21
Status: OPEN
Severity: blocker — no MCP or LSP-MCP native artifact can be built from `origin/main`

## Symptom

```
SIMPLE_CACHE_SCOPE=mcp bin/release/x86_64-unknown-linux-gnu/simple native-build \
  --runtime-bundle core-c-bootstrap --source src/app --entry-closure \
  --entry src/app/mcp/main.spl --strip --threads 2 \
  --output build/mcp-sanity/simple_mcp_server
```

fails after ~1972 s with exactly one error:

```
error: semantic: undefined field 'kind': cannot access field on value of type 'nil'
error: native-build worker exited with code 1
```

The sibling entry `src/app/simple_lsp_mcp/main.spl` fails identically (~435 s).
`src/app/simple_lsp_mcp/**` contains **no** `.kind` access at all, so the defect
is in shared code reached through the entry closure, or in the driver itself.

## Why it is hard to diagnose (three separate defects)

1. **The diagnostic has no file/line span.** It is the only error emitted. Every
   other diagnostic in the same stream carries a `--> path:line:col`.
2. **It fires after every instrumented source reports clean.** The line
   immediately preceding it is
   `[bootstrap-error-count] source_idx=2 point=post-store count=0`, with
   `count=0` at all four points for all three sources. So this is not an
   ordinary source-compile error; it is on the post-store entry-closure /
   codegen path.
3. **The driver truncates worker stderr from the middle** — "TRUNCATED: 16945 of
   28945 bytes of worker stderr were dropped from the MIDDLE" — discarding
   whatever context would localize it.

## Evidence

- Full preserved stderr: `/mnt/data/tmp/native-build-stderr-359022.log`
  (MCP entry) and `/mnt/data/tmp/native-build-stderr-321437.log` (LSP entry);
  the error is at line 806 in the latter.

## Relationship to the fixed blocker

This is the *next* wall past the HIR-lowering failure in
`src/lib/common/text_advanced.spl` fixed by `5c285c2436f`. Before that fix the
build never reached this point. The `text_advanced` diagnostics are confirmed
absent from post-fix build logs.

## Fix directions

- Attach a span to the `undefined field` diagnostic — worth doing regardless,
  since it blocks localization of this and every future instance.
- Stop truncating worker stderr from the middle, or preserve all `error:` lines
  (the driver already has a "PRESERVED DIAGNOSTICS" mechanism; it preserved
  only 2 lines here).
- Locate the unguarded `.kind` read on a nil receiver on the post-store
  entry-closure path.

## Repro cost

~33 min per attempt for the MCP entry, ~7 min for the LSP entry; prefer the LSP
entry for iteration.

---

## Update 2026-08-22 — localized, two traps fixed, one still open

### How to localize it (this is the reusable part)

The diagnostic is span-less, but the seed already ships the instrumentation:

```
SIMPLE_DEBUG_FIELD_ACCESS=1   # or SIMPLE_BOOTSTRAP_DIAG=1
```

gated at `src/compiler_rust/compiler/src/interpreter/expr/calls.rs:1046`
(`field_access_debug_enabled()`). It prints the field, receiver type, receiver
value, the receiver *expression*, and a 12-frame Simple-level call stack. No
rebuild needed. That turned a span-less error into an exact location in one run:

```
[field-access-error] field=kind recv_type=nil recv=nil expr=Identifier("t")
  stack=lower_and_check_impl -> run_any_escape_pass -> any_escape_check
     -> any_check_function -> any_check_block -> any_check_stmt
     -> any_check_block -> any_check_stmt -> any_type_is_any
```

Note this only covers the *non-enum* arm. The sibling arm at `calls.rs:1032`
("unknown property or method '<f>' on <enum>") has **no** debug branch, which is
why the follow-on `Option` trap below could not be localized the same way.
Adding the same branch there is a worthwhile fix.

### Correction to the original analysis

"The error fires after post-store" was **wrong**. `[bootstrap-error-count]` is
emitted only `if source_idx < 3`
(`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:430,526,625`), so the
last `source_idx=2` line is an artifact of that cap, not a phase marker. The
trap is in ordinary HIR lowering / semantic checking of a later module.

### Trap 1 — FIXED

`src/compiler/35.semantics/any_escape/checker.spl`, `any_check_stmt`,
`case Let(symbol, type_, init)`: called `any_type_is_any(type_)` /
`any_type_mentions_any(type_)` directly. `HirStmt.Let`'s `type_` is absent for
an inferred binding (`val x = e`), and `any_type_is_any(t: HirType)` opens with
`match t.kind` — hence `kind` on `nil`. The very next lines already nil-check
`symbol`, so nil payloads were known to occur here. Now unwrapped with `if val`
(not `.unwrap()`, which is box-assuming and breaks flat optionals on the stage4
native lane). Both predicates ask about the DECLARED type, and an inferred
binding has none; inference-side erasure is still covered by `any_expr_is_any`
on `init`, so no check is lost.

### Trap 2 (latent, also fixed)

`src/compiler/20.hir/hir_lowering/_Items/module_callable_types.spl`,
`declared_callable_type`: passed `Param.type_` to `lower_type` with no
`has_type_` guard, while the sibling `declared_surface_callable_type` 34 lines
below does guard. An untyped parameter would trap identically in
`20.hir/hir_lowering/types.spl:442`. Fixed by returning nil, matching this
function's own policy for every other "cannot form a complete declared
signature" case. This was **not** the blocker (the build failed identically with
it fixed) but it is a real latent defect of the same class.

### Still OPEN — trap 3

With trap 1 fixed the `nil` receiver is gone (0 `[field-access-error]` lines),
and the build now fails with:

```
error: semantic: undefined field: unknown property or method 'kind' on Option
```

i.e. a `.kind` read on a *wrapped* `Some(...)` rather than a bare nil, at a site
that is **not** the one fixed above (verified: the fix is present in the file and
the pipeline demonstrably recompiles the edited compiler source). Candidate call
sites, all passing a desugared-optional slot into the same two predicates:
`checker.spl:150` (`e.has_type_ and any_type_is_any(e.type_)` — `has_type_`
proves presence but the value stays wrapped), and `:290, :639, :651, :666, :707`.

Blanket `eprintln` instrumentation of those call sites is **not** viable as
written — several are match arms / `elif` continuations, and injecting a
statement before them is a parse error. Instrument individually, or add the
missing debug branch at `calls.rs:1032` and re-run with
`SIMPLE_DEBUG_FIELD_ACCESS=1`.

### Regression evidence for the fixes

- `test/01_unit/compiler/semantics/any_escape/` — 14/14 pass.
- `test/01_unit/compiler/hir/untyped_param_declared_callable_type_spec.spl` —
  new, 5/5 pass (covers free fn, mixed typed/untyped, no declared return,
  method, and static fn with untyped params).

### Iteration cost

Use the LSP entry (~7.5 min) not the MCP entry (~33 min) to iterate.
