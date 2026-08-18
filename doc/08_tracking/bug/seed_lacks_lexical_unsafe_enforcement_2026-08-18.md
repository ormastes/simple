# Rust seed accepts raw-pointer / SFFI / inline-asm operations outside `unsafe:`

- **TODO-DB row:** 557 (`doc/08_tracking/todo/todo_db.sdn:559`), area=compiler, P1, status=open
- **Row text:** "Enforce lexical unsafe scope in the Rust seed so raw pointer, SFFI, and
  inline-assembly operations are rejected outside UnsafeBlock."
- **Row note:** "danger:/unsafe: now retain an UnsafeBlock marker through HIR and erase it at
  MIR; the Rust seed does not yet have the pure compiler's in_unsafe safety pass"
- **Date:** 2026-08-18
- **Status of this document:** SOURCE-VERIFIED, **NOT EXECUTION-VERIFIED**. Nothing here was
  run. See "Deferred verification" at the bottom for the exact commands.

## Verdict

The row's claim is **accurate for the seed** and **needs one correction for the pure side**.

| | lexical scope tracked? | raw ptr / SFFI / asm outside `unsafe:` rejected? |
|---|---|---|
| Rust seed (`src/compiler_rust/`) | **No** — no `in_unsafe` concept anywhere | **No** — accepted silently, no diagnostic exists |
| Pure Simple (`src/compiler/`) | **Yes** — wired and working | **Only under `critical`/`verified` profile**; Advisory (log-only) by default |

So this is a real hole in the seed, and a *deliberate, documented migration window* — not a
hole — in the pure compiler. Any fix must not be described as bringing the seed to parity with
a pure compiler that "rejects", because by default the pure compiler does not reject either.

## Census — where unsafe scope IS (and is not) tracked

### Pure Simple compiler — real, wired, lexical

`src/compiler/35.semantics/safety_checker.spl` is the `in_unsafe` pass the TODO row refers to.

- `SafetyContext.in_unsafe: bool` — `safety_checker.spl:78`, initialised false at `:91`
- Lexical enter/exit on the HIR `UnsafeBlock` marker — `safety_checker.spl:471-476`
  (saves `was_unsafe`, sets true, recurses, restores — correct nesting)
- Rule: inline asm outside unsafe — `safety_checker.spl:480` -> `SafetyError.InlineAsmOutsideUnsafe`
- Rule: `asm match` outside unsafe — `safety_checker.spl:491` (added after it fell through
  the wildcard unchecked; see `safety_checker_pass_never_invoked_2026-07-27.md`)
- Rule: direct call to raw-pointer primitive or module extern fn outside unsafe —
  `safety_checker.spl:566` -> `safetychecker_flag_callee`

**It is invoked.** `src/compiler/80.driver/driver_hir_pipeline_passes.spl:149-153` constructs
`SafetyChecker.create()` and calls `safetychecker_check_module` /
`safetychecker_check_transfer_module_with_policy`.

**But its severity is profile-gated and defaults to log-only.**
`src/compiler/80.driver/driver_safety_severity.spl` defines
`SafetyPassSeverity { Advisory, Warn, Deny }` and `safety_pass_severity_for_name`:
`robust` -> Warn, `critical`/`verified` -> Deny, **everything else including unknown/empty ->
Advisory** (log-only via `SIMPLE_SAFETY_WARN`, never reaches the compile context). This is an
explicit settled decision (2026-07-28) creating a migration window, not an oversight.

HIR marker retained at `src/compiler/20.hir/hir_definitions.spl:575`
(`UnsafeBlock(body: HirBlock)`), lowered at
`src/compiler/20.hir/hir_lowering/expressions.spl:1058-1060`.

### Rust seed — marker retained, then dropped on the floor

The `UnsafeBlock` marker survives the whole frontend and is then erased with **zero checks
performed against it**:

- Parser produces it — `src/compiler_rust/parser/src/parser_impl/core.rs:913`
- AST variant — `src/compiler_rust/parser/src/ast/nodes/core.rs:776` (`UnsafeBlock(Vec<Node>)`)
- HIR variant — `src/compiler_rust/compiler/src/hir/types/expressions.rs:114`
  (`UnsafeBlock(Vec<HirStmt>)`) — **the site cited by the TODO row**
- HIR lowering — `src/compiler_rust/compiler/src/hir/lower/expr/control.rs:1747`
  `lower_unsafe_block`, building `HirExprKind::UnsafeBlock` at `:1762`. Its own doc comment
  says "Lower a lexical unsafe block…" (`control.rs:1745`) — the lexicality is preserved in
  the tree but never consulted.
- **MIR erasure** — `src/compiler_rust/compiler/src/mir/lower/lowering_expr.rs:234`:
  `HirExprKind::UnsafeBlock(stmts) => self.lower_block_expr(stmts)` — indistinguishable from
  a plain block from here on.

Every other seed site that mentions `UnsafeBlock` treats it as a **transparent statement
container** and recurses into it, i.e. it is deliberately made invisible rather than checked:
`compilability.rs:828`, `security.rs:1372`, `symbol_analyzer.rs:288`, `macro/hygiene.rs:519`,
`i18n/extractor.rs:313`, `pipeline/native_project/discovery.rs:243`,
`parser/src/effect_inference.rs:205`, `driver/src/cli/check.rs:1023` and `:1244`,
`driver/src/cli/code_quality.rs:377`, and the four `lint/checker_*.rs` walkers — all match
`Expr::DoBlock(x) | Expr::UnsafeBlock(x)` in a single arm.

**No `in_unsafe`-equivalent state exists in the seed.** Exhaustive grep for
`in_unsafe` / `unsafe_depth` / `is_unsafe` state over `src/compiler_rust/**/*.rs` (excluding
`vendor/` and `target*/`) yields no context flag and **no "requires unsafe" diagnostic string
of any kind**.

The one adjacent function, `is_unsafe_operation(name)` at
`src/compiler_rust/compiler/src/effects.rs:191`, is called from exactly one place —
`has_side_effects` at `effects.rs:205` — i.e. it feeds `@pure` inference, **not** unsafe-scope
enforcement. `mir/effects.rs:197,342,631` (`is_unsafe`) likewise classify an effect for
capability purposes and never consult lexical position.

### Dead duplicate — do not mistake this for the pass

`src/compiler/35.semantics/unsafe.spl` (256 lines) looks like the pure compiler's unsafe pass
and is **not**. It is a complete-looking but entirely dead module: `UnsafeContext` with
`unsafe_depth`/`enter_unsafe`/`exit_unsafe` (`:83-113`), `is_unsafe_op` (`:166`),
`check_unsafe_context` (`:220`), `require_unsafe` (`:228`), `validate_unsafe_block` (`:232`).

Grep for every one of those symbols across `src/` and `test/` returns **one line each** — the
re-export at `src/compiler/35.semantics/__init__.spl:103`. There is no traversal function at
all, `enter_unsafe` is never called (so `unsafe_depth` is permanently 0), and nothing invokes
`require_unsafe`. It also has a latent correctness bug should it ever be wired:
`is_sffi_function` (`:207-217`) returns `false` for the `HirExprKind.Var` case with the comment
"Cannot determine SFFI status from SymbolId alone", so the FfiCall rule would never fire for an
ordinary direct call. The live pass is `safety_checker.spl`, which resolves this by matching
`NamedVar(_, callee_name)` (`safety_checker.spl:566-570`) and carrying an `extern_fns` list.

**Recommendation:** delete `unsafe.spl` and its `__init__.spl:103` re-export. Per
`.claude/rules/code-style.md` ("NEVER add unused code — delete completely") it is dead weight
that actively misleads exactly this investigation. Not done here because deletion touches the
semantics `__init__` export surface and could not be execution-verified this session.

## Why no code was changed

The row scopes the work to the Rust seed. Landing a seed change requires a rebuild to observe
any behavioural effect, and a seed rebuild was forbidden this session (it would clobber ~15
parallel lanes). The fallback compile-only proof, `cargo check --release --bin simple`, was
also explicitly withdrawn mid-session on host-capacity grounds: `earlyoom` was actively
SIGTERMing `simple` processes (104/125 GB used, 21 GB available, 83 concurrent `simple`
processes, load 69-72, zero swap), and a release `cargo check` on this crate would either be
OOM-killed or push the box further into the kill zone.

Writing several hundred lines of Rust that could not even be shown to compile would be a
liability, not progress. The census above is the deliverable; the design below is the handoff.

## Design — exact sites to change

Mirror `safety_checker.spl`, do not invent a second model.

1. **Add the context flag.** New module `src/compiler_rust/compiler/src/hir/safety.rs`, holding
   `struct SafetyContext { in_unsafe: bool, errors: Vec<SafetyError>, extern_fns: Vec<String> }`.
   Do **not** hang this off `effects.rs` — that file's `CURRENT_EFFECTS` is thread-local
   ambient state, whereas unsafe scope must be lexical and save/restore across recursion.
2. **Walk HIR, not AST.** The seed's AST walkers all collapse `DoBlock | UnsafeBlock` into one
   arm; reusing any of them reintroduces the blindness. Walk `HirExprKind` so the marker from
   `hir/types/expressions.rs:114` is still present.
3. **Enter/exit** on `HirExprKind::UnsafeBlock(stmts)` with save-and-restore semantics exactly
   as `safety_checker.spl:471-476` (restore the *previous* value; do not unconditionally set
   false, or nested blocks break).
4. **Three rules**, matching the pure pass:
   - `HirExprKind::InlineAsm(..)` outside unsafe -> error. (Check whether the seed HIR has an
     `InlineAsmMatch` equivalent; the pure pass needed a separate arm at `:491` precisely
     because it fell through a wildcard.)
   - Raw-pointer deref / cast outside unsafe.
   - Direct `Call` whose callee resolves to an extern/SFFI fn outside unsafe — reuse the
     `NamedVar` + `extern_fns` approach from `safety_checker.spl:566`, **not** `unsafe.spl`'s
     broken `is_sffi_function`.
5. **Invoke it** from the seed's HIR pipeline, at the point analogous to
   `driver_hir_pipeline_passes.spl:149-153`.
6. **Severity must be profile-gated the same way**, projecting
   `driver_safety_severity.spl`'s Advisory/Warn/Deny ladder. Landing this as an unconditional
   hard error would break every currently-building program that relies on the migration window
   and would diverge the two compilers in the opposite direction.

## Specs to ship with the fix

Each must **fail without the fix** and must be paired with a positive control, otherwise a
blanket-rejection regression would pass:

- raw-pointer deref outside `unsafe:` -> rejected | same deref **inside** `unsafe:` -> accepted
- SFFI/extern call outside `unsafe:` -> rejected | same call **inside** `unsafe:` -> accepted
- inline `asm` outside `unsafe:` -> rejected | same `asm` **inside** `unsafe:` -> accepted
- nesting control: `unsafe:` containing a plain block containing the op -> still accepted
  (proves lexical *scope*, not merely a per-statement flag)

All six/eight must be run under a `critical` (Deny) profile, since Advisory is the default and
an Advisory run cannot distinguish "rejected" from "accepted".

Not written this session: an unrunnable spec whose own harness could not be exercised has a
real chance of being silently wrong, and `bin/simple check` is separately known to be blind to
parse errors (exit 0 on unparseable files), so it could not have been used to sanity-check
them either.

## Deferred verification

None of the following was executed. In particular the acceptance census above is derived from
source reading, not from observed compiler behaviour.

```bash
# 1. Compile-proof for any seed change (NOT run - withdrawn on host-capacity grounds).
#    Use a dedicated target dir on /mnt/data, never the shared one, and only when
#    `free -g` shows real headroom and load is low.
cd src/compiler_rust && CARGO_TARGET_DIR=/mnt/data/cargo-target-unsafe-scope \
  cargo check --release --bin simple

# 2. Behavioural census on the PURE compiler under a Deny profile. Expect all three
#    rejected; under the default profile expect all three accepted (Advisory).
#    Requires a `Results: N total, N passed, N failed` line - exit 0 alone is NOT a pass,
#    and exit 143 is an earlyoom kill, i.e. INCONCLUSIVE, never a pass or a fail.
bin/simple test test/01_unit/compiler/semantics/unsafe_scope_enforcement_spec.spl

# 3. Seed-side census, only meaningful after a seed rebuild+redeploy.
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"   # before AND after
```

## Related

- `doc/08_tracking/bug/safety_checker_pass_never_invoked_2026-07-27.md` — the pure-side
  precedent: the same pass existed and was not invoked at all.
- `src/compiler/80.driver/driver_safety_severity.spl` — the settled severity ladder any seed
  implementation must mirror.
