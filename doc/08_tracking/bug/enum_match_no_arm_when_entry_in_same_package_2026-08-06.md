# `match` on an imported enum silently matches NO arm when the entry point lives in the same package

- **Filed:** 2026-08-06
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  identified in finding (b) is closed; the Rust-seed-JIT measurement in
  finding (a) remains out of scope (`src/compiler_rust/**`).
- **Severity:** High — silent wrong behavior, no error, no crash, no warning
- **Component:** compiler — enum discriminant / module identity
- **Found by:** WS-B host-adapter work (`src/app/ui_showcase/hosts/main_2d.spl`)

## Fix landed (2026-08-06)

Landed exactly the fix this doc's own investigation (finding (b), below)
already prescribed: `HirExprKind.Unwrap` (the `!` force-unwrap operator) now
has a dedicated arm in MIR lowering
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`, `case
Unwrap(base):`, inserted directly before the `Try` arm). Before this, `!` had
no MIR arm at all and fell to the file's loud `case _` default (records a
compile error, returns a fresh unit temp) — a *different* symptom than the
silent match-fallthrough measured via the Rust seed in finding (a), which
remains a separate, out-of-scope artifact of `src/compiler_rust/**`.

The new arm mirrors `.unwrap()`'s own proven MIR lowering
(`method_calls_literals.spl`, the `"unwrap"` method-call arm) essentially
line-for-line: branch on `rt_is_some` (never truthiness, so a present numeric
zero / payloadless variant round-trips correctly), extract the Some-branch
payload via `option_payload_or_self` + `enum_payload_value` /
`decode_runtime_value` / `option_text_value` / `option_bool_value` depending
on the physical Option lane and payload type, panic via `rt_panic` on the
None branch, and carry `struct_value_syms` provenance across so a
struct-typed payload stays field-addressable after `!`.

**Regression spec:** `test/01_unit/compiler/mir/enum_match_after_force_unwrap_mir_spec.spl`
(6 examples). Since sspec's default runner is the tree-walk interpreter and
cannot reach the JIT/native path `!` lowers through (see
`doc/07_guide/infra/testing.md`), the spec pins the CONTENT of the new MIR
arm structurally (`rt_file_read_text` + `to_contain`/`index_of`), the same
pattern already established for other MIR-lowering-only fixes (see
`test/01_unit/compiler/mir/option_text_unwrap_pointer_spec.spl`). Sabotage-checked
manually: reverting the MIR edit reproduces 5 of 6 failures (the 6th assertion
was hardened afterward to no longer pass vacuously when the string is
absent); reapplying restores all 6 to green.

Not re-verified end-to-end against a fresh pure-Simple self-hosted binary
(`bin/simple native-build` + execute the committed repro fixture): this
session's environment had 7-10 concurrent native-build/bootstrap processes
from other agent sessions throughout, and two attempts to build a fresh
stage2 binary for direct verification stalled/were resource-starved. The fix
is a close structural mirror of already-shipping, already-tested code
(`.unwrap()`'s identical lowering shape), so risk is low, but a follow-up
native-build + run of
`test/fixtures/repro/compiler/enum/enum_match_after_option_unwrap_repro.spl`
lines 2-3 (expect `A7` / `Green`, not `FALLTHROUGH`) once a quiet window is
available is still worthwhile.

## Symptom

`showcase_apply(st, ev, w, h)` matches on `HostInputEvent`
(`src/lib/common/ui/host_input_event.spl`). When driven from an entry point
located **inside the same package as the matching code**, every `match ev` arm
fails to fire. No arm matches, no error is raised, and execution continues — the
reducer simply returns an unchanged state.

Observable result: `frames=2 clicks=0 typed=""` where `clicks=1 typed="ab"` is
correct. Frames still paint, so the failure looks like an input-plumbing bug
rather than a compiler bug.

## Isolation (this is the load-bearing part)

The same source behaves differently based *only* on where the entry file lives:

| Entry location | Result |
|---|---|
| scratch path outside the package | `clicks=1` ✅ |
| anywhere under `src/app/ui_showcase/**` | `clicks=0` ❌ |

Narrowed further, from an in-package entry:

| Path exercised | Result |
|---|---|
| events built **in the entry**, `showcase_apply` called directly | `clicks=1` ✅ |
| events from `host_2d.screen_2d_parse_script`, applied directly | `clicks=1` ✅ |
| same host passed to `showcase_core.showcase_run` | `clicks=0` ❌ |

In the failing case `poll_input` **does** return real values across the trait
boundary — the cursor advances and all 4 events are drained — and frames are
painted. So the values cross the trait fine; it is specifically the `match`
that recognizes none of them.

## Why this matters beyond one showcase

The values are not corrupt and nothing throws. A reducer that silently matches
no arm returns unchanged state, which reads downstream as "the input never
happened." Any spec asserting on post-input state would fail with a confusing
diff; any spec asserting only that frames rendered would **pass vacuously**.

## UPDATE 2026-08-06 — root cause found; the "same package" axis is a CONFOUND

The title is wrong. Package location, module split and the trait boundary are
all irrelevant. The trigger is the `?`-to-`!` round trip: **an enum value that
has been force-unwrapped out of an Option (`ev!`) matches no declared arm.**

`showcase_run` is the only failing path precisely because it is the only one
that goes through `host.poll_input() -> HostInputEvent?` and then `showcase_apply(st, ev!, ...)`.
Every "working" path in the table above builds the enum value directly and
never round-trips it through an Option.

### Committed repro

`test/fixtures/repro/compiler/enum/enum_match_after_option_unwrap_repro.spl`
— single file, no package, no module split, no trait, ~40 lines.

Measured with the Rust bootstrap seed `bin/release/x86_64-unknown-linux-gnu/simple`
(md5 `ed53cc5f255e269ca27c4cd83b17aef9`), which is what `bin/simple` currently is:

| line | JIT (default) | `SIMPLE_EXECUTION_MODE=interpret` |
|---|---|---|
| 1 direct construct + match | `A7` | `A7` |
| 2 payload variant after `!` | **`FALLTHROUGH`** | `A7` |
| 3 payloadless variant after `!` | **`FALLTHROUGH`** | `Green` |
| 4 match the `E?` value directly (no `!`) | `A7` | **`FALLTHROUGH`** |

The two engines are exactly **inverted**, so neither is a control for the other.

### The three open questions, answered

- **Does `case _` fire?** **YES.** The match statement *executes*; it simply
  recognizes no declared variant. This rules out "match skipped entirely" and
  rules out a control-flow miscompile. Without a `case _`, the reducer falls
  out of the match and returns unchanged state with no error or warning —
  exactly the silent failure originally observed.
- **Payload-carrying variants only?** **NO.** A three-variant payloadless enum
  (`P.Red/Green/Blue`) fails identically after `!` (line 3). Payloads are
  irrelevant.
- **Is the trait boundary required?** **NO.** Neither a trait, a second module,
  nor a package is required — a single file with two plain `fn`s reproduces it.

### Localization — two SEPARATE claims, do not conflate them

**(a) The measured defect — Rust bootstrap seed, JIT.** Every number in the
table above came from the seed binary. Behaviourally, `!` does not strip the
Option wrapper under the JIT: the match then reads the wrapper's tag rather
than the enum's, so no declared variant is recognized and `case _` catches it.
Line 1 vs line 2 differ only by the Option round trip, within a single
declaration in a single compilation unit — so the **dual-keyed enum registry is
NOT implicated**, and neither is module or package identity. This lives in
`src/compiler_rust/**`, which is out of scope by policy; the mechanism above is
*consistent with* the observations, not proven at the IR level.

**(b) An independent structural finding — pure-Simple compiler, unverified.**
Force-unwrap is parsed as `ExprKind.ForceUnwrap`
(`src/compiler/10.frontend/parser_types_expr.spl:344`), lowered to
`HirExprKind.Unwrap` (`20.hir/hir_lowering/expressions.spl:810`) and carried
through resolve (`35.semantics/resolve.spl:451`) and the safety checker
(`35.semantics/safety_checker.spl:630`) — and then **there is no `Unwrap` arm
anywhere in MIR lowering.** Its three Option siblings all have explicit arms
that branch on `rt_is_some` and re-attach payload provenance (`NullCoalesce`,
`ExistsCheck` at `50.mir/_MirLoweringExpr/expr_dispatch.spl:2938+`, `ExistsCheck`
again at `mir_lowering_stmts.spl:1518`). The MIR default arm
(`expr_dispatch.spl:3380`) is a **loud** unsupported-expression-kind failure,
not a pass-through — so this predicts a *compile error*, not the silent
mismatch measured in (a). `parser_expr.spl:1058` marks the panic codegen as
deferred milestone "M12", so the gap looks deliberate-but-unfinished. This
could not be verified: no pure-Simple binary exists in this tree
(`bin/simple` is the seed).

### Why no fix is landed here

The measured failure is in the **Rust seed's JIT**, and `src/compiler_rust/**`
is out of scope by policy. Finding (b) is in scope but is a *different* symptom
(loud error, not silent mismatch) and could not be compiled or proved — no
pure-Simple binary exists here. Adding a lowering arm blind, on a path where
every sibling arm needed struct-name provenance work to be correct, is exactly
the speculative type-identity change to avoid.

**What to change, when a pure-Simple build is available:** give
`HirExprKind.Unwrap` its own MIR arm modelled on `NullCoalesce`'s — branch on
`rt_is_some`, extract the payload via `enum_payload_value`, re-attach the
Option's declared inner type provenance via `option_inner_hir_type_for_local`,
and panic on the None branch. Then run the fixture under that binary; lines 2
and 3 must print `A7` / `Green`.

**Workaround available today:** never `match` a value that came out of `!`.
Match the `T?` directly under the interpreter, or restructure so the enum is
never round-tripped through an Option. Neither is engine-portable — see line 4.

**Separate defect, not yet filed:** line 4 is the exact inverse — the
*interpreter* fails to match arms when the scrutinee is an `E?` matched
directly, while the JIT handles it. Same silent-wrong-answer class. Needs its
own bug entry.

## Suspected cause (ORIGINAL — refuted, see update above)

Consistent with the known dual-keyed enum registry, where the discriminant
behaves as a cross-crate ABI: the enum appears to acquire a different identity
depending on whether the constructing module and the matching module resolve it
through the same package path. See the related note on the enum registry being
dual-keyed and first-registration-wins.

## Repro

Minimal repro is ~10 lines: an enum in a lib module, a constructor and a
`match` in a second module of package P, and an entry point placed (a) outside P
and (b) inside P. Compare the matched arm.

Temp probes used during isolation were deleted rather than left in the tree; the
repro above is quick to reconstruct from this description.

## Not yet done

- ~~Minimal repro not committed as a fixture.~~ DONE — see update above.
- ~~Whether this affects enums generally or only payload-carrying variants.~~
  DONE — all enums.
- ~~Whether `case _` fallthrough fires.~~ DONE — it fires.
- ~~Still open: land the MIR `Unwrap` arm~~ DONE — see "Fix landed" above.
- ~~file the inverted interpreter defect (line 4) separately~~ DONE —
  `doc/08_tracking/bug/interpreter_match_on_option_of_enum_fires_no_arm_2026-08-06.md`,
  now also fixed (different root cause, see that doc).
- Still open: re-verify the MIR fix end-to-end against a freshly built
  pure-Simple self-hosted binary once the shared build environment is quiet
  (native-build + run the committed repro fixture, lines 2-3).

## Related

- Enum registry dual-keyed; discriminant is a cross-crate ABI.
- Single-field enum variant payload is not a 1-tuple.
- Enum payload sub-patterns: the axis is nesting.
