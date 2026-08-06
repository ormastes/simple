# `match` on an imported enum silently matches NO arm when the entry point lives in the same package

- **Filed:** 2026-08-06
- **Status:** Open
- **Severity:** High — silent wrong behavior, no error, no crash, no warning
- **Component:** compiler — enum discriminant / module identity
- **Found by:** WS-B host-adapter work (`src/app/ui_showcase/hosts/main_2d.spl`)

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

### Localization

The force-unwrap is parsed as `ExprKind.ForceUnwrap` and lowered to
`HirExprKind.Unwrap` (`src/compiler/20.hir/hir_lowering/expressions.spl:809`),
carried through resolve (`src/compiler/35.semantics/resolve.spl:451`) — and then
**there is no `Unwrap` arm anywhere in MIR lowering.** Its three Option siblings
all have explicit, heavily-commented arms that branch on `rt_is_some` and
re-attach payload provenance (`NullCoalesce` and `ExistsCheck` in
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:2938+`, `ExistsCheck`
again in `mir_lowering_stmts.spl:1518`). `Unwrap` has none, so it reaches the
default arm and passes the operand through unchanged — the Option wrapper is
never stripped, and the match then reads the wrapper's discriminant instead of
the enum's. That is a precise fit for "no arm fires, nothing throws".

The dual-keyed enum registry is **not** implicated: the same enum, same module,
same declaration matches correctly on line 1 and fails on line 2 within one
compilation unit.

### Why no fix is landed here

The measured failure is in the **Rust seed's JIT**, and `src/compiler_rust/**`
is out of scope by policy. The pure-Simple mirror of the bug (the missing MIR
`Unwrap` arm) is in scope, but no pure-Simple binary is currently built in this
tree (`bin/simple` is the seed), so a new lowering arm could not be compiled or
proved. Adding one blind — to a path where the sibling arms needed struct-name
provenance fixes to be correct — is exactly the speculative change this bug
does not need. **What to change:** give `HirExprKind.Unwrap` its own MIR arm
modelled on `NullCoalesce`'s: branch on `rt_is_some`, extract the payload via
`enum_payload_value`, re-attach the Option's declared inner type provenance via
`option_inner_hir_type_for_local`, and panic on the None branch. Then re-run the
fixture; line 2 and 3 must print `A7` / `Green`. Line 4 (interpreter matching an
Option directly) is a **separate, opposite** defect and should be filed apart.

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
- Still open: land the MIR `Unwrap` arm and re-verify (needs a pure-Simple
  build); file the inverted interpreter defect (line 4) separately.

## Related

- Enum registry dual-keyed; discriminant is a cross-crate ABI.
- Single-field enum variant payload is not a 1-tuple.
- Enum payload sub-patterns: the axis is nesting.
