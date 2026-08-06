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

## Suspected cause

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

- Minimal repro not committed as a fixture.
- Not yet determined whether this affects enums generally or only enums whose
  variants carry payloads.
- Not yet checked whether `case _` fallthrough fires (which would distinguish
  "no arm matches" from "match skipped entirely").

## Related

- Enum registry dual-keyed; discriminant is a cross-crate ABI.
- Single-field enum variant payload is not a 1-tuple.
- Enum payload sub-patterns: the axis is nesting.
