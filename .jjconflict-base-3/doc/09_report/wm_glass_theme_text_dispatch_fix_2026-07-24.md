# WM Glass Theme Text Dispatch Fix Evidence

- status: source-and-object-pass, live-qemu-pending
- root cause: stale resolved aggregate owner overrode a proven text receiver
- compiler: `build/bootstrap-wm-text-dispatch/stage4-cranelift/aarch64-apple-darwin/simple`
- compiler sha256: `2d57ed3f76132dda43301c5bacc6bd2e5e5f6e114980de02e7eab30d17868763`
- compiler version: `simple-bootstrap 1.0.0-beta`
- compiler provenance: fresh pure-Simple self-host via the verified Stage 3 compiler
- fixture: `test/03_system/compiler/fixtures/text_predicate_owner_collision_probe.spl`
- object: `build/wm-text-dispatch-repro/native-objects-POmxAU/mod_0.o`
- object sha256: `2f1f346ecb40966e9a0f4e6dda22156db5f12fc7352e4100bda04845663658e6`

## Object evidence

The CSS-shaped function performs:

`split -> index -> rt_string_trim -> rt_string_starts_with`

The `rt_string_starts_with` relocation is at object offset `0x518`. The object
also defines `CustomPrefixOwner.starts_with` and `exercise_custom_owner`, so
the regression proves both sides of owner precedence. `nm` reports no
`ByteSpan` predicate reference.

The retained disassembly command is:

`xcrun llvm-objdump -dr --disassemble-symbols=_Users__ormastes__simple__test__03_system__compiler__fixtures__text_predicate_owner_collision_probe__exercise_css_text_owner build/wm-text-dispatch-repro/native-objects-POmxAU/mod_0.o`

Review subsequently narrowed owner recovery to unresolved/instance calls and
made resolved instance dispatch reuse its pre-lowered receiver. That
side-effect/static/trait/UFCS hardening is source-reviewed but is not claimed
as part of the retained object's evidence.

## Renderer follow-up

The shared-WM theme fallback now resolves after cascade, paints the declared
opaque background and foreground, clears unrealizable backdrop/gradient/layer
state, and attaches typed realized-material provenance to the pixel artifact.
Software, cached, fast Draw IR, and direct Draw IR artifact paths preserve the
same SHA-256 evidence contract. The hash is derived from emitted paint commands,
not raw CSS spelling, and is intentionally absent from Draw IR.

## Remaining limitation

The reduced executable reached object generation but failed during host link:
the current `core-c-bootstrap` runtime archive references
`MTLCreateSystemDefaultDevice` without adding the Metal framework. No further
build retry was made after the verify/fix cap. The session's QEMU launch cap
was already exhausted, so the final live themed framebuffer must be collected
in a fresh session.
