# String interpolation silently evaluates literal brace content

- **Filed:** 2026-07-28
- **Severity:** medium — silent wrong output, no diagnostic
- **Status:** open (one known instance fixed; no general guard)

## Symptom

A string literal containing `{...}` is interpolated. When the brace content
happens to parse as a valid Simple expression, it is silently evaluated and
replaced — even when the author meant literal text. There is no warning.

Probe (`bin/simple run`, verified 2026-07-28):

```
print("A: !llvm.dbg.cu = !{!0}")        # -> A: !llvm.dbg.cu = !true
print("B: !llvm.module.flags = !{!1, !2}")  # -> B: ... !{!1, !2}   (intact)
print("C: !{{!0}}")                      # -> C: !{!0}              (escaped)
print("D: !{!0, !1}")                    # -> D: !{!0, !1}          (intact)
```

`{!0}` is a valid expression — logical-not of `0` — so it becomes `true`.
`{!1, !2}` survives only because the comma makes it invalid as a single
expression. Whether literal text is preserved therefore depends on an
accident of the grammar, which is not a property an author can reason about.

## Impact found

`src/compiler/70.backend/backend/llvm_ir_builder.spl:512` emitted the DWARF
compile-unit anchor as:

```
!llvm.dbg.cu = !true
```

instead of `!llvm.dbg.cu = !{!0}` — invalid LLVM IR that `opt -passes=verify`
rejects. This sat undetected because the surrounding debug-info emitters had
zero callers (dead code) until the DS3 lane wired them up.

Fixed there by double-brace escaping (`!{{!0}}`), the same escape already used
in `emit_baremetal_attributes`. A repo-wide scan for the pattern
(`"[^"]*\{![0-9]+\}"` excluding `{{`) now returns **0** remaining instances.

## Why this needs more than the one-site fix

The failure is silent and content-dependent. Any code that emits a foreign
syntax with braces — LLVM IR metadata, VHDL, JSON, C, shell, regex quantifiers
like `a{2}` — is exposed, and only the subset whose brace content fails to
parse escapes corruption. The author gets no signal either way.

## Suggested fix

Warn when an interpolation expression inside a string literal is a constant
expression with no variable reference (e.g. `{!0}`, `{2}`, `{1+1}`). Such an
interpolation is almost always literal text the author did not intend to
evaluate; a real interpolation references something. Escaping (`{{`) silences
it. This is a lint-level check, not a language change, so it stays
backward-compatible.

## Related

- `doc/07_guide/language/dict_native_pitfalls.md` — same family: silent wrong
  values rather than a loud failure.
