Result payload text-provenance regression fixtures (not executed yet).

- `result_text_trim.spl`: `Result<text, text>?` must preserve text provenance
  for `.trim()`. Expected output is `[λ]` followed by `[]`; this covers a
  multibyte payload, ASCII whitespace, and an empty trimmed result. Its locals
  are intentionally unannotated so it reproduces the missing provenance.
- `result_text_trim_annotated_control.spl`: the explicit `text` annotation is
  the source workaround control; expected output is `[λ]`.
- `custom_trim_precedence.spl`: a user-defined `Label.trim()` must remain the
  selected method when text builtins share the method name. Expected output is
  `custom`.
- `nontext_trim_rejected.spl`: a numeric receiver must not be routed through
  the text builtin; expected outcome is a normal unresolved-method diagnostic.
- `text_trim_wrong_arity_rejected.spl`: the text builtin is zero-argument and
  must reject an extra argument rather than dispatching it as `.trim()`.
