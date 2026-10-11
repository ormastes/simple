# Imported enum subject-type probes

Source base: `a487584ced2f4000fdc9c7ce7be1b441fa6150a5`. Fixtures are frozen as a test-only commit; no compiler source is changed. Positive mixed-arm probes use the source-shaped bare pattern `Deref | Field(_)`. The direct typed parameter is the baseline; one qualified companion separates bare-name classification from subject-type transport.

| Entry | Distinction | Expected stdout if accepted |
|---|---|---|
| `direct_mixed` | Direct typed `E` parameter, bare mixed arm | `1\n1\n0\n` |
| `direct_qualified_mixed` | Same parameter with qualified constructors | `1\n1\n0\n` |
| `property_mixed` | Imported `Holder.kind: E` | `1\n1\n0\n` |
| `nested_field` | `Holder.inner.kind` | `1\n1\n` |
| `call_field` | `make_holder().kind` | `1\n` |
| `index_field` | `holders[index].kind` | `1\n` |
| `typed_foreach` | Iteration over `[E]` parameter | `2\n` |
| `untyped_foreach` | Iteration over inferred enum array literal | `2\n` |
| `alias_untyped` | `val alias = value` then bare mixed arm | `1\n1\n` |
| `alias_typed` | `val alias: E = value` control | `1\n1\n` |
| `unrelated_owner_negative` | `E.Shared` against `F.Shared` | If accepted, stdout must be `0\n`; compile-time rejection is also recorded as observed, not assumed |
| `binding_name_collision` | Bare `Deref` against an `i64` subject, checks binding-name collision handling | Intended observation is `17\n`; actual acceptance/output or diagnostic is recorded without presupposing behavior |

If a positive mixed-arm case fails before execution, record the actual diagnostic; the target first-loss signature is `or-pattern alternatives must bind the same variables`. Do not classify failures as compiler regressions unless the direct control establishes the same bare pattern is accepted. The existing six-case validation already covers genuine `x`/`y` or-pattern binding mismatch rejection. No probe has been compiled or run.
