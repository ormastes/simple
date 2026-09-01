# `alias X = Y` is spec-documented but silently degrades to a bare identifier (2026-09-01)

## Summary

`doc/07_guide/quick_reference/syntax_quick_reference.md:171-182` documents
`alias` as a supported declaration form:

> **Note:** `alias` creates an alternative **name** for an existing class. It is
> not inheritance.
>
>     alias Optional = Option
>     alias Vec = Vector
>     alias IntSet = Set<i64>

No parser implements it as a declaration. The lexer produces a dedicated token
(`src/compiler_rust/parser/src/lexer/identifiers.rs:257`, `"alias" =>
TokenKind::Alias`), but every consumer turns that token straight back into an
ordinary identifier:

    src/compiler_rust/parser/src/expressions/primary/identifiers.rs:58
        TokenKind::Alias => self.parse_keyword_identifier("alias")
    src/compiler_rust/parser/src/parser_patterns.rs:605
        Ok(Pattern::Identifier("alias".to_string()))

so `alias ComputeError = GcComputeError` parses as an expression naming a
variable called `alias`, and the declaration is silently discarded. The
pure-Simple parser has no `alias` handling at all — `grep -rn "alias" 
src/compiler/10.parser/ --include=*.spl` returns nothing for the declaration
form, and there is no `type_alias`/`TypeAlias` production there either.

## Why it matters — the failure is silent, not a syntax error

Nothing rejects the input. The declaration simply does not exist afterwards, so
the failure surfaces far away as `unresolved name: alias` plus one
`unresolved name`/`unresolved type` per aliased symbol. Measured in the
SimpleOS WM x86_64 host-daemon `native-build`
(`build/simpleos_wm_vulkan/daemon-build2.log`), 12 of the 119 HIR errors were
this one file:

    12 HIR lowering error in src/std/gc_async_mut/gpu/engine2d/backend_session.spl
     6 unresolved name: alias
     2 unresolved name: ComputeError
     2 unresolved name: BackendSessionPolicy
     2 unresolved name: BackendSessionHandle

A `warning`/`error` at the declaration would have cost one line to diagnose
instead of a whole build cycle.

## Population

Only two files in the tree use the documented form, against 48 using `type`:

    src/lib/gc_async_mut/gpu/engine2d/backend_session.spl:200-202   (FIXED, see below)
    src/os/compositor/arm64_virtio_input_backend.spl                (STILL PRESENT)

The supported spelling is `type X = Y` (e.g.
`src/lib/nogc_sync_mut/io_runtime.spl:135  type ShellResult = ProcessResult`,
`src/lib/nogc_sync_mut/game2d/math/__init__.spl:9-10`).

## What was done, and what was deliberately NOT done

`backend_session.spl:200-202` was converted to `type`, because that file is in
the x86_64 WM daemon closure and the row is blocked behind it. This bug record
exists so that the conversion is a RECORDED workaround and not a silent
normalization — CLAUDE.md forbids the latter:

> When a short, safe grammar or compact expression form fails, compiles too
> slowly, or forces a workaround, fix it or record a concrete bug/feature
> request instead of silently normalizing the workaround.

`arm64_virtio_input_backend.spl` was left alone: it is on the aarch64 row, which
is blocked for unrelated reasons, and converting it would hide the second
witness.

## Fix options (either is acceptable; both close this record)

1. **Implement it.** Make `alias` a synonym for `type` in both parsers. This is
   what the spec promises and is the smaller surprise for readers.
2. **Withdraw it.** Delete the `alias` section from
   `syntax_quick_reference.md:171-182`, convert the remaining call site to
   `type`, and make the parser emit a real diagnostic
   (`alias is not a declaration form; use \`type X = Y\``) rather than degrading
   to an identifier.

What is NOT acceptable is the present state: documented in the language
reference, accepted by the lexer, and silently dropped by the parser.

## Related

- `doc/08_tracking/bug/simpleos_wm_vulkan_cross_arch_rows_blocked_2026-08-31.md`
  — the x86_64 WM row this blocked.
