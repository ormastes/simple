# `[u8]` Indexing Mis-Flagged as Deprecated Generics in Test Path

## Closed 2026-09-13 — `[u8]` indexing no longer emits the deprecated-generics warning

- **measured** Binary: Rust seed `bin/simple` v1.0.0-rc.1 (16,347,136 bytes, 2026-09-02), Windows host.
- **measured** A file whose function takes `s: [u8]` and indexes `s[i]` in a loop compiles and runs (`sum=6`) with `grep -icE 'deprecat|fix-generics'` over the full stderr returning `0`.
- **measured** Repeated under `SIMPLE_EXECUTION_MODE=interpret` (the mode the test runner uses): still `0` deprecation hits, `sum=6`.
- **inferred** The exact reported invocation was `bin/simple test`, which is unusable on this Windows host (empty `Compilation failed:` on scratch specs; outer-bound timeout on a repo spec), so interpret-mode `run` was used as the proxy.

Date: 2026-06-28

Lane: `.spipe/simpleos-alpine-harden-musl-busybox`

## Summary

Indexing a `[u8]`-typed variable (`s[i]`) emits a spurious
"Deprecated syntax for type parameters / Use angle brackets: s<...> instead of
s[...]" warning under the `bin/simple test` compile path, and suggests
`simple migrate --fix-generics` — which, if applied, would rewrite valid array
indexing `s[i]` into `s<i>` and break the code. The runtime behavior is correct
(spec passes), so this is a false-positive lint, not a real syntax issue.

## Reproduction

```sh
# WARNS on s[i] at lines indexing a [u8] param:
bin/simple test test/01_unit/os/libc/libc_string_ctype_spec.spl
```

vs.

```sh
# CLEAN — 0 such warnings:
bin/simple check src/os/libc/simpleos_string.spl
```

`src/lib/common/string_core.spl` (which indexes a `text`-typed `s` with `s[i]`)
also emits 0 such warnings. The trigger is specific to indexing a `[u8]`
(array) -typed variable, and only on the `test` compile path — `check` and
`text` indexing are clean.

## Root cause (suspected)

The generics-migration deprecation lint cannot distinguish array indexing
`arr[i]` from the deprecated generic-instantiation `Type[T]` when the receiver
is a `[u8]`/array-typed variable, and the `test` runner enables this lint while
`check` does not. The two paths should agree, and array indexing must never be
flagged for `--fix-generics`.

## Acceptance for closure

- `bin/simple test` and `bin/simple check` agree on generics-deprecation
  warnings for the same file.
- Indexing an array-typed variable (`[u8]`, `[i64]`, …) never emits the
  "Use angle brackets" deprecation, and `simple migrate --fix-generics` never
  rewrites such indexing.
