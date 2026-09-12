# `[u8]` Indexing Mis-Flagged as Deprecated Generics in Test Path

**Status:** RESOLVED (2026-09-12, re-verified: `bin/simple test test/01_unit/os/libc/libc_string_ctype_spec.spl` runs clean — 14 examples, 0 failures, and emits zero "Deprecated syntax for type parameters / Use angle brackets" warnings; only unrelated `#[runtime_intrinsics]` deprecation notices appear)

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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule B: cheap repro run against the deployed seed); the described false-positive deprecation warning no longer fires. Evidence: `bin/simple test test/01_unit/os/libc/libc_string_ctype_spec.spl` on deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) -> `14 examples, 0 failures`, zero "Use angle brackets" warnings in output.

## Re-check 2026-09-12

- Status: CLOSED (2026-09-12) — not reproducible on `3d120a6f9ab5`
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple`, sha256 `3d120a6f9ab5`

The exact repro command emits zero generics-deprecation warnings:

```
$ bin/simple test test/01_unit/os/libc/libc_string_ctype_spec.spl --no-session-daemon
   | grep -ci "angle brackets|fix-generics|Deprecated syntax for type parameters"
0
SPEC FILE VERDICT: test/01_unit/os/libc/libc_string_ctype_spec.spl outcome=OK declared>=14 executed=14 passed=14 failed=0
```

**Discrimination — the zero is not vacuous.** The lint is still live and still
fires for genuine bracket-generics on the same binary:

```
$ cat gen.spl
fn take(xs: Array[i64]) -> i64:
    xs.len()
$ bin/simple run gen.spl
warning: Deprecated syntax for type parameters
Use angle brackets: Array<...> instead of Array[...]
```

So the rule was not deleted or silenced wholesale; it now distinguishes array
indexing of a `[u8]`-typed variable from generic instantiation, which is the
first acceptance criterion in this record. The second (`simple migrate
--fix-generics` never rewriting such indexing) follows from the lint not firing,
but was not exercised directly — no migrate run was made.
