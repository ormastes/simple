# `is_cipher_intrinsic` always returns false — `.?` on an `i64?` compared to `true`

- Date: 2026-08-23
- Status: OPEN — one-line fix identified; NOT applied here because
  `src/compiler/50.mir/**` is owned by the live MIR construct-matrix lane.
- Found by: compiler-tree spec sweep (`test/01_unit/compiler/**`).
- Engine: reproduces in the **interpreter** (`bin/simple run` / `bin/simple test`).
  Not yet checked on JIT or native — those resolve independently.

## Symptom

`test/01_unit/compiler/mir_opt/cipher/cipher_intrinsics_spec.spl` fails 3 of 3
examples in the "`is_cipher_intrinsic` — true for every registered name" group
(AES family, SHA-256 family, CRC32 + CLMUL family), each with
`expected false to equal true`. The three *negative* examples pass, which is why
this looked healthy: the function is not broken in one direction, it is stuck
returning `false` for every input.

## Root cause

`src/compiler/50.mir/intrinsics.spl:153-154`

```
fn is_cipher_intrinsic(name: text) -> bool:
    cipher_intrinsic_arg_count(name).? == true
```

`cipher_intrinsic_arg_count` is declared `-> i64?`
(`src/compiler/50.mir/intrinsics.spl:136`) and yields `2` for every registered
cipher intrinsic, `nil` otherwise.

`.?` is **unwrap-or-propagate**, not a presence test. Minimal repro on the
interpreter:

```
fn maybe(n: i64) -> i64?:
    if n > 0:
        return 2
    nil
```

| expression | result |
|---|---|
| `maybe(1).?`         | `2`     |
| `maybe(1).? == true` | `false` |
| `maybe(1) != nil`    | `true`  |
| `maybe(0).?`         | `nil`   |

So `2 == true` is `false`, and `is_cipher_intrinsic` answers `false` for every
registered name. The spec is RIGHT; the source is WRONG.

## Consequence

Any caller gating on `is_cipher_intrinsic` silently sees "not a cipher
intrinsic" for AES / SHA-256 / SHA-512 / CRC32 / CLMUL, i.e. the cipher
intrinsic path is effectively disabled rather than erroring.

## Fix

```
fn is_cipher_intrinsic(name: text) -> bool:
    cipher_intrinsic_arg_count(name) != nil
```

Semantics-preserving with respect to the declared intent; no ABI, layering, or
value-semantics change.

## Defect-class sweep (whole class enumerated, not one instance)

`/usr/bin/grep -rFn --include=*.spl ".? == true" src/` returns **12** sites.
The idiom is **correct** where the optional's payload is already `bool` — the
`.?` unwraps to a bool and the comparison is meaningful:

- `src/lib/gc_async_mut/web/browser_session_loading.spl:342,368`
- `src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:310`
- `src/lib/common/io/types.spl:32,204`
- `src/compiler/90.tools/lint/_LintMain/config_and_model.spl:837`
- `src/app/interpreter/helpers/debug_spec.spl:611,613,626,1078,1088`

`src/compiler/50.mir/intrinsics.spl:154` is the **only** site in the class where
the payload is not `bool` (`i64?`), and therefore the only site where the
comparison is unconditionally false. The 31 `.? == false` sites were checked the
same way and are all `bool?` payloads.

## Follow-up worth considering (separate, larger — filed, not done)

A lint rule for `X.? == <bool literal>` where `X`'s payload type is not `bool`
would make this class impossible to reintroduce. That is a new lint rule, not a
minimal fix, so it is recorded here rather than bundled.

## Ratchet decision (routed 2026-08-23)

Asked whether `.? == <bool literal>` deserves a lint or a pre-push ratchet.
Recommendation: **a lint rule, not a ratchet — and not yet a fatal one.**

Why a lint and not a ratchet: a ratchet freezes a population and fails on
growth. That is the right tool when the population is large and cannot be
drained (as with `unbacked_extern_baseline.txt`'s 1,466 symbols). Here the
whole-tree census is **12 sites**, of which **11 are correct** — the payload
really is `bool` and `.?` really does unwrap to it. A ratchet over a
12-row population that is 92% legitimate would be pinning noise, and the
one real defect is already fixed by this record. There is nothing to freeze.

Why a lint: the failure is silent and type-directed, which is exactly what a
compiler-side check is good at and what review is bad at. `X.? == true`
where `X`'s payload type is not `bool` is **unconditionally false** — never
what anyone meant — so the rule has no false-positive class as long as it
consults the payload TYPE and does not fire on the 11 `bool?` sites. A
text-only grep rule would flag all 12 and be turned off within a day.

Scope note, so the rule is not written too narrowly: the defect is not
specific to `== true`. `X.? == <any non-bool-typed literal>` has the same
shape, and `.? == false` (31 sites, all `bool?` payloads today) would fail
the same way the moment a non-`bool` optional appears. Key the rule on
"payload type of `.?` is not comparable to the literal's type", not on the
`true` token.

Not implemented here: a new lint rule is a feature, not the minimal fix this
record is about, and `90.tools/lint` is outside this lane. Recorded so it is
tracked rather than lost.
