# `case Some(...)` on a slot that is only sometimes boxed — corrupts the payload or misses entirely

- **Filed:** 2026-08-31
- **Status:** FIXED at the MIR reader (`6d3856e6b4b`); the upstream writer inconsistency is OPEN
- **Component:** `src/compiler/50.mir/mir_lowering_stmts.spl`, `src/compiler/20.hir/hir_lowering/statements.spl`

## The defect class

A field declared as a plain nullable (`type_: HirType?`) is written by SOME call
sites as a `Some(x)` Option box and by others as a bare value. Reading such a slot
with `case Some(binding):` is wrong in two independent ways at once:

1. For bare-value writers the Option arm does not match the representation at all.
2. For boxed writers the Option-payload ARM BINDING deep-copies the aggregate and
   CORRUPTS it. An `RtCoreEnum`'s `word[1] = (discriminant << 32) | enum_id`, and
   `enum_id == 1 == RT_VALUE_TAG_HEAP`, so the copy's heap-box guard
   `(v & 7) == 1 && (v & ~7) != 0` PASSES and it dereferences `discriminant << 32`.

Observed symptoms: `_sffi_hir_type_discriminant` returning **-1**,
`E-MIR-TYPE-Unknown` errors, and SIGSEGV at addresses of the form
`0xf198715900000000` (the `Some` discriminant shifted into a pointer).

## The measured instance

`HirSymbol.type_` is declared `HirType?`. Of the **56** `symbols.define(` call
sites in `src/compiler`, only **13** pass a `Some(...)` box. The slot is a mixed
population, so `case Some` was never sound on it.

Of its three readers, only the MIR one assumed a box. The other two already
tolerate both forms and both work:

| reader | idiom | status |
|---|---|---|
| `20.hir/.../union_narrow_arms.spl:70` | `if val declared = ...` | fine |
| `20.hir/.../declaration_lowering.spl:469` | `.?` then `.unwrap()` | fine |
| `50.mir/mir_lowering_stmts.spl:~854` | `case Some(...)` | **defective** |

## Two wrong fixes, recorded because the shape of the error is the lesson

- **Attempt 1** replaced `case Some` with a nil guard `if let_type != nil`. That
  avoided the corruption by never unwrapping, and handed the raw box to
  `lower_type`: SIGSEGV. Committed as `c79afab1e43`, reverted in `345817963a6`.
- The reasoning error behind it: `letkindzero=false` was read as proof that
  `let_type` was a bare `HirType`. **That inference does not hold.** For an Option
  box, `.kind` reads the `RtCoreEnum` header word, which is also non-zero. BOTH
  representations give `letkindzero=false`; the probe never distinguished them.

The requirement was always a **safe unwrap** — neither `case Some` (unwraps but
corrupts) nor a nil guard (does not unwrap) is one.

## Fix

`.?` + `.unwrap()`, the idiom already proven on this exact slot at
`declaration_lowering.spl:469`. Chosen over `if val` deliberately: a draft REOPEN
note in this lane records `if val` binding the Option HANDLE rather than its
payload on the native writer/extraction seam, and there was no reason to take
that risk when a proven-on-this-slot idiom was available.

Measured, aarch64-apple-darwin, cranelift:

```
E-MIR-TYPE occurrences ......... 0     (was 20)
SIGSEGV ........................ none  (was rc=139 in lower_type)
bootstrap_stage2_struct_receiver PASS
```

## Still OPEN — the upstream half

The writers in `hir_lowering/statements.spl` box into a slot declared `HirType?`,
and an in-place comment says that is intentional BECAUSE the MIR reader used
`case Some`. **That comment is now stale.** De-boxing those 13 writers to match
the declaration and the repo's "a nullable is not an Option box" rule
(`statements.spl:409/580`, `module_declarations_bootstrap.spl:435`, bug doc
2026-07-23) is the correct follow-up. It touches readers outside that file and
should land on its own evidence rather than riding along with a gate fix.

A classified sweep of the remaining `case Some(` sites across `src/compiler` —
which of them sit on flat-nullable or mixed-population slots — is the bounded way
to find the rest of this population, rather than another point fix.
