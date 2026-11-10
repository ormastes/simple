# Implicit `self` field READ inside a plain `fn` method is unresolved (JIT + HIR)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Date: 2026-09-03
- Status: OPEN — re-confirmed 2026-11-11 (lane ne11): pure-Simple HIR lane FIXED, Rust seed lane still red; see addendum
- Platform observed: Windows x86_64 (`bin/simple.exe`, tracked seed)
- Related but distinct: `implicit_self_field_assignment_still_silent_in_plain_fn_methods_2026-08-31.md`
  (that record covers ASSIGNMENT; this one is a READ, and it is not silent — it
  is a hard "not found").

## Minimal repro (12 lines)

```simple
class Box:
    kind: text

    fn code() -> i64:
        if kind == "a":
            4
        else:
            1

fn main() -> i64:
    val b = Box(kind: "a")
    print "code={b.code()}"
    0
```

```sh
bin/simple.exe run repro_kind.spl
```
Exit status: 2.

## Observed

```
[CODEGEN BODY] Function 'Box.code' body compilation failed:
  GlobalLoad: unresolved identifier 'kind' (not a global, function,
  const-data name, or import)
[INFO] JIT compilation failed, falling back to interpreter: ...
error: semantic: variable `kind` not found
```

The interpreter fallback fails the same way, so there is no working path.
The bootstrap/native front end reports the identical `unresolved name: kind`
during HIR lowering of `src/app/devhub/errors.spl`.

## Expected

`kind` inside a method body resolves to the receiver's field, printing
`code=4` and exiting 0.

## Real-world impact

`src/app/devhub/errors.spl:44 ItfError.exit_code()` is written exactly this way
(deliberately, with a comment explaining why the `match` form was avoided).
Five examples in `test/01_unit/app/devhub/itf_config_spec.spl` fail with
`semantic: variable ``kind`` not found`.

Scope check (done, 2026-09-03): the live CLI paths that emit exit code 4 do
NOT go through this method — `src/app/devhub/cmd_wiki.spl` uses a bare
`return 4` at 6 sites, which is why `devhub wiki list` still exits 4 on this
box. Impact is therefore limited to callers that actually invoke
`ItfError.exit_code()`, plus any future code written in this idiom — not to
every devhub exit path.

## Workaround

Write `self.kind` explicitly. Not applied here: the scope of the defect is
compiler-side and a mass rewrite would hide it.


---

## 2026-11-11 addendum — lane ne11 (P3 traverse, batch ne11)

**Verdict: lane-split re-confirmed on the fresh seed — pure-Simple HIR lane
FIXED; Rust seed frontend lane still LIVE. Keep OPEN.**

- **Seed lane (LIVE):** the doc's verbatim 12-line repro run on tracked
  `bin/simple.exe` build-commit `46fe8f6b6def` (seed-smoke) fails identically
  to 2026-09-03: Cranelift `GlobalLoad: unresolved identifier 'kind'` with JIT
  demotion, then the interpreter fallback dies with
  `semantic: variable \`kind\` not found` (exit 1). No working path on the
  seed; the `self.kind` workaround in `src/app/devhub/errors.spl` (`exit_code`,
  with its do-not-rewrite comment) is still required for code that must run on
  the seed.
- **Pure-Simple HIR lane (FIXED):** `test/01_unit/compiler/hir/implicit_self_field_read_plain_fn_spec.spl`
  (lowered through `compiler.hir.hir_lowering` on the seed interpreter)
  **1/1 PASS** this lane — the self-hosted compiler resolves the bare field
  read. This matches the 2026-11-09 lane-split finding (`ed11081c6e23`).
- **Remaining fix location:** `src/compiler_rust` seed frontend (name
  resolution for receiver field reads in plain `fn` methods, both JIT and
  interpreter paths). Outside this no-cargo lane.
- **Grant:** a lane with Rust toolchain + seed-rebuild permission: fix the
  seed frontend resolution, rebuild + refresh `bin/simple.exe`
  (`scripts/bootstrap/` seed build flow), then re-run this doc's repro
  (expect `code=4`, exit 0) and `test/01_unit/app/devhub/itf_config_spec.spl`.
