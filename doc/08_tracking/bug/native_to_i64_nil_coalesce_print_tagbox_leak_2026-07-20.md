# Native `text.to_i64() ?? default` leaks tag-box representation, wrong value in string interpolation

**Date:** 2026-07-20
**Status:** ROOT-CAUSED + SOURCE-FIXED 2026-07-21 (Rust seed,
`src/compiler_rust`); dynamic end-to-end (compile-and-run) verification of
the *patched* binary is BLOCKED by an unrelated, pre-existing toolchain gap
(see "Fix + verification status" below) — treat as source-fix-landed,
runtime-unverified until a working fresh-build toolchain is available to
close the loop. Originally: found incidentally while instrumenting an
unrelated bug (`bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`),
not independently bisected further; filed per repo rule (concrete bug over
silent workaround) rather than tracked only as a doc aside.
**Severity:** P2 — silent wrong value, no diagnostic, on a common stdlib
call (`text.to_i64()` combined with `??` and string interpolation).
**Component:** compiler codegen — Option (`i64?`) coalesce (`??`) +
string-interpolation print, **hosted native-build**
(`x86_64-unknown-linux-gnu`, cranelift backend, `--mode one-binary`).
Same "Some payload not correctly unwrapped/reboxed" family as
[hosted_native_option_try_unwrap_payload_leak_2026-07-19](hosted_native_option_try_unwrap_payload_leak_2026-07-19.md),
different shape (`??` + print-interpolation, not `.?`/`if val`).

## Symptom

```simple
fn main() -> i64:
    val s = "12345"
    val n = s.to_i64() ?? -999
    print "n={n}"
    val s2 = "12345".trim()
    val n2 = s2.to_i64() ?? -999
    print "n2={n2}"
    0
```

Compiled via `native-build --source . --entry t.spl --backend cranelift
--mode one-binary` on the stage3 self-hosted binary
(`build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`) and run:

```
n=<value:0x3039>
n2=341095809
```

Expected `n=12345` / `n2=12345`. Two distinct wrong outputs from the same
source value:

- `n`: prints the raw tagged/boxed representation `<value:0x3039>` instead of
  being unwrapped to a plain `i64` for string interpolation. Note `0x3039 ==
  12345` — the correct integer **is** inside the box, so `to_i64()`/`??`
  itself produced the right payload; the bug is in how `{n}` interpolation
  reads/formats an `i64` that arrived via `text.to_i64() -> i64?` + `??`
  coalesce (the interpolation code path apparently doesn't unbox it before
  formatting, or picks the wrong print-dispatch arm for a still-tagged
  value).
- `n2` (same literal, routed through `.trim()` first): prints a *different*
  wrong integer (`341095809`) rather than the boxed-tag string seen for
  `n`. Not reproduced deterministically across sessions — an earlier probe
  in the same investigation (via a `rt_process_run`-sourced string, not a
  literal) saw `675995905` for the same `"12345".trim().to_i64()` shape.
  The non-constant wrong value suggests uninitialized/misinterpreted memory
  being read back as the payload, not a fixed miscompile constant — consistent
  with a box/unbox or ABI mismatch rather than an arithmetic error in
  `to_i64` parsing itself.

## Why this isn't the parse-memory bug it was found investigating

Confirmed isolated from `rt_process_run`, from `--low-memory`, and from any
of that investigation's driver.spl changes — reproduces on a two-line
`main()` with only stdlib calls, no extern declarations, no other project
code involved. Purely a `to_i64()` + `??` + print-interpolation codegen
question.

## Root cause

Not bisected. Likely the same box/unbox family flagged in
`hosted_native_option_try_unwrap_payload_leak_2026-07-19.md`'s "Related /
class" section (`box_enum_payload_if_needed` gating, `rt_enum_payload`
extract/unbox path shared across Option shapes) — that doc's repro is
`.?`/`if val`; this one is `??` + print, a different lowering surface that
may share the same underlying Option-ABI representation bug. Needs its own
bisection before assuming it is the exact same root cause.

## Repro

```sh
SB=build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple
mkdir -p /tmp/toi64repro && cd /tmp/toi64repro
cat > t.spl <<'EOF'
fn main() -> i64:
    val s = "12345"
    val n = s.to_i64() ?? -999
    print "n={n}"
    val s2 = "12345".trim()
    val n2 = s2.to_i64() ?? -999
    print "n2={n2}"
    0
EOF
"$SB" native-build --source . --entry t.spl --backend cranelift --mode one-binary -o out
./out   # expect n=12345 / n2=12345, observe n=<value:0x3039> / n2=<garbage>
```

Not yet added to `scripts/check/native-smoke-matrix.shs` — future session
should add a case here (matching the `optnil` case style in the sibling bug
doc) once this is bisected enough to know the expected fix shape.

## Repro matrix (2026-07-21)

Isolated the exact trigger with four variants (all compiled and run via the
**prebuilt** `build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`,
`--entry-closure`, cranelift, one-binary — the checked-in artifact is the
**Rust seed**, confirmed by disassembly, not the pure-Simple compiler):

| case | source | result |
|------|--------|--------|
| (a) `??` result, interpolation | `val n = "12345".to_i64() ?? 0`; `print "n={n}"` | `n=<value:0x3039>` (BUG) |
| (b) `??` result, plain `print(n)` | same `n`; `print(n)` | `<value:0x3039>` (BUG, same fallback — not interpolation-specific) |
| (c) plain `i64`, interpolation | `val m: i64 = 12345`; `print "m={m}"` | `m=12345` (correct) |
| (d) `??` result used arithmetically then interpolated | `val p = n + 1`; `print "d_arith p={p}"` | `p=6.0987...e-320` (BUG — `p`'s bits reinterpreted as a raw f64, proving the mistyping propagates through arithmetic too) |
| (e) `??` result returned from a fn with an explicit `-> i64` | `fn parse_it(s: text) -> i64: s.to_i64() ?? -999`; interpolate `parse_it(...)` directly | `n=12345` (correct — an explicit return-type annotation supplies the missing type) |
| (f) `??` interpolated directly, no `val` binding | `print "f_inline n={s.to_i64() ?? -999}"` | `n=<value:0x3039>` (BUG — rules out the `val` binding as the cause; the defect is in `??`'s own exported type) |

`bin/simple test` / `bin/simple run` could not be exercised: the worktree's
own checked-in `release/x86_64-unknown-linux-gnu/simple` (pure-Simple,
self-hosted) segfaults or fails on essentially any invocation at this pinned
commit (`-c`, plain `<file.spl>`, `native-build`, `simple test`) — unrelated
pre-existing breakage at this exact commit, not this bug's fault; see
"Fix + verification status" below for the analogous fresh-build gap on the
Rust-seed side.

## Root cause (confirmed via `gdb`/`objdump`, 2026-07-21)

`gdb` breakpoints on the compiled repro (case (a)) show `spl_main` calling
`rt_value_to_string(0x3039)` directly (tail-call-inlined through the
identity wrapper `rt_value_to_string` -> `rt_to_string` in
`runtime_native.c`), which hits the `<value:0x%llx>` fallback because
`rt_core_is_int`/`is_float`/`is_special` all reject a *raw, untagged* i64
bit pattern. `objdump` on case (f) confirms the value's bits are correct
(0x3039 == 12345) but arrive unboxed. `rt_value_to_string` is a symbol that
exists ONLY in `runtime_native.c`/`src/compiler_rust` — never in
`src/compiler/*.spl` — so the repro exercises the **Rust seed's** codegen,
not the pure-Simple compiler.

The seed's `src/compiler_rust/compiler/src/hir/lower/expr/control.rs`
`lower_coalesce` (the `??` operator's own HIR lowering) computes the
coalesce expression's result type as:

```rust
let result_ty = if expr_hir.ty == TypeId::NIL {
    default_hir.ty
} else {
    expr_hir.ty          // <-- BUG: the LEFT operand's type, still Optional-wrapped
};
```

For `s.to_i64() ?? -999`, `expr_hir.ty` (the left operand `s.to_i64()`'s
type) is `i64?`, represented as `HirType::Pointer { inner: TypeId::I64 }`
(`type_resolver.rs`'s uniform representation for every `T?`) — not the bare
`TypeId::NIL` the `if` checks for — so `result_ty` keeps the *Optional*
wrapper instead of narrowing to `TypeId::I64`.

That wrapped TypeId then reaches
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs`'s
value-display boxing decision (both the `rt_value_to_string` interpolation
call-site and the separate `print`/`println`/`eprint`/etc call-site — each
independently checks `arg.ty` against the bare scalar `TypeId` constants
`I8..U64`/`F32`/`F64`/`BOOL` to decide whether to `BoxInt`/`BoxFloat`/
`rt_value_bool` the value before it reaches the runtime). A Pointer-wrapped
TypeId never matches any of those checks, so the value is handed to the
runtime raw/unboxed, and the runtime's tag-dispatch can't decode an
untagged scalar — hence `<value:0x...>`. This explains every case in the
matrix: (a)/(b)/(f) all reach this boxing decision with a wrapped TypeId;
(d)'s arithmetic (`n + 1`) inherits `n`'s wrong type, so `p`'s boxing
decision picks the WRONG scalar renderer (float) instead of skipping
boxing, reinterpreting `p`'s raw int bits as a double; (c) and (e) both have
an explicit, non-Optional `i64` type available (a `: i64` annotation, or a
function's declared `-> i64` return type) that never goes through
`lower_coalesce`'s narrowing at all, so the boxing decision sees a bare
`TypeId::I64` and works correctly.

## Fix (2026-07-21)

Per the "adjacent, not identical" framing vs the already-landed `??`/`.?`
payload-producer fixes (`hosted_native_option_try_unwrap_payload_leak_2026-07-19.md`):
`??`'s VALUE was already correct (0x3039 == 12345, no corruption) — this is
a **consumer/display-side** decode-by-type gap, not a producer bug. Fixed at
the display side, not in `lower_coalesce`: both boxing-decision sites in
`lowering_expr_builtin.rs` now resolve `arg.ty` through the type registry
and, when it is `HirType::Pointer { inner, .. }` with `inner != arg.ty`
(an Optional wrapper, guarded against self-reference), use `inner` in place
of `arg.ty` for every subsequent boxing check. This mirrors the
already-established `TypeRegistry::get_type_name` /
`enum_payload_type_for_method_receiver` pointer-unwrap pattern used
elsewhere in this exact codebase for the identical "Optional-wrapped TypeId
reaches code that expects the bare payload type" shape (see
`lowering_expr_method.rs`'s `Some(HirType::Pointer { inner, .. }) if *inner
!= ty => ...` guard). The fix is general — it applies to every scalar kind
(signed/unsigned int, float, bool), not an i64 special-case — and touches
neither `??`'s own value production nor the runtime's `rt_to_string`
dispatch.

Files changed: `src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs`
(two call sites: the `rt_value_to_string` boxing decision, and the
`print`/`println`/`eprint`/`eprintln`/`print_raw`/`eprint_raw`/`dprint`
boxing decision — case (b), plain `print(n)`, goes through the latter and
showed the identical `<value:` symptom, confirming both sites share the
same gap).

## Fix + verification status

Confirmed by direct static analysis (gdb/objdump root-cause trace, source
reading, precedent match) and confirmed to compile cleanly under `cargo
build --profile bootstrap -p simple-driver` (twice, independently, at this
pinned commit and again at `main` HEAD after transplanting the identical
patch — no errors, only pre-existing unrelated warnings both times).

**NOT verified end-to-end (compile-and-run) with the patched binary.** Every
freshly-`cargo`-built seed binary tested in this sandbox — patched or
unpatched, at this pinned commit or independently at `main` HEAD, under
every combination of `--entry-closure`, `--threads 1`,
`SIMPLE_NO_STUB_FALLBACK=1`, `SIMPLE_BOOTSTRAP=1`, a cleared
`build/native_cache`, and building `simple-native-all` as a prerequisite —
fails `native-build` on any program calling `.to_i64()` with `[mir-lower]
WARNING: unresolved method call 'to_i64'` / `MIR lowering error: unresolved
method call: to_i64`. That exact diagnostic string is sourced from
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2418` — the
**self-hosted Simple compiler's own** MIR lowering, reached via
native-build's worker/self-hosted-delegation path, a DIFFERENT path from
the direct-Rust-seed-codegen path this bug's original repro's disassembly
exercised. Only the prebuilt, checked-in
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple` (main repo, dated
2026-07-18, predating this pinned commit) resolves `.to_i64()` successfully;
it was used for the entire pre-fix repro/matrix above, but by definition
cannot exercise a source change made after it was built. This `to_i64`
resolution gap on fresh-cargo-built seed binaries is a **separate,
pre-existing, unrelated toolchain issue** — flagging it here rather than
filing a dedicated doc since it wasn't independently bisected; a future
session with a working from-source build should file and fix it, at which
point this bug's regression coverage
(`test/03_system/native/option_nullcoalesce_i64_print_interp.spl`, expected
rc 42) can finally be run.
