# I-6 H-6 done

## Flag added (new)

`SIMPLE_EMIT_CLIF=<path>` env var. Set on the env when running
`bin/simple compile … --native …`. Optional companions:

- `SIMPLE_EMIT_CLIF_FILTER=<substr>` — only dump functions whose MIR name
  contains `<substr>`. Without it, every function is dumped (verbose).
- `SIMPLE_EMIT_CLIF_OPTIMIZE=1` — also dump post-egraph CLIF (the
  authoritative answer for "did Cranelift fold X").

Output is appended to `<path>` (so multiple `compile` invocations stack).
Implementation: `src/compiler_rust/compiler/src/codegen/common_backend.rs`
`compile_function` (just before `define_function`); ~50 lines, single
diff hunk. No CLI plumbing changed — env var is checked at the codegen
hot path, costless when unset.

### Invocation that produced the verdict

```
DRIVER=src/compiler_rust/target/release/simple
SIMPLE_EMIT_CLIF=/tmp/i6_repros/clif_h6_const_clean.txt \
SIMPLE_EMIT_CLIF_FILTER=rotl \
SIMPLE_EMIT_CLIF_OPTIMIZE=1 \
"$DRIVER" compile /tmp/i6_repros/h6_const_clean.spl \
    --native -o /tmp/i6_repros/h6_const_clean_bin
```

(Note: `bin/simple compile … --native` swallows the wrapper's output on
this branch — the underlying release driver `src/compiler_rust/target/
release/simple` works directly. Likely a separate wrapper bug; not in
scope for I-6.)

## CLIF excerpt (post-opt) — h6_const_clean, literal k=7

```
function u0:677(i64) -> i64 system_v {
block0(v0: i64):
    v2 = iconst.i64 7
    v3 = ishl v0, v2     ; v2 = 7
    v5 = iconst.i64 57
    v6 = sshr v0, v5     ; v5 = 57   <-- sshr defeats the rotl rule
    v7 = bor v3, v6
    return v7
}
```

Compare against `vendor/cranelift-codegen/src/opts/shifts.isle:271`:

```
;; (bor (ishl x k1) (ushr x k2)) == (rotl x k1) if k2 == ty_bits - k1
```

Rule needs `ushr`, Simple emits `sshr`. No fold.

## Verdict

**Real codegen regression** — but the underlying mechanism is not "rotl
folding fails on constant N" as the B7 hunt-list said. Simple has no
intrinsic `rotl`; it builds rotation from `(x << k) | (x >> (W - k))` in
stdlib (`src/lib/common/crypto/types.spl::rotl32`/`rotl64`). Cranelift's
egraph has the right rule, but Simple's MIR `ShiftRight` lowers signed
RHS via `sshr`. Default integer is `i64` (signed), so every crypto rotl
emits `ishl + sshr + bor` and never collapses to a single x86 `rol`.

## Where the verdict was recorded

- `doc/08_tracking/bug/bug_h6_rotl_unfolded_2026-04-25.md` — full bug
  doc with CLIF excerpts, ISLE rule citation, three repros, fix sketches.
- `.sstack/crypto-pure-simple-port/research/sugar_perf_repros.md` — H-6
  section updated from DEFERRED → REAL REGRESSION (filed); TL;DR row
  also updated.

## Repros (kept under /tmp/i6_repros/, NOT in /tmp/r_d_repros/)

- `h6_const_clean.spl` — canonical `(x << 7) | (x >> 57)` literal-k form
- `h6_const_var.spl` — variable-k baseline, same body
- `h6_const_masked.spl` — R-D's malformed `(1 << n) - 1` mask form (kept
  to show the mask is *not* what defeats folding — sshr is)
- Plus copied-emitted CLIF dumps `clif_h6_*.txt`

## Follow-ups (not in I-6 scope)

1. Cheapest fix per bug doc option 1: add `rotl`/`rotr` stdlib intrinsic
   that lowers to `builder.ins().rotl(x, k)` in
   `src/compiler_rust/compiler/src/codegen/instr/`. Replace bodies of
   `rotl32`/`rotl64`/`rotr32`/`rotr64` in
   `src/lib/common/crypto/types.spl`. One-shot fix for all crypto.
2. Wrapper bug: `bin/simple compile` swallows release-driver output
   (only direct-binary invocation prints "Compiled X -> Y"). Out of
   scope for H-6 but worth a separate note.

## advisor() points & how I handled them

1. **"Pre-opt CLIF won't answer H-6 — call optimize() first."** Done. The
   knob has `SIMPLE_EMIT_CLIF_OPTIMIZE=1` mode that clones the function,
   calls `Context::optimize(isa, ControlPlane)`, and dumps the result. The
   verdict is based on post-opt CLIF — the authoritative answer.
2. **"Prefer env var over CompileOptions threading."** Done. Single hook
   in `common_backend::compile_function`, no plumbing across files. Total
   diff: one Rust file, ~50 lines.
3. **"Test multiple repro forms — R-D's `(1 << n) - 1` mask form is
   suspicious."** Done. Built `h6_const_clean.spl` (canonical),
   `h6_const_var.spl` (variable-k), and kept `h6_const_masked.spl`
   (R-D's). All three show the same `sshr` problem — confirmed the
   diagnosis is independent of the mask.
4. **"Confirm which path serves --native."** Done.
   `compile_file_native` → `CompilerPipeline::compile_file_to_native_binary`
   → eventually `CodegenBackend::compile_function` in
   `common_backend.rs`. The env var fires there. Verified by seeing CLIF
   for `rotl_clean`, `rotl_var`, etc. functions.
5. **"`--mode=smf`/`--mode=native` false-PASS memory note doesn't apply
   here."** Correct — I-6 reads IR, not test results.
