# Typed-local workaround for bootstrap float literal decoding

Status: source workaround candidate; native **UNRUN**. This is not the
underlying compiler repair and does not qualify a new Phase2 producer.

## Evidence and ownership

The original scalar fixture compiled and executed on both output backends
with producer `3bd458857152a0c1be96b08f21c87ebd686c3f155a87f0f0eb7633d1bd2b07cb`:
six checks, four passed, two failed. f64/f32 literal checks failed while runtime
arithmetic, text parsing and declared enum transport passed. The original
fixture is retained byte-for-byte from source `a1b1b200700`; its assertions
are not weakened. The 13-case enum-width fixture also remains unchanged.

Upstream root repair `75c893d8cf99fe46d91b62b2d30bed1420d38f84` records the
same `convert_flat_expr` expression calling the text-returning accessor
`expr_get_float` but numerically converting its handle. Its canonical record
is `doc/08_tracking/bug/native_cross_module_call_result_type_loss_2026-10-05.md`
on release/1.0. The repair preserves imported callable return metadata in the
Rust bootstrap Cranelift backend. Its executed Linux native-project test
contains independent C/runtime and local-text controls, an alias, a cross-module
float result, and a local declaration overriding an imported name. That is
strong relevant evidence, not Windows bootstrap or new Phase2 qualification.

## Temporary source change

Bind `expr_get_float(idx)` to an explicitly typed `text` local before invoking
`.to_float()`. This gives the old bootstrap backend an explicit receiver type
instead of relying on the lost imported-call result metadata. Evaluation order,
one accessor call, numeric parsing, and returned AST kind remain the same.
The text local is used immediately before returning; no cache, global state,
heap retention policy, or shared mutable alias is introduced. Actual memory
and timing effects remain unmeasured.

The workaround applies only to the unsuffixed `EXPR_FLOAT_LIT` branch. The
existing suffixed branch already binds the accessor result separately and is
not silently rewritten. Frozen source61e26, frozen consolidated sourcef7e0784,
and their running compilers are unchanged.

## Required native comparison and retirement

Use one canonical admitted 20-job lane when capacity is available. Preserve
the old binaries and failing receipts. Do not rematerialize a full source for
this patch without the consolidated source owner selecting the next epoch.

1. Build a Phase2 candidate containing this source workaround with the same
   pinned old bootstrap producer. Preserve exact source, producer, target,
   backend, runtime/toolchain, cache identity and closed-tree receipts. This
   is the source-workaround alternative to rebuilding the Rust seed first.
2. Compile and run `test/fixtures/compiler/float_literal_transport/main.spl`
   on Cranelift and LLVM. Require exit0, exactly ordered case1..6 records
   with zero cumulative failures, and `float literal transport: 6 checks, 0 failures`.
   An infrastructure failure or compile-only success is not a passing check.
3. Compile and run unchanged `test/04_smoke/native_enum_numeric_payload_widths.spl`
   on both backends. Require exit0, exactly ordered case1..13 records with
   zero cumulative failures and `checks=13 failures=0`. Preserve case-specific
   failures separately: Any/width/ABI defects are not automatically attributed
   to literal parsing.
4. Record compile/run elapsed time and process-tree peak/retained RSS for the
   same fixtures and configuration. Compare correctness and memory together;
   no performance claim follows from fewer source tokens or compile success.

The eventual replacement bootstrap source must include both imported-return
repair75c893 and the float cast/out-slot repair merged by PR2562 as
`70cf3b0ef32c2e0c20f40a5b6459ff05d14bd13e` (implementation parent16d803208c5).
The latter repairs cross-block/call-result float bit decoding and mutable
extern output addresses; it is distinct from identifying an imported text
result. Neither patch changes an already-built seed or live producer.

Retire this workaround only after the repaired seed is pinned and qualified,
a new Phase2 compiler is built **without this local source workaround**, and
the original six and thirteen checks pass on both output backends. The
underlying upstream repair and unchanged chained expression must remain in
that proof. Linux bootstrap test success alone is insufficient for retirement.
