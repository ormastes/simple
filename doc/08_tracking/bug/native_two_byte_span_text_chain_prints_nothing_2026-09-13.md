# Native: 3-operand text `+` chain over a 2-byte span loop reportedly prints nothing (unfiled observation, unfiled bug)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Filed: 2026-09-13
- Status: **UNCONFIRMED — native reproduction blocked by a pre-existing,
  tree-wide `native-build` breakage** (see "Blocking issue" below). The
  interpreter side is confirmed and behaves correctly for every shape tried.

## The claim being investigated

A `while i < sp.len(): ... var out = a + "=" + x ... print(out)` loop over a
**2-byte** span (`U16le`/`U16be`-backed) was reported to print no elements
under native codegen (seed pipeline `native-build --mode=dynload`), while
4-byte and 8-byte spans print correctly.

## Reproducer

```simple
use lib.common.bytes.span.{ByteSpan, ByteBuffer}
use lib.common.bytes.ints.{U16le}

fn main():
    val sp = U16le.of(0xBEEF).to_span()
    var i = 0
    while i < sp.len():
        val a = "elem"
        val x = sp.get(i).to_i64()
        var out = a + "=" + x
        print(out)
        i = i + 1
```

Two discriminating variants, as directed:

- **(a) interpolation instead of the 3-operand `+` chain** — replace
  `var out = a + "=" + x` with `var out = "{a}={x}"`.
- **(b) same 3-operand `+` chain, 4-byte span instead of 2-byte** — swap
  `U16le.of(0xBEEF)` for `U32le.of(0xDEADBEEF)`.

Probe files used (kept for re-run once native-build is unblocked):
`probe_2byte.spl` (repro, 3-operand `+`), `probe_2byte_interp.spl` (variant a),
`probe_4byte.spl` (variant b, 3-operand `+` over 4 bytes).

## Interpreter (reference) — all three variants correct

```
$ SIMPLE_EXECUTION_MODE=interpreter <seed> run probe_2byte.spl
elem=239
elem=190

$ SIMPLE_EXECUTION_MODE=interpreter <seed> run probe_2byte_interp.spl
elem=239
elem=190

$ SIMPLE_EXECUTION_MODE=interpreter <seed> run probe_4byte.spl
elem=239
elem=190
elem=173
elem=222
```

`0xBEEF` little-endian is bytes `EF BE` = `239, 190` — correct. `0xDEADBEEF`
little-endian is `EF BE AD DE` = `239, 190, 173, 222` — correct. Interpreted
execution shows no divergence between the 3-operand `+` chain and
interpolation, and no length-dependent behavior, for either seed
(`build/cargo-r2/release/simple`).

## Blocking issue — native-build could not be run to completion

> **UPDATE 2026-09-13 — the `method 'len' not found on type 'i64'` half of this
> blocker is RESOLVED.** Root cause: `native_noop_normalized_invocation_v1`
> framed `aspect.mcdc_mode` (an `i64`, default 0) into a `[text]` literal without
> `.to_text()`, and `native_noop_frame_v1` calls `value.len()` on every element.
> It ran on the default native-build path before any user logic, which is why a
> 3-line program with no `.len()` hit it. Introduced `e0fa5ef45e2` (2026-09-07);
> fixed by `aspect.mcdc_mode.to_text()` in
> `src/compiler/80.driver/cache/native_noop_admission.spl:57`. Full analysis:
> `doc/08_tracking/bug/native_build_noop_invocation_frames_raw_i64_mcdc_mode_2026-09-13.md`.
>
> **This record's own claim (the 2-byte span `+` chain) remains OPEN and
> untested** — `native-build` still does not complete, now for two *different*
> reasons: `scv-authority-missing`
> (`stage3_step_omits_package_index_cold_init_scv_authority_missing_2026-09-13.md`)
> and a `(scope, msg)` arity mismatch after `aop_weave`
> (`native_build_aop_weave_one_arg_call_binds_log_scope_msg_2026-09-13.md`).
> The note below that this shares a cause with the `rt_env_vars` record is
> **not** borne out: that is a distinct defect.


Every attempt to natively build even a **trivial** program on this tree fails
before reaching codegen for the reproducer's own logic, with a semantic error
in unrelated whole-program scope:

```
$ SIMPLE_SCV_FREEZE_FALLBACK=1 build/cargo-f52/release/simple native-build \
    --mode=dynload probe2.spl -o probe2_native
...
SCV-E-SNAPSHOT: snapshot-inventory-unavailable
SCV-W-FREEZE-FALLBACK: SIMPLE_SCV_FREEZE_FALLBACK=1 is set; scanning the
  working tree directly instead of a frozen SCV snapshot
error: semantic: method `len` not found on type `i64` (receiver value: 0)
error: native-build worker exited with code 1.
```

This reproduces even for `probe2.spl` — a 3-line program (`val sp = ...;
val n = sp.len(); print(n)`) with no loop and no `+` chain at all — so the
failure is not caused by this reproducer's own source. It matches the shape
already filed in
`doc/08_tracking/bug/native_build_entry_closure_unknown_extern_rt_env_vars_2026-09-13.md`
("`native-build` is red tree-wide... No `.spl` can be native-built on this
tree with any deployed binary") and
`doc/08_tracking/bug/native_optional_unwrap_field_index_by_name_collision_2026-09-12.md`
("native-build fails for every input") — both filed OPEN, same day, no
workaround recorded. The specific error text differs (`unknown extern
function: rt_env_vars` there vs. `method 'len' not found on type 'i64'`
here), which is itself notable: two different symptoms from the same
"whole-program native-build entry-closure computation over the current tree"
step, neither caused by the file actually being built. No fix or workaround
was found in either record.

No `bin/simple` (deployed self-hosted binary) exists in this worktree to try
as an alternate driver.

`bin/simple bug-add` was not run: this worktree has no runnable `bin/simple`
(bootstrap-only seeds are the only drivers present, and neither exposes
`bug-add`).

## What is and is not established

- **Established:** the interpreter is correct for the 2-byte, 4-byte cases and
  for both the `+`-chain and interpolation forms. No divergence exists on the
  interpreter side.
- **Not established:** whether the native-codegen defect described in the task
  (2-byte span loop printing nothing) is real, is the same three-operand
  `text` `+` landmine already recorded elsewhere (see
  `doc/08_tracking/bug/...three_operand...md` / the vector_fonts landmine
  recipe #8, referenced from
  `native_cross_module_same_name_methods_collapse_to_one_impl_2026-09-13.md`),
  or is a distinct length-dependent defect (`span.len()` / `u16` element load
  for a 2-byte span). **This record cannot be closed or hardened into a root
  cause until `native-build` itself is unblocked** — see the two OPEN records
  above. Re-run this file's three probes once either of those lands a fix.

