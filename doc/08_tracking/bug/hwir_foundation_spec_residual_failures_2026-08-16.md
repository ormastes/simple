# hwir_foundation_spec residual failures after missing std.spec import fix (2026-08-16)

Status: RESOLVED 2026-08-19 (was OPEN P2) — residual 21 confirmed live 2026-08-17; the *infra* half had been silently clobbered and was re-applied, see the bottom section
Status: OPEN (P2) — residual 21 confirmed live 2026-08-17; the *infra* half had been silently clobbered and was re-applied, see the bottom section
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Context
The mass failure of `test/01_unit/compiler/50.mir/hwir_*` specs (batch timeout at
550s, per-spec 100% fail) had an infra root cause: commit `6fe33f889dee`
"test(hwir): modernize foundation specifications" (and sibling modernizations)
added `step("...")` calls to 7 specs WITHOUT adding `use std.spec.*`, so every
test in those files errored with `semantic: function 'step' not found`.

Fixed 2026-08-16 by inserting `use std.spec.*` in:
- hwir_foundation_spec.spl, hwir_mir_function_extract_spec.spl,
  hwir_zca_load_effect_outcomes_spec.spl, hwir_zca_rv64_contract_spec.spl,
  hwir_zca_rv64_ld_sd_rows_spec.spl, hwir_zca_rv64_rows_spec.spl,
  hwir_zca_rv64_stack_memory_rows_spec.spl

After the fix: all four zca_rv64/load_effect specs and the contract spec are
fully GREEN (2/2, 4/4, 2/2, 4/4, 4/4); hwir_foundation_spec went 0/50 -> 29/50;
hwir_mir_function_extract_spec 41/55 (14 residual substantive failures).

## Residual (owned by riscv_gen2_hwir_foundation lane)
`test/01_unit/compiler/50.mir/hwir_foundation_spec.spl`: 21 remaining failures,
all substantive against the HWIR slice, not test infra:
- 17x `expected false to equal true` (strict lowering / row-construction
  predicates returning false)
- 2x `expected subject to be truthy, got false`
- 1x `semantic: invalid assignment: complex indexed field receiver is not
  supported` (interpreter limitation hit by a test body)
- 1x diagnostic-code mismatch: got `HWIR-E-VHDL-IDENTIFIER: module name is not
  a stable VHDL identifier`, expected `HWIR-E-MODULE-SUMMARY: module summary
  requires a concrete matching profile`

These look like the spec asserting behavior the current
`src/compiler/50.mir/hwir/*` + `src/compiler/70.backend/backend/hwir_to_vhdl.spl`
slice does not yet implement (or diagnostics reordered). Left to the
`.spipe/riscv_gen2_hwir_foundation` lane, which owns these modules and specs.

## Unblock condition
riscv_gen2_hwir_foundation lane reconciles hwir_foundation_spec expectations
with the current strict HWIR lowering/diagnostic order, or implements the
missing behavior. Repro: `bin/simple test
test/01_unit/compiler/50.mir/hwir_foundation_spec.spl`.

## 2026-08-17 — the infra fix was NOT in the tree; re-applied

Re-running the repro gave **0/50, not 29/50**:

```
$ bin/simple test test/01_unit/compiler/50.mir/hwir_foundation_spec.spl --no-session-daemon --sequential
Results: 50 total, 0 passed, 50 failed
# all 50: `semantic: function `step` not found`
```

`grep '^use '` showed **no `use std.spec.*`** — in `hwir_foundation_spec.spl`
and in **all seven** files this record says were fixed on 2026-08-16. So the
2026-08-16 infra fix had been lost (the working-copy clobber mode `.claude/rules/vcs.md`
documents: an Edit-tool change that was never snapshotted, or a stale whole-WC
sync). Nothing about it was subtle to detect and it was invisible in the record,
which read as though the fix were in place.

Re-applied `use std.spec.*` to all seven, and re-measured every one:

| spec | result |
|---|---|
| `hwir_foundation_spec` | **50 total, 29 passed, 21 failed** |
| `hwir_mir_function_extract_spec` | **55 total, 41 passed, 14 failed** |
| `hwir_zca_load_effect_outcomes_spec` | 2 total, 2 passed, 0 failed |
| `hwir_zca_rv64_contract_spec` | 2 total, 2 passed, 0 failed |
| `hwir_zca_rv64_ld_sd_rows_spec` | 4 total, 4 passed, 0 failed |
| `hwir_zca_rv64_rows_spec` | 4 total, 4 passed, 0 failed |
| `hwir_zca_rv64_stack_memory_rows_spec` | 4 total, 4 passed, 0 failed |

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59537240 bytes,
2026-08-17 12:58:51 (Rust seed). Invocation for each:
`bin/simple test <spec> --no-session-daemon --sequential`.

29/50 and 41/55 are **exactly** the numbers this record documents, so the
residual is reproduced bit-for-bit and this section adds no new failure — it
restores the baseline the record describes.

**Residual status: unchanged and genuinely OPEN.** The 21 remaining failures are
substantive assertions against the HWIR slice, not infra, and per
`.claude/rules/testing.md` they are left RED rather than weakened. Ownership
stays with the `.spipe/riscv_gen2_hwir_foundation` lane; the unblock condition
above is unchanged.

## Re-run on rebuilt seed 2026-08-17 (seed md5 669150b61f2f20401a6a895ae54e9fee, 59550432 bytes, mtime 2026-08-17 20:10:45)

    bin/simple test test/01_unit/compiler/50.mir/hwir_foundation_spec.spl --no-session-daemon --sequential
    SPEC FILE VERDICT: ... declared>=50 executed=50 passed=29 failed=21 dropped=0   (exit 1)

Identical to the recorded baseline (29/50 passing, 21 failing). The seed rebuild
changed nothing here. Status unchanged: OPEN (P2).

## 2026-08-19 — RESOLVED: both specs fully GREEN (50/50 and 55/55)

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59773320 bytes,
2026-08-19 15:14:28 (fixed seed with the 2026-08-19 interpreter repairs).
Baseline re-confirmed first on that binary: still 29/50 and 41/55 — the
interpreter fixes alone healed nothing. The 21+14 residuals decomposed into:

**Product defects fixed (src/compiler/50.mir/hwir/):**
- `mir_to_hwir.spl`: the canonical `and` fixture named its output port `out`,
  a VHDL reserved word, so `shape_diagnostic()` failed HWIR-E-PORT before every
  assertion; renamed to `out_c` (spec fixtures updated to match). This alone
  took foundation 29→35.
- `sequential.spl` `readable_width`: guards referencing an "all"-kind output
  binding (`fetch_ready`, `dispatch_valid` — pure combinational one-bit
  conjunctions, readable per VHDL-2008 out-port readback) resolved to -1, so
  the entire stateful frontend failed HWIR-E-SEQUENTIAL-GUARD and all 6
  stateful/sequential foundation tests were unreachable.
- `zca_rows.spl` C.LUI row: summary declared `comb_op_count: 22` but the row
  holds 13 comb + 5 compare + 5 select = 23, failing HWIR-E-MODULE-COUNT and
  poisoning the whole migrating-predecode composition (decoder → stateful
  frontend product). Corrected to 23; extract spec's pinned 22 updated.

**Spec-side repairs (intent preserved, no assertion weakened):**
- The interpreter rejects `xs[i].field = v` and returns COPIES for indexed
  reads; every mutation test rewritten as bind → mutate → write back
  (`val e = xs[i]; e.field = v; xs[i] = e`), including the
  `for local in function.locals: local.type_ = word` fixture loop (loop vars
  are copies too — rebuilt the list).
- Stale emitter expectations: constants are now explicit binary literals
  (`"00...01111111111111111"`), not `std_logic_vector(to_unsigned(...))`;
  constants keep the MIR local's own name (`shift`, not `shift_amount`;
  `mask`, not `field_mask`); the two-stage field graph keeps `field` as an
  internal signal (2 signals / 3 comb ops); `cbreak_parcel` typo →
  `cebreak_parcel`.
- Fixture profile mismatches: `parcel_mask`/`bad_select` summaries carried
  `"rv32"`/`"rv32-zca-critical"` against configs whose profiles are
  `"rv32-zca"`/`"riscv-gen2-rv32-zca-critical"`, tripping HWIR-E-MODULE-SUMMARY
  before the check under test.
- Diagnostic-order updates where the fail-closed behavior is unchanged but a
  broader check legitimately fires first: serializer-unsafe module name ⇒
  HWIR-E-VHDL-IDENTIFIER; altered decoder pin ⇒
  HWIR-E-PARCEL-FRONTEND-SEQUENTIAL-TEMPLATE. The C.J / C.BEQZ reject tests
  mutated only the signature (leaving Arg locals stale), so the generic
  HWIR-E-MIR-LOCAL check fired; fixtures now mutate the matching local and the
  intrinsic-specific HWIR-E-MIR-SIGNATURE rejections under test fire.

Final: `hwir_foundation_spec` **50/50**, `hwir_mir_function_extract_spec`
**55/55**. The full stateful frontend product now compiles end-to-end
(`compile_strict_zca_single_outstanding_frontend_product` emits VHDL).
Status: RESOLVED.
