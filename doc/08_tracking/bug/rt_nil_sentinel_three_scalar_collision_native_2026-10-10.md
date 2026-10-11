# `v == nil` is TRUE for the integer 3 and for `true` under staged-native codegen (RT_NIL sentinel collision)

Status: OPEN as a representation defect (root-cause codegen fix in progress on
`work/rel-native-nil-compare-20261010`, another lane). This record is the
reproduction record the repo was missing (the robustness audit of 2026-10-10,
`CURRENT_BUG_PREVENTION.md` class 6, found no committed record for the exact
int-3 / bool-true case). The **static** half — refusing or warning on the
comparison before it reaches codegen — is the `E-TYPE-NIL-COMPARE` typing rule
landed on `work/rel-robust-frontend-diag-20261010` (family
`nil_compare_non_optional`, warn-first).

## Symptom

In code compiled by a stage-2 (staged-native) compiler, comparing a value whose
static type is a NON-optional scalar against `nil` does not answer "false":

```
fn raw_is_nil(v: i64) -> bool: v == nil        # i=3  -> true   (every other i -> false)
fn bool_is_nil(v: bool) -> bool: v == nil      # true -> true, false -> false
```

The seed interpreter answers `false` for every input, which is why every
interpreted spec stayed green while the native build misbehaved.

## Evidence

Probe compiled by the frozen stage 2 (`simple-bootstrap 1.0.0-rc.1`, sha256
`49cbd0052706c055…`, tree `6b540f21546`, Windows host), recorded in
`doc/08_tracking/bug/hir_codec_put_i64_three_encoded_as_nil_native_2026-10-10.md`
(branch `work/rel-frontend-parallel-20261010`):

```
i=3 raw_is_nil=true
bool f=false t=true
OLD=[0,1,2,N,4,5,N]        # HirCodecWriter.put_i64 over 0..5 and [1,2,3].len()
BOOL_OLD=[0,N,N,0,N]       # false,true,true,false,true
```

Consequence seen in production: the HIR cache never hit under a stage-2
compiler (`[hir-cache] hits=0 misses=1163 stores=1133`, HIR 2278 s of a 2818 s
front end) because `HirCodecWriter.put_i64`/`put_bool`
(`src/compiler/20.hir/hir_codec_support.spl`) decided "write the nil marker"
with `v == nil` on `i64`/`bool` slots; every `3` and every `true` was encoded
as `N`, the decoder desynchronised (`no SymbolKind arm for tag 1448`) and the
entry was rejected. Three stored entries of 261,898 / 121,701 / 126,515 lines
contained **zero** lines equal to `3`.

## Root cause (representation)

Under staged-native codegen a scalar slot compared against `nil` is compared
against nil's immediate encoding. `RT_NIL` is the sentinel value 3
(`src/compiler/00.common/assurance/flight_rules.spl` already notes "RT_NIL is
the sentinel value 3 and is therefore truthy"), and a `bool true` shares the
same low bits once widened, so:

- `i64 == nil` is `v == 3`;
- `bool == nil` is `v == true`.

The comparison has no language meaning: a non-optional `i64`/`bool`/struct can
never hold `nil`, so the compiler is answering a question the type system says
cannot be asked. Related earlier records:
`pure_simple_option_i64_ifval_always_some_eqnil_always_false_2026-08-08.md`,
`bare_optional_in_condition_position_wrong_branch_2026-08-01.md`,
`nil_optional_enum_return_truthy_2026-08-21.md`.

## Prevention (two halves, two lanes)

1. **Static** (this lane, `work/rel-robust-frontend-diag-20261010`):
   `E-TYPE-NIL-COMPARE` in `src/compiler/30.types/type_infer/inference_expr.spl`
   — `x == nil` / `x != nil` where `x` resolves to a non-optional concrete type
   is diagnosed at the comparison span ("comparison is always false/true;
   declare `T?` if nil is intended"). Registry family
   `nil_compare_non_optional` in
   `src/compiler/90.tools/lint/_LintMain/config_and_model.spl`, default
   `warn`; the driver typecheck pass caps it at Warn (warn-first lifecycle,
   `--assurance-warning-phase` ramp) until the measurement baseline in
   `scripts/check/frontend_diag_baseline.txt` is burned down. Spec:
   `test/01_unit/compiler/lint/nil_compare_non_optional_spec.spl`.
2. **Representation** (`work/rel-native-nil-compare-20261010`): the codegen
   must not lower a scalar-vs-nil comparison to an immediate compare against
   `3`; pin with a per-backend sentinel-parity spec (audit task 6b).

## Still to verify

- Count of `src/**` sites the static rule hits (one warning-phase measurement
  run; recorded in `C:/dev/simple-bootstrap-storage/robustness/FRONTEND_DIAG_FINDINGS.md`
  and the ratchet baseline).
- After the representation fix lands in a rebuilt stage 2: the probe above
  prints `i=3 raw_is_nil=false` and `t=false`, and the codec round-trip gate
  (`SIMPLE_HIR_CODEC_ROUNDTRIP=1`) reports `ok=true stable=true`.
