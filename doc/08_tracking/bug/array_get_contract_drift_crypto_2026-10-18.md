# Array get contract drift exposed by crypto nested access

Status: OPEN. Native evidence reproduced; proposed source repair UNRUN.

Campaign retry3, target 4bbc6fe91ae, admitted compiler SHA prefix 70194:
`module_compile_object.log` in
`/home/yoon/dev/simple-phase3-targeted-diagnostics-retry3-20261018/verification/module-diagnostics/attempt.J56KlM/1/`
reports unresolved len at bigint lines 329, 556, 564 and unresolved get.
The annotation-only commit 366fae64ee7 did not fix this failure.

Actual source trace:
- HIR `hir_lowering/types.spl:1287`: `list` becomes `Array(Any)`;
  `[list]` therefore preserves the nested array declaration.
- MIR `method_calls_literals.spl:4253` sends both get and at into
  `lower_array_first_or_last`.
- That helper recovers the array element HIR type, then at line 5664
  constructs `Optional(elem_hir_type)` and records the returned option.
- Crypto uses this optional result directly as a collection. Changing the
  producer annotation cannot remove that wrapper. This is not evidence of
  lost nested type information in HIR serialization.

Contract conflict: `test/01_unit/language/module_var_array_get_method_spec.spl`
expects direct text from get, based on an August interpreter check. The current
pure-Simple interpreter `call_method_eval.spl` array dispatcher implements at
with optional semantics but has no get branch. The public array facade lists
neither accessor. Native get explicitly returns an Option. These sources do
not justify globally changing get to return an unwrapped element.

Bounded compatibility repair: use indexing for fixed-size bigint helper
results (division always produces two limb arrays; swaps/ladder produce two
or four coordinate arrays). Remainder index zero is protected by its nonempty
check. Preserve the four nested annotations. This does not alter arithmetic.
This source repair is not a compiler root fix and is not runtime-qualified.

Retirement/contract gate: `test/fixtures/compiler/nested_array_get_contract_probe.spl`
retains the original direct nested get usage, without indexing workaround.
Once the public get contract is selected, run it and the existing module-var
get spec on both self-hosted interpreter and native lanes. If direct get is
supported, both must pass including nested len/value checks. If get is Optional,
update the public contract and obsolete direct-get specs explicitly, add
Some/None and out-of-range tests for both lanes, and reject unwrapped use with
a precise type diagnostic. Do not silently declare this discrepancy resolved.

No fourth compiler attempt is authorized in this session. The crypto regression
and source repair remain UNRUN pending a new authorized verification cycle.

The full original direct-get regression is preserved verbatim below a status
comment in `test/fixtures/compiler/crypto_nested_get_contract_spec.spl`; it is
not counted as passing or replaced by the indexing assertions.

Index proof: `_bi_divmod_i64` returns two arrays in its zero-divisor, one-divisor,
and general branches, so divmod[0] and divmod[1] exist. `remainder[0]` is guarded
by `remainder.len() > 0`. `_bigint_cswap_pair` returns four arrays in both swap
branches; swapped/final_swapped positions 0..3 all exist. `_bigint_ladder_step`
always returns four computed coordinates; step positions 0..3 all exist. Both
public diagnostic probes select position zero from those same four-item results.
The regression checks both swap branches, all ladder values, division special
branches, and multi-limb byte roundtrip; no empty-shape assumption was added.
