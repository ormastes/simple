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

## Scalar access follow-up (UNRUN)

The same Optional-as-value mismatch affected `_bigint_get_bit` and
`_bigint_shift_left_one`: both used get results in integer arithmetic. Their
accesses now use indexing. Source/test call-site search found only
`_bigint_mod_safe` calling these helpers before the new regression.

For get_bit, that caller initializes i to bit_length(a)-1 and invokes the
helper only inside `while i >= 0`, decrementing i afterward. Thus n >= 0 at
all existing calls; divisor 30 gives limb_idx >= 0, and the helper returns
before access when limb_idx >= a.len(). A negative n is outside this proven
caller domain; its public contract remains unspecified/open. No negative-n
behavior or guard was invented in this repair.

For shift_left_one, zero/empty inputs return early. The loop starts i at zero,
checks i < a.len(), and increments by one without mutating a. Thus every read
is in bounds. New assertions cover empty/zero inputs, low and limb-boundary
bits, the upper-bound return, one-limb carry, propagation into a second limb,
and actual modulo use of both helpers. Expected modulo: (2^30+5) % 7 = 6.
All new executable assertions remain UNRUN; this is a source-only repair.

## Qualified native compilation and example (2026-10-18)

This later evidence supersedes the earlier UNRUN status only for the selected
native object compilation and linked example. The affected SSpec scenarios and
the unresolved get-contract probes remain UNRUN: no qualified general SSpec
runner was available. The global get contract and negative-index precondition
remain OPEN.

The repaired source compiled as the dependency closure of
`src/app/_scratch_ed/main.spl` under admitted producer SHA-256
`70194dd3e815ed6ec1da0ed7f286d14914d7946b827541beaa53080512e7f650`.
The AArch64 ELF relocatable object is 603,096 bytes, SHA-256
`381a88baf60f7a2c614447f6c6b3a9b6eb4ca832803d11464daa986509065396`.
Five modules were rebuilt with no reuse; compile and post-authority exits were
zero. The exact source SHA-256
`72dd3d80f0b75c9f3c8a58707a5810afce216c7d901d696e23d8e5e7041754ab`
occurs in the admitted target snapshot and matches this narrow landing branch.

Manual link attempt 4 reused that object and 42 retained runtime/entry objects;
it did not rebuild the Simple object. Link and executable exits were zero.
The five stdout lines exactly matched an independent affine oracle for the
Ed25519 base point, identity, identity-plus-base, doubling, and base-plus-base.
This example does not directly execute every bigint division/bit/ladder case
in the SSpec regression. No full X25519, whole-suite or Phase 3 qualification is
claimed. The resulting binary SHA-256 is
`a2fab4fe60a3cebe4d4ef93d7b909af5cbcef17e41417c4f309567b5f155e979`.

Retained local evidence root:
`/home/yoon/dev/simple-phase3-targeted-diagnostics-retry4-20261018/`.
Object assessment `terminal-assessment.json` SHA-256:
`145f51c05e26a2777b12e589fa9d3d49404138a0b41a3e01386841592049cd8a`.
Manual-link `manual-link-packet/actual4/result.json` SHA-256:
`49a6b426a8ec11c708f9a6223825b5ee0aa29cd1e67561c0027c0528bf9cde01`.
Oracle output `manual-link-packet/actual4/run.stdout` SHA-256:
`c3c7ab6211b7e70777dadd69292186091a4ed44edcb63fe7c1a5a6abce590250`.
Manual-link manifest SHA-256:
`ec25ff063cb75ce81c20bc5fe14fc47c3efac98086f3d4669d58cb787cfd9e14`.
Guard receipt `manual-link-packet/guard4.env` SHA-256:
`8a36908ac27012ece4f35c9b4ac116c126a6ee8e58faf68537b59a8b61775d85`.
