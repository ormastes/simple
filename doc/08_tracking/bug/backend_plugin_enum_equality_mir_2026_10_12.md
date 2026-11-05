# Backend plugin enum equality is lowered as a struct operator

Status: reproduced with retained Phase2 producer; private caller workaround qualified. Authoritative bug DB reconciliation pending. Shared workaround commit is pending parent application; no release/buildability claim.

Local application: workaround, durable spec, and this report were committed on `release_phase3` as `12c8aa7fb11b5272b8860094626b2b41a75e30bf`. The shared source SHA-256 is `36a320b39ac96d8878dab711492499cea346ca1a392d7a06b99a7114943ab5e6`, exactly matching the native-tested candidate. Remote landing and producer deployment remain pending; no live cohort was restarted.

The retained f2ce31b4e4dea1ea6ca3e8726cd411144914c24ffcf58722021f38c4b6393dec producer rejects the real backend plugin model at lines75 and85: BackendRole/BackendCapability equality is treated as a struct operator requiring an unavailable __eq__ overload. Actual RED is retained in build/native_probe/phase3-module-batch3-20261012-astra/workers/27/model-49d4fc78-logs/child.log; native exit1, peak58452KiB. Original model SHA256 c0b4570bb44091af9f793a32bacce8d976255b0fb9efe12b58dad14cda9af42d matches current clean shared bytes and C:/p3 snapshot. That passing identity check does not identify the compiler root-cause implementation by itself.

Recovery source Git a2889b42984de7f0cf60e6c25811608e701904cf retains the intended direct enum comparisons. The tagged two-line workaround compares existing canonical name methods. Both enums are finite, payload-free, and their exhaustive name mappings are injective; therefore equality of names is equivalent to equality of these variants. No unknown-identity integer fallback, new enum encoding, reordered fields, weakened validation, or source assertions are introduced. Runtime cost equivalence is unmeasured; this is a buildability workaround, not a performance optimization. Remove it only after direct equality passes the same source-bound criterion with the repaired producer.

Actual private production object SHA256 5f023e255628b6772b7b942cf275b2b3675d42778f602579d5b58fe619b86889 builds without logged errors. A second native object consists of the exact candidate production prefix plus semantic_cases.spl, calling the real membership helpers. The resulting executable SHA256 55cd67078d32c27a38e3cdb482271dcaf476d871137d4b7df2d1c09f5590b390 completes48 conditions: all4 role pairs, all36 capability pairs, empty membership, duplicate/later members, absent capability and three target comparisons. Positive exits0 with SEMANTIC_CHECKS=48 EXPECTED=48; intentional wrong-count control exits1 with SEMANTIC_CHECKS=48 EXPECTED=47. All Jobs close at0. Existing qualified core-C archive is reused; no stub or undefined-symbol suppression is linked.

Durable enum_membership_spec.spl is the equivalent three-example SSpec proposal. Its SSpec runner/import route is UNRUN; the actual native criterion is the evidence above. Receipt.spl remains an independent failing group: role comparisons and Result.err().unwrap() calls should be replaced only with verified equivalent matches, preserving the exact BackendPluginError payload and operation checks. No receipt source is changed here. Full compiler/library checks, full backend contract suite, cross-target behavior, performance, and complete Phase3 build/link remain unqualified.


---

## 2026-11-05 — Second worked-around call site: `ParserProviderV1` admission (in-guest lane, PR #6983+2)

The riscv64 in-guest interpreter kernel (S-mode, freestanding runtime)
reached `parse_and_build_module` and panicked at
`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:1671`:
`parser_provider_v1_admit` returned
`parser_provider_unqualified: parser.simple.legacy-reference` even though
`parser_provider_v1_default()` IS `ParserProviderV1.LegacyReference` —
`provider != ParserProviderV1.LegacyReference` evaluated true for two
equal, independently constructed enum values (tagged-handle identity
compare, this record's exact class).

Caller-scoped workaround, same qualified pattern as model.spl:75
(compare canonical names; no integer-discriminant fallback):

- New helper `parser_provider_v1_same(a, b)` in
  `src/compiler/10.frontend/core/frontend.spl` (after
  `parser_provider_v1_name`, exported): returns
  `parser_provider_v1_name(a) == parser_provider_v1_name(b)`. The name
  mapping is exhaustive over the four payload-free variants and
  injective, so equal names <=> equal variants; text `==` compares by
  content, which the freestanding runtime implements correctly.
- Five `!= ParserProviderV1.LegacyReference` sites replaced with
  `not parser_provider_v1_same(..., ParserProviderV1.LegacyReference)`:
  `frontend.spl:152` (inside `parser_provider_v1_admit` — the panic path
  for genuinely unqualified providers is preserved: non-legacy names
  compare unequal and still return Err) and
  `_FlatAstBridge/module_assembly.spl:1553, 1657, 1672, 1852`
  (post-admission provider gates in the cache, checked-reference,
  scope-owner, and centrally-admitted routes).

Host-side regression (checked-in seed, interpreter mode):
`test/01_unit/compiler/frontend/parser_provider_v1_spec.spl` 8/8 OK and
`flat_ast_parser_provider_route_v1_spec.spl` 4/4 OK.

Kernel evidence: `build-simpleos-riscv64-interpreter-kernel.shs` PASS
(both rows); OpenSBI v1.4 boot (`/tmp/rv-boot/interp-serial-provider-admit.log`)
clears the admission panic — `[interp] lowering hello-world source
through the real frontend` now proceeds into the parse — and stops at the
NEXT blocker, a different class (recorded here for the umbrella's
worked-around-sites list only):

```
[TRAP] S-mode exception, the guest is parking here
[TRAP]   scause=0x0000000000000005 sepc=0x0000000080200976
[TRAP]   stval=0x0000001100000000 sp=0x0000000082e6a8f0
```

scause=5 load fault in `rt_array_set` (header `type` word load) with an
untagged garbage receiver 0x0000001100000000, and sp within ~1 KiB of
the 8 MiB stack top — i.e. unbounded recursion/deep call chain upstream
in the in-guest frontend (same family as the 2026-08-31 "parser made no
forward progress" defect, one milestone deeper). Not an
enum-equality-class defect; NOT fixed in this lane.
