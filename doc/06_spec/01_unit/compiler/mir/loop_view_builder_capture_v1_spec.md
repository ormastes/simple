# Actual MirBuilder producer capture v1

Requirement: C4-LOOP-PRODUCER-VIEW-001. All 20 specifications are **UNRUN**. No compiler, runtime, native, allocation or timing acceptance is claimed.

The executable spec invokes actual MirBuilder constructors, shared resource accounts, provider writers and sealing. It reads scalar node identity, exact constant value, block revision, local source symbol/type revision and spans from the provider's sealed view. The constant-empty opted return is checked only as a compatibility representation; publication success comes from the actual owner.

| Case | Concrete control |
|---|---|
| Constructor publication | Real begin/constant/return/end, exact scalar constant and empty sentinel |
| Empty flush | Two actual flushes preserve previous instructions |
| Replacement | Reopened block replaces sequence while retaining stable ID |
| Local edits | Rename and retype preserve scalar source binding and row revision; no removed rich source-symbol field is restored |
| Raw instruction | Unpaired actual emit refuses completion |
| Capacity | Zero instruction category refuses before instruction allocation |
| Raw terminator | Unpaired actual set_terminator refuses completion |
| Placeholder | Unfinished construction-only unreachable cannot seal |
| CFG | Actual new_block/switch/goto retains exact IDs |
| Unsupported mutation | Existing entry allocation fails owner |
| Span | Actual constructor source position retained |
| Ordinary | No optional capture and ordinary rich body retained |

Test helpers begin `lpv1_builder_`. Provider alias/permit/stale writer controls belong to the independent provider spec. Parsed source, signatures, structural type pairing, aggregate positives and namespace policy are parent integration obligations. Additional capture edge and mutation coverage remains necessary before claiming integrated acceptance.

Additive provider-v4 controls cover a real tuple aggregate with an explicit structural cursor and absent non-array kind type, ordered switch arms sharing a target, one correctly paired raw constructor, missing structural cursor refusal, and exact/one-over instruction allowance. The original 12-case tests-first image remains immutable; these five controls are an implementation supplement and remain UNRUN. Signature setup now writes all four actual provider-v3/v4 scalar fields.

The additive length control deliberately sets actual Span.length=99 with start=2/end=9 and requires scalar slot4=99. It is frozen before the grouped Span schema/producer correction; no reconstruction from offsets is accepted. UNRUN.

The terminal-credit control completes the actual builder three times: normal funded empty return, funded emergency return after invalid repeated completion, then nil with unchanged account work/state counters. This checks the existing nullable refusal representation, not physical allocation. The dedicated spec imports BlockId from its defining module and selects instruction limits with ordinary statements.

The current integration keeps the rich local's three short-borrow provenance fields across rename/retype. An additional ordinary-route scenario checks `short_borrow`, `short_mutable` and `short_boundary=83` while verifying the changed name/type and absent capture. This proves preservation only when executed; it does not admit short metadata into the scalar SOURCE route. The historical rich `source_symbol_v1` field is absent; the controlled opted scenario retains its source binding only in the scalar provider. Parsed SOURCE authority and complete metadata/bypass coverage remain open. All 20 scenarios remain UNRUN.
