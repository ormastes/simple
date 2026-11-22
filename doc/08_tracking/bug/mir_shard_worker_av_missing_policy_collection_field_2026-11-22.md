# MIR shard worker dies 0xC0000005 before claiming: `policy.collection` names a field that does not exist

- **ID:** mir_shard_worker_av_missing_policy_collection_field_2026-11-22
- **Priority:** P1 (Phase 2 to Phase 3: every capsule MIR shard worker with `--entry-closure` dies)
- **Status:** fix-implemented-verification-pending (source fix in `src/app/cli/native_build_main.spl`;
  it takes effect only in the next compiler generation)
- **Host:** Windows 11, x86_64-pc-windows-msvc. The Stage 2 compiler is built from release/1.0.0 @ a20233fd230

## Symptom
In the Stage 3 two-pass capsule route (`[stage3-route] HIR warm-up + MIR shard pool`), the first MIR
shard worker dies at once with `status=CRASH exit=-1073741819 claimed=-1 ... ntstatus=0xC0000005`.
It prints nothing and writes no ledger inventory, and the pool stops with `died before claiming any module`.
This reproduced on compiler_cli_build (4102 files), test_runner_build (412 files) and the Stage 3 closure.

## Minimal repro (1 file)
A git-committed fixture `src/app/fx/main.spl` (`fn main() -> i64: print "hi"; 0`), with
`SIMPLE_BOOTSTRAP_STAGE3=1 SIMPLE_MIR_SHARDING=1 SIMPLE_FILE_WORKERS=0` and LLVM 23 first on PATH:
`simple.exe native-build --entry src/app/fx/main.spl --source src/app/fx --mode dynload --entry-closure -o out.exe`.
The worker crashes. **Without `--entry-closure` the same fixture passes**, with workers claiming and sealing.

## Root cause
Only shard children run `native_build_capsule_admit_preclosed_v1` with a published closure request.
The coordinator only publishes the request. That function called (cc595ec5935, 2026-11-22):

```
native_entry_closure_handoff_install_capsule_v1(admitted, policy.collection, library_policy)
```

`policy` is an `EnvironmentVariantPolicyPreparedHandoffV1`, which has only `handoff` and
`encoded_payload`. The collection is `policy.handoff.collection`. The Stage 2 compiler accepted the
missing field and lowered it as an out-of-range slot read. Under cdb the worker faults in the install
function, which is identified by its writes to the three adjacent handoff globals:
`simple+0x1096ba6  mov rbp,[rax]  rax=0x0000077400000000`. That is the bogus tagged
`policy_inputs` pointer of the garbage 4-field "collection" being deep-copied into
`_g_native_entry_closure_policy_collection`.

## Fix
`policy.handoff.collection`, the same form as `native_build_worker_entry.spl:33` and
`parse_shard_main.spl:157`.

## Follow-up: compiler accepted the missing field (fix implemented, verification pending)
`policy` is bound by `val policy = match ...: case Ok(value): value`, so HIR has no type for it.
The HIR accessor-forwarding check (`lower_accessor_read`) needs an owner, so it never ran. The
MIR module-qualified layout tier, which already rejects a missing field, needs a HIR type
symbol, so it never ran either. `resolve_field_index`
(`src/compiler/50.mir/_MirLowering/function_lowering.spl`) found the bare value-provenance layout
and saw that it lacked `collection`. It fell through and returned the default index 0, the
`handoff` record. That is why the deep copy read a 4-field "collection" out of a handoff.

Fix: when the bare value-provenance layout is unambiguous (not conflict-warned) and lacks the
field, and no later tier resolves it, lowering now fails with
`no field '<f>' on '<Owner>' (receiver type from value provenance)`. Successful lookups are
unchanged: any tier that finds the field still returns its index first.

The HIR `SIMPLE_STRICT_FIELD_FORWARDING` default was deliberately left alone. For a typed receiver,
MIR's qualified tier already fails closed. Flipping the HIR default needs the cross-module census
that `strict_field_forwarding_opt_in_workaround_2026-10-27.md` still lacks.

Specs (`test/01_unit/compiler/50.mir/missing_struct_field_lowering_spec.spl`, describe
"missing field on an untyped match-bound receiver"):
- reproduction: `policy.collection` on a match-bound `Prepared`;
- generalization: the same read through an `if val` binding;
- control: `policy.handoff.collection` still lowers.

They run only on a compiler deployed after this change.

Unverified assumption: the guard arms only when `struct_value_syms` holds the receiver's owner.
Value provenance for an untyped match result comes from `remember_merged_arm_identity`
(`mir_lowering_stmts.spl` match lowering), and nothing here checks that it is populated for this
shape. If the reproduction case stays RED, the remaining gap is missing provenance for the
match-arm binding. That gap must be fixed. The assertion must not be weakened.

## Verification pending
Phase 3 rebuild, then the 1-file `--entry-closure` repro above must seal both owners.
