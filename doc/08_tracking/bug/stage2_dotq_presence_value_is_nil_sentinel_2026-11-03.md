# Frozen stage2 lowers a .? presence VALUE as unwrap-or-nil-sentinel (nil mold_path -> has_mold=true -> unwrap panic)

- **ID:** stage2_dotq_presence_value_is_nil_sentinel_2026-11-03
- **Priority:** P1 (phase 3: the stage3 hello build dies in the link step with panic: called .unwrap() on a nil Option)
- **Status:** open. Source workaround landed in src/compiler/70.backend/linker/mold.spl (ind_linker_path).

## Symptom
Stage3 hello build (HIR cache off, MIR/env/promote patches applied) compiles the object, enters phase=link
and the worker exits 1 with panic: called .unwrap() on a nil Option. Exit-time stack (fable_exit shim):
t_panic <- compiler.backend.linker.mold.find_linker_path+0x245.

## Root cause (NEW object aot-fc2181..., stage2 ef0681fc0e1)
link_engine_policy("", false, mold_path.?, lld_path.?) is lowered as

`
if rt_is_some(mold_path): t = rt_unwrap_or_self(mold_path) else: t = 3   ; 3 = RT_NIL sentinel
has_mold = (uint8) t                                                       ; movzbl -> bool param
`

so a nil mold_path (no mold on Windows) arrives as has_mold = 3 (true), the policy answers "mold",
and mold_path.unwrap() panics. if x.?: in statement position lowers through t_is_some correctly;
only the .? used as a VALUE argument is wrong.

## Workaround
al has_mold: bool = mold_path != nil / al has_lld: bool = lld_path != nil passed to the policy.
Link-level interim (not landed): the two movq  sentinel stores patched to $0 in a copy of the object
(s3_fable9.exe).

## Removal condition
A stage2 that lowers .? in value position to a presence bool (rt_is_present / rt_is_some).