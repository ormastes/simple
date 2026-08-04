# The wine_vm module family was destroyed by tree wipes and partly rebuilt by guess

- **Date:** 2026-08-04
- **Status:** partially repaired (see *What is fixed* / *What is left*)
- **Origin tip reproduced:** `f4cd63de2283f6b4bd990f3be1b08ed0eb2e37e5`
- **Evidence binary:** Rust bootstrap seed (`bin/simple`, v1.0.0-beta), `SIMPLE_EXECUTION_MODE=interpret`

## Summary

`src/lib/common/wine_vm_adapter.spl` at origin tip was an 89-line stub whose API
matched none of its 141 consumers. The real 322-line module had been lost in one
of the repo's tree-wipe events; commit `3734fb4a868` (2026-06-30) then re-grew a
stub from a 15-line remnant by **guessing** the API rather than restoring it.

Five sibling modules in the same family were destroyed in the same way and never
restored at all:

| module | origin-tip state | last intact size |
|--------|------------------|------------------|
| `wine_vm_adapter.spl` | 89-line guessed stub | 322 lines (`797bf03d016`) |
| `wine_vm_gate.spl` | **absent** | 64 lines |
| `wine_process_session.spl` | 80-line stub, 5 fns | 1,412 lines / 98,624 B |
| `wine_substrate.spl` | **absent** | 14,722 B |
| `wine_seh_frame.spl` | **absent** | 3,526 B |
| `wine_precondition_manifest.spl` | **absent** | 3,609 B |
| `wine_process_entrypoint_startup_fault.spl` | **absent** | 8,460 B |

## The arity census false positive

A repo-wide call-site arity census flagged `wine_vm_commit` as the largest
confirmed defect cluster: declared with 4 parameters, called with 3 at ~96 sites
(the true count is **109**), which was read as the protection string landing in
the `size` slot.

**The finding is inverted.** The real signature is and always was three
parameters:

```
pub fn wine_vm_commit(space: WineVmSpace, base: i64, perms: text) -> WineVmOpResult
```

Every one of the 109 call sites is correct. The 4-parameter
`(space, address, size, protection)` declaration was invented by the stub, and
its body ignored all four arguments. The census compared call sites against a
declaration that was itself the defect.

This is a generalisable trap: **a call-site arity census assumes the declaration
is ground truth.** When a module has been reconstructed by guess, the declaration
is the least trustworthy thing in the file, and the call sites — which survive in
numbers and were written against the real API — are the better evidence. A
cluster where *every* call site disagrees with the declaration in the *same* way
should be read as evidence against the declaration, not against the callers.

## By-value proof of the mis-binding

Against the 3-parameter declaration, a `0x1000` reservation at `0x500000`:

```
reserved.region.base   = 5242880
reserved.region.size   = 4096
committed.region.base  = 5242880
committed.region.size  = 4096
committed.region.perms = rw
```

The protection string lands in `perms`, and `size` keeps the reserved extent.

Against the 4-parameter stub, the same three arguments bind `"rw"` into the
`size: i64` slot and leave `protection` unfilled:

- interpreter: `semantic: function expects argument for parameter 'protection', but none was provided`
- JIT: the call is silently dropped and the process **exits 0**

The JIT half is the dangerous one and matches the known nil-sentinel behaviour:
no diagnostic, no non-zero exit, no output.

## Reproduction

The family is the 62 specs under `test/01_unit/lib/common/` and
`test/03_system/app/simpleos/feature/` that import `common.wine_vm_adapter`.

At origin tip:

| | specs | examples | failures | passing |
|---|---|---|---|---|
| before | 62 (5 with no verdict at all) | 212 | 187 | 25 |
| after  | 62 (0 with no verdict)       | 232 |  82 | 150 |

`test/01_unit/lib/common/wine_vm_adapter_spec.spl` went from
`11 examples, 11 failures` to `11 examples, 0 failures`.

### Correction to an earlier claim in this repair

The first landed commit of this repair (`10cc1e3c37e`) states that before the fix
"all 62 wine_vm-family specs produced no verdict line at all; they died in
semantic analysis". **That is wrong**, and the error was a harness artifact of
this investigation: the verdict was grepped as `^Results:`, which the `simple run`
path never emits. 57 of the 62 specs did produce a verdict line; they reported
every example as a failure. The corrected numbers are the table above. The
technical content of that commit is unaffected — the module really was a guessed
stub, and the restoration really does take the adapter spec from 11 failures to 0
— but the specific "nothing produced a verdict" sentence in its message should be
read as retracted.

Distinct blocking errors at origin tip, counted across the family's logs:

| count | error |
|-------|-------|
| 40 | ``class `WineVmOpResult` has no field named `region` `` |
| 15 | ``function `wine_vm_space_new` not found`` |
| 4  | ``class `WineVmFault` has no field named `thread_id` `` |
| 2  | ``class `WineVmProcessSpace` has no field named `regions` `` |
| 1  | ``function `wine_vm_regions_overlap` not found`` |
| 13 distinct | missing `wine_process_*` functions |
| 3 | `Cannot resolve module:` `wine_seh_frame`, `wine_precondition_manifest`, `wine_process_entrypoint_startup_fault` |

Note the verdict line for `simple run` on a spec is `N examples, M failures` —
**not** `Results:`, which is the `simple test` runner's format. Grepping for
`^Results:` on this path reports a false "nothing ran" for every spec including
green ones.

## What is fixed

The seven modules above were restored from the last commits that carried them
intact. After restoration all 62 specs compile and execute, and 17 are fully
green (was 0). Passing examples went 25 → 150.

## What is left

45 of 62 specs still have genuine assertion failures. These are **not** arity or
resolution problems; they are behavioural mismatches between the restored
historical modules and the current specs, plus further truncated modules in the
same family (e.g. `wine_hello_exe.spl` is missing
`wine_hello_exe_probe_manifest`, `wine_hello_exe_probe_manifest_evidence` and
`wine_hello_exe_probe_vm`). Each needs the same treatment: establish from history
which side is authoritative, restore or fix, and prove by value. That work is not
done here and must not be assumed green.
