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

---

# Second repair pass (2026-08-04)

Continues from the state above (232 examples / 82 failures / 150 passing / 45
failing specs). Seven **further** modules in the same wipe cohort were found and
restored. Family after this pass: **232 examples / 26 failures / 206 passing /
26 failing specs**. The example count is 232 in every run, per spec, so no
`describe` block was dropped by a module-load failure at any point.

| | examples | failures | passing | failing specs |
|---|---|---|---|---|
| origin tip (before any repair) | 212 | 187 | 25 | — |
| after first pass | 232 | 82 | 150 | 45 |
| after hello-fixture chain (`e7607df1335`) | 232 | 42 | 190 | 32 |
| after hello_exe + x86_64_decode (`f762ae6ec61`) | 232 | 28 | 204 | 27 |
| after gui_hello (`78af671cba3`) | 232 | 26 | 206 | 26 |

## Further modules destroyed in the same wipe

Authority was established the same way each time, and the test is decisive:
**every symbol the live consumers import is absent from the current file and
present in the last intact version.** No API was guessed.

| module | before | last intact | restored | landed |
|--------|--------|-------------|----------|--------|
| `wine_hello_fixture.spl` | 22-line stub | `797bf03d016` | 167 lines | `e7607df1335` |
| `wine_precondition_fixture_builder.spl` | **absent** | `797bf03d016` | 278 lines | `e7607df1335` |
| `wine_service_adapter.spl` | **absent** | `797bf03d016` | 129 lines | `e7607df1335` |
| `wine_thread_adapter.spl` | **absent** | `797bf03d016` | 120 lines | `e7607df1335` |
| `wine_hello_exe.spl` | 33 lines, 1 of 10 symbols | `797bf03d016` | 204 lines | `f762ae6ec61` |
| `wine_x86_64_decode.spl` | **absent** | `797bf03d016` | 263 lines | `f762ae6ec61` |
| `wine_gui_hello.spl` | 59-line guessed body | `797bf03d016` | 110 lines | `78af671cba3` |

### The 4-byte PE

`wine_known_hello_exe_fixture_bytes()` returned **four bytes**,
`[0x4D,0x5A,0x90,0x00]` — an MZ magic with no PE header behind it. Every gate in
the family that validates the fixture image therefore rejected, which surfaced as
`expected rejected to equal <success-status>` in 40 assertions. By value:

```
              before   after
byte_len         4      1024
b[0],b[1]     77,90    77,90      (MZ)
e_lfanew       n/a       128
PE signature   n/a    80,69,0,0   ("PE\0\0")
```

Sabotage: flipping `data[0x80] = 0x50` to `0x51` reproduces the original message
exactly (`expected rejected to equal cpu-preflight-ready`); restoring returns
green.

### The absent decoder

Restoring `wine_hello_exe` exposed `wine_x86_64_decode.spl` as absent. Over the
restored fixture the decoder now returns a coherent decode where the call
previously raised `function wine_x86_64_hello_decode_plan not found`:

```
decode_ok=true  entry_rva=8192  instruction_count=6  call_count=3
get_std_handle_rva=8288  write_file_rva=8296
instruction_sequence = xor-rcx-rcx call-rip-indirect lea-rdx-rip-rel32
                       call-rip-indirect xor-ecx-ecx call-rip-indirect
```

Sabotage in the implementation (not a shim): changing the recognizer
`if b1 == 0x31 and b2 == 0xc9: return "xor-rcx-rcx"` to a wrong mnemonic drives
`instruction_count` 6 → 0, `call_count` 3 → 0, both IAT RVAs to 0, and the spec
from 0 back to 4 failures.

### A guessed body under a correct name

`wine_gui_hello.spl` kept the right export but its body did
`if not space.ok ...` on a `WineVmSpace`, which has no `ok` field — the same
invent-an-API pathology as the 4-parameter `wine_vm_commit`. The intact body
checks `.ok` only on result objects.

## Two size-based "truncations" that were FALSE POSITIVES

A sweep that ranks modules by current size against their historical maximum
produced two findings that do **not** survive the consumer-symbol test. Recording
them because the heuristic is otherwise the one that found everything above:

- **`wine_nt_api_catalog.spl` (24,047 B vs 62,441 B historical, 38%) is NOT
  truncated.** It was legitimately **split**: `wine_nt_api_kernel32.spl`
  (30,543 B) + `wine_nt_api_ntdll.spl` (15,344 B) +
  `wine_nt_api_user32_gdi32_advapi32.spl` (5,557 B), and the catalog re-exports
  from them. All 27 symbols its 29 consumers import resolve. An initial census
  here reported "25 of 27 missing" — that was **wrong**, an artifact of matching
  only `^(pub )?fn NAME` and therefore missing every re-exported name. Size alone
  cannot distinguish a wipe from a split; only the consumer-symbol test can.
- **`wine_dll_view_tls_dispatch.spl` (4,489 B vs 5,331 B, 84%)** has no missing
  consumer symbol either.

## Still absent, outside this family (live consumers, not restored here)

`wine_proton_gate.spl` (3 consumers), `wine_proton_runtime.spl` (2),
`wine_rtl_string.spl` (1) — all last intact at `797bf03d016`. Tracked separately
by `wine_proton_runtime_modules_missing_2026-07-20.md`.

## What remains red — 26 failures, and why they were NOT made green

Two clusters remain, and both are cases where **no version of the source in the
whole history of `main` has ever produced what the spec asserts.** There is no
authoritative version to restore and the consumers do not determine the shape,
so per the no-guessing rule they are left honestly red.

| failures | assertion | finding |
|---|---|---|
| 24 | `expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")` | The token appears **48 times in `test/` and zero times in `src/`**. `git log -S 'VMWriteReadback' -- src/` over main's entire history returns **no commit**. The source emits `PEBTEBLayoutVMReadback` instead, and other specs in the same family assert *that* spelling and pass. |
| 2 | `expect(result.evidence).to_contain("dll-view-imports-bound")` | The token exists in `src` only as the *status* field of `wine_dll_view_import_binding`, never inside `evidence`. `wine_dll_view_dllmain_handoff.spl` has exactly **one distinct blob in its entire history on main** — it has never composed `bound.status` into evidence, so no historical version could satisfy this spec. |

Renaming either expectation to match the source would make 26 assertions green
without any evidence that the source is what changed. Deciding between "the spec
is aspirational" and "the source lost a feature that predates this repository's
history" needs an authority this repository does not currently contain.

## Measurement note

The family's verdict lines are **ANSI-colour-wrapped**, so `^[0-9]+ examples` does
not match them; every spec reads as "no verdict" unless the escapes are stripped
first. This is a second instance of the same class of harness error as the
`^Results:` mistake recorded above, and it produced an identical false
"nothing ran" for all 62 specs before it was caught.
