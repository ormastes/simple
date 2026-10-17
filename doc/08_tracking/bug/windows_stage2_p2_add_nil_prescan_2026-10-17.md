# Windows Stage2: p2_add reaches prescan with nil function values

Date: 2026-10-17. **Status: observed failure; repair qualification pending.**
Scope: native Windows x86_64, LLVM/core-C bootstrap. No new build or probe was
run while writing this report. No speculative compiler patch is proposed here.

## Failed candidate and admission boundary

The canonical frozen `3636b716294` campaign completed 1352 compilation units
and linked a Stage2 candidate. That proves compilation/linking only: its
`p2_add` sanity build then terminated with Windows `0xC0000005`; the collector
recorded raw status139. The candidate was rejected, not admitted:

- Artifact: `build/bootstrap/smux-astra-campaign/stage2/x86_64-pc-windows-msvc/simple.exe.rejected`.
- SHA-256: `7786a031bef37bab3e572b93c345b7cf49c22950859f59bd6bd116da1d712d87`.
- `stage3/x86_64-pc-windows-msvc/stage2-sanity.env` records `status=fail`, the
  same before/after digest and `frontend_smoke_bootstrap0_raw_status=139`.
- Its frontend status receipt identifies `probe=p2_add-build`. SCV prime,
  MIR retention, module-path naming and positional Hello subprobes are
  `not-run`; the bootstrap1 frontend probe also did not run. None is a pass.

These paths are relative to `D:/dev/simple-smux-upstream-20261017`. The fixture
is `src/compiler/bootstrap_admission/p2_add.spl`; its expected stdout is `5`.
The rejected compiler failed before producing that fixture's binary. This is
not Phase3 qualification or smux feature-test evidence.

## Retained debugger evidence

Under `build/smux-astra-crash-20261017/`, the first debug attempt stopped at
the loader breakpoint, and the second was aborted by the harness's stderr
handling. Neither captured the compiler failure. The third captured the actual
access violation and wrote `p2-add-av.dmp`, a full-memory user dump.
`capture-attempt3.exit.txt` contains debugger exit0: that denotes capture
completion, not compiler success.

`cdb-attempt3.log` and `dump-inspection2.log` retain:

- Exception RVA `0x57e118`, reading address0 at `mov r9,qword ptr [rbp]`,
  with `rbp=0`.
- A unique exact 24-byte object match in `object-matches.json`: object
  `90273d184306d471.o`, symbol
  `MirLowering.prescan_one_function_v1`, function offset `0xc98`.
- The caller's map-values array, untagged address `0x1d62be41cf0`, has length
  and capacity5, data pointer `0x1d62be41d40`, and all five entries equal3
  (the nil tag). The caller index is0: the bad values predate its first
  per-function prescan call.
- `astra-prescan-caller-disassembly.txt` identifies the caller sequence
  `rt_dict_values` → `rt_for_iterable` → indexed `rt_array_get` →
  `prescan_one_function_v1`, establishing the materialized function-map
  values boundary. Short nonunique return-site byte matches are not used as
  unique attribution.

The supported conclusion is that prescan receives an already-invalid function
value. This does **not** identify where those values first became nil, prove
that `rt_dict_values` caused corruption, or establish a particular ownership,
ABI, GC or prescan-body root cause.

## Existing repairs and next qualification

NEXT was rebased onto `79fc28a5e36`; the inspected head was `cbb652b4aac`.
Its ancestry includes existing remote p2_add cycles123–126:
`820a9b89177` (feed trace), `a1ecb8e8161` (context-field transport),
`ab4270c4bcd` (guard-first rebuild reads) and `bf3ce38b521` (identity admission
retains the original feed array). Their presence is source history, not proof
that this rejected binary is repaired. NEXT also has a different prescan
transport shape; do not attribute its current source layout to the old object.

Astra is reviewing the existing repair coverage. A newly built, source-matched
candidate must pass p2_add and the remaining admission probes before Phase3 or
smux qualification can continue. Preserve the rejected executable, producer and
runtime identities, source snapshot, object cache, receipts and dump. Do not
reinterpret link completion, debugger exit0 or unexecuted subprobes as admission.
