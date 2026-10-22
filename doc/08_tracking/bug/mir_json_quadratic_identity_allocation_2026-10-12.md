# Quadratic MIR JSON identity allocation

Status: **OPEN; source candidate, native qualification blocked**. This patch is not an admitted compiler repair. No aggregate runner retry is authorized by the measurements below.

## Confirmed failure

Actual self-hosted producer SHA256 `d3563806c3babfe69358380aa752a0b90b65f7119a7b83cb441a97a969ca9791` already contains the empty-transient and bounded-file-read runtime fixes. Its compiler source is b58baa89e4d65a40768fceaf8221fdbdbe58da24. A separate two-file fixture with a single1024-statement arithmetic function reached3GiB before producing an object. GDB at2GiB captured:

```
libc copy -> rt_string_concat -> serialize_mir_function
-> native_capsule_mir_identity_v1 -> FrozenNativeModuleCapsuleV1.identity_valid
-> driver_native_capsule_inputs_valid_v1 -> _compile_frozen_module_capsule
-> ParallelBuilder.build
```

The original218-module test-owner attempt stopped at its12GiB cap with no object, HIR/MIR218PASS and native_compile54/218. Its75existing cached objects were unchanged. Its log stops before the unconditional backend-dispatch notice; source places witness/capsule preparation there. The small fixture proves an allocation defect on this shared identity path, not that this is the only cause of the original OOM. Phase2 tests executed0.

## Before-repair scaling evidence

All rows use the same patched producer, real native compilation, private Git-admitted source/caches,90s/3GiB guard and actual native-worker GDB counters. Tracing adds overhead; elapsed times are diagnostic observations, not production latency promises.

| Fixture | Compile | Peak process-tree KiB | Executable sanity |
|---|---|---:|---|
|128 separate tiny functions +main|0;9.931s;22000B object|88,512|paired strict link0/run0;151 result assertion and exactstdout PASS|
|One512-statement function +main|0;10.327s;1352B object|1,247,012|paired strict link0/run0;529 result assertion and exactstdout PASS|
|One1024-statement function +main|-9;11.342s;3GiB guard;noobject|3,191,212|UNEXECUTED|

The512-statement module's seven large identity calculations each increased worker RSS by151–171MiB and took.048–.099s. The first three1024-statement calculations each increased RSS by644–661MiB and took.303–.336s. Twice the body size incurred approximately four times the allocated/retained bytes. At those boundaries raw-transient live count was0, capacity1048576; heap registry count increased about59628 per1024-statement identity call. Those are actual counters, not a claim that all retained objects are unreachable.

The1024 source revision is c9ed36cadc57f1792fb746b08c84fafd2adff63b;512 is93c628b057ceb807f6cfc1b4e0aed09641104d77;128 is589e36d996a363ef2d091224bbcc66ea41612160. Three diagnostics completed; no fourth run.

## Narrow source candidate

`serialize_mir_function` repeatedly copied the growing JSON prefix for locals and blocks; `serialize_mir_block` did so for instructions. Each iteration allocated a longer string. The patch collects serialized fragments and joins with the same comma separators once per collection. Constant-count header/trailer concatenations remain. JSON order, labels, escaping, empty arrays, leaf serializers and metadata handling are unchanged; cache format/hash/validation are not relaxed.

Actual runtime `rt_string_join` first sums byte lengths, allocates once, then copies each fragment/separator. Native LLVM runtime-array lowering instead selects `rt_array_join_any`, which also uses one allocation and two passes but has the separate NUL defect below. Neither repeatedly concatenates prefixes. Existing MIR escaping/constant-container serialization already uses this pattern. The change adds no free, scope reset, object mutation, cache admission, or ownership transfer. Per-instruction/other leaf serializers can contain additional quadratic cases; those are untouched. This repair targets only the demonstrated function/block prefix growth.

The measured hotspot bodies are identical in producerb58 and source54a1397eb. The entire baseline mir_json.spl is identical between frozen523ce4c9 and product base020e419f5bedbd83449bafd04d98e89fd9a8bb27. Thus the change is relevant to both source revisions without importing unrelated ancestry.

## Real authored regression and attempted execution

`test/05_perf/compiler/mir_json_linear/main.spl` imports the production serializer and actual MIR owners. Two frozen baseline function bodies from020e provide a byte-for-byte oracle; there are no replacement MIR structs or fake serializers. The fixture constructs real locals/instructions/blocks, including constants, copies, binary operations, calls, branches, metadata, empty blocks, non-ASCII, interiorNUL and multiline/quoted strings. Independent shape/golden assertions reject empty/default-result parity. Failure returns nonzero. Candidate/baseline modes write exact byte outputs separately; small/512/1024 sizes are intended for independent process measurements.

Two bounded direct native builds were attempted with the actual producer (6GiB/180s caps, jobs1):

| Dependency owners | Result | Peak tree KiB |
|---|---|---:|
|Current020e plus candidate (source6733c5c3024ec8ab41582871cc342523247bfb92)|exit1/94.171s,100modules,noobject|2,277,152|
|Frozen523 plus exact same candidate/fixture (source63f63afe0b46787d5ebf2692896c5438d1997378)|exit1/87.143s,100modules,noobject|2,280,968|

Both failed existing producer MIR lowering contracts: imported Option enum payload types; record patterns such as MirBlock inferred as I64/non-array; SymbolId treated as an enum; existing Dict.keys().sorted unsupported. The newer dependency closure also reported untouched hir_symbol_table_methods `raw` resolution. Full diagnostics are preserved. The final fixture additionally aligns string constant/local types with canonical pointer-to-I8 text representation; this authored adjustment is UNEXECUTED. Repeating the same source closure would not establish parity, so no third unchanged attempt was made.

Native baseline/candidate JSON parity, derived cache identity equality, after-patch latency/RSS, and prevention bounds are **UNEXECUTED**. Authored tests are not PASS. No Rust seed test fallback, mocked records, symbol renaming, duplicate-provider suppression or C-model substitution was used. Source inspection alone does not qualify this patch.

## Separate native join dependency found during logic review

An actual C probe linked against the same07a41f runtime and935f backfill constructs a tagged string containing bytes `61 00 62`. `rt_string_join([that,"cd"],",")` returns six bytes `61 00 62 2c 63 64`; native `rt_array_join_any` returns only four bytes `61 2c 63 64`. Link/run exit0 asserts both observations. This confirms a separate existing length-contract defect in the native join owner, not candidate serializer execution.

`escape_json_string` currently escapes quote, backslash, LF, CR and TAB, but forwards other control characters including NUL as ordinary fragments before its existing join. Thus the native route can already lose NUL before the newly added outer joins. A new serializer regression is not claimed solely from `strlen`. Conversely, the counted join preserves raw NUL, which is not valid JSON escaping; that existing escaping defect also needs separate tracking. Native byte parity remains blocked until the actual route is qualified. No runtime or escaping change is included here.

Source review found no P0/P1 in collection order/comma/empty-array behavior or ownership. That review does not establish native NUL parity. The real contract probe and receipt are `join-nul-probe.c` and `join-nul-receipt.json` in the qualification directory.

## Next qualification contract

Use a compatible admitted native producer to compile the real regression. Run compare mode once for small and512; run baseline/candidate separately for512 and1024. Assert exact output bytes and hashes, independent golden shape/escaping, and output-length/work bounds. Record elapsed time and peak/after-operation RSS; establish a broad measured bound that fails quadratic regression. Confirm retained arrays/strings follow the same runtime owner contracts. Then build a legitimate affected compiler module/provider and qualify a new producer with real Hello before considering the previously capped runner lane. Old cached Rust-mangled providers and new dotted LLVM providers have not been shown ABI-compatible; do not rename them to force a link.

All full compiler/core/lib checks, MCP/LSP smokes, whole suites and native Windows/macOS/BSD/SimpleOS execution remain UNEXECUTED for this source candidate. This is an unfinished draft, not release admission.

## Evidence locations

`/mnt/c/Temp/simple-native-codegen-allocation-diagnosis-20261012/`: exact producer commands, private Git fixtures, GDB stack/counters, RSS samples, paired native sanity receipts, source-owner hash comparison and causal-report.md.

`/mnt/c/Temp/simple-mir-json-linear-qualification-20261012/`: per-attempt command/log/receipt/errors, frozen-source-binding.json and candidate source binding. Original runner: `/mnt/c/Temp/simple-manual-lanes-20261011/p2-runner-bounded-read-final/`.
