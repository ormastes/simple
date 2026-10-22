# HIR integer dictionaries lose value 3 during native decoding

Status: causal failure captured; reviewed source fix integrated locally; patched native runtime qualification remains blocked. Phase3 and the nine retained application targets are not qualified.

## Same-call evidence

The explicitly authorized observational run used unchanged admitted compiler `d85dd53b7a1d5a3438d06c9856a3b252c02122f784411a9d9c330b2877dab708`. GDB captured the actual original/reencoded validation frames immediately after encoding and before their normal comparison. It read bounded memory only; validation continued and failed normally. Source/runtime authority checks passed, and all guarded processes became quiescent with clean cgroup removal. The existing102 frontend cache entries were retained unchanged.

Evidence root: `/home/yoon/dev/simple-feature-caps-probe-packet-20261019/diagnostic-gdb1`. Terminal assessment SHA256: `68e9a40976ec55673b5c09e9e4750eaf5a007c021456c8891d72e751d1233167`. The frame identifies `src/lib/string_core.spl` as both module name and path.

Original92341bytes SHA256 `628081062b17734f223594ee87b94ea109510a541a7b72b44170358efb820720`; reencoded92230bytes SHA256 `076d150b608e579a44369d969a29f9e79d4305d72e87017369f412da9f631884`.

| Dictionary | Count before/after | Removed key | Removed value |
|---|---|---|---|
| Scope[0].symbols |308/307 |text_to_upper_ascii |3 |
| SymbolTable.exact_symbols |307/306 |text_to_upper_ascii |3 |
| SymbolTable.module_callables |344/343 |lib.common.string_core#text_to_upper_ascii |3 |
| SymbolTable.root_scope_symbols |308/307 |text_to_upper_ascii |3 |

Applying exactly those four count decrements and four key/value removals reproduces the entire reencoded frame byte-for-byte, accounting for all111 lost bytes. This is not merely a count-pattern inference. It does not explain the separate19 SIGSEGV worker exits.

## Fix and acceptance trace

`src/app/compiler_schema/codec_gen.spl` specializes nonoptional integer dictionary values. It reads an explicitly typed integer, checks the consumed wire token against its canonical representation, and inserts the scalar directly. The seven corresponding generated decoders in `src/compiler/20.hir/generated/hir_codec.spl` are updated. Required-node presence guards, other dictionary value types, cache self-checks and post-HIR validation remain enabled.

The native fixture is `test/fixtures/compiler/codec_scalar_map_roundtrip/main.spl`, SHA256 `a3a6c1e68d87cac67951ef1271e72e51cbc4838df1010c1fc3ce87b68864b5a3`. It exercises actual generated codec exports, not a test mirror.

| Existing invariant | Implementation | Executable check | Current evidence |
|---|---|---|---|
| Preserve every signed scalar/key in all seven maps |Typed integer dictionary decode |check_scalar_map, check_scope_roundtrip, check_table_roundtrip |Static reviewed; runtime UNRUN |
| Preserve exact encoded bytes |Generated encode/decode paths |Frame completion and byte-identical reencoding assertions |Static reviewed; runtime UNRUN |
| Reject absent/noncanonical/truncated scalar wire |Reader validity and exact-token guard |check_absent_and_malformed_wire with canonical and legacy readers |Static reviewed; runtime UNRUN |
| Leave unrelated node/cache validation intact |Unchanged required-node branches and validation gates |Source diff review; existing controls remain required |Static reviewed; no new runtime claim |

## Qualification blocker and next handoff

Isolated source commits `bdb86842f41` (production patch) and `efa9a7ada70f81ff63d80bfa0c473d9ca59e7e79` (fixture) were independently reviewed. The same source changes and fixture are now integrated in the owned working branch. No new compiler binary is deployed or admitted.

The fixture build under old d85 failed with `RT-E-HIR-BLOB-NONCANONICAL` before a binary was produced; none of its runtime assertions executed. A compatible genuine bootstrap authority must build/admit the corrected producer before compiler-path roundtrip qualification. Do not weaken the gate, relabel old receipts, substitute a mirrored Python test for native execution, or claim the19 crashes/nine targets are fixed. Preserve all existing source snapshots, caches and failure evidence. Further execution needs a separately authorized bounded cycle.

## Canonical repaired-producer bootstrap outcome

The later single authorized canonical Rust bootstrap used the unchanged isolated source `efa9a7ada70f81ff63d80bfa0c473d9ca59e7e79`, LLVM23.1.2, private storage and one build job. Packet: `/home/yoon/dev/simple-codec-repaired-bootstrap-packet-20261019`. Session14746 is terminal, exit89: `rss-measurement-failed`. The Rust seed completed in5m24s; native-all construction remained incomplete. No Stage2 compiler, admission, runtime capsule or verification matrix was produced.

The outer receipt records one55,685.509ms observation against a1,000ms observation budget, with measurement incomplete. The accepted peak3,270,416KiB was below the16,777,216KiB cap, but cannot establish RSS during the observation gap. Outer quiescence, helper integrity and empty/error-free cgroup cleanup are confirmed. The inner receipt is absent and must not be represented as complete. All45 frozen input pins still match; Cargo artifacts are retained.

Terminal assessment SHA256: `b3bd1341b85ed7d1307bbd19c8aa76ebb40c498c5d37b718fec9cd34d15e4209`. Astra's read-only diagnosis `/tmp/astra-watchdog-observation-20261019.md` establishes no causal watchdog defect: scheduling, I/O and observation work remain indistinguishable. Failure-phase telemetry is the next isolated diagnostic change; enforcement and validation remain unchanged. This is not evidence that the scalar fix ran. No automatic bootstrap retry.
