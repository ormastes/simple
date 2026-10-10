# Native HIR cache warning cursor rejects stable v8 frames

Status: **FAIL; cache qualification and Phase 3 incomplete.** The three allowed
changed-source construction cycles are exhausted. No fourth construction,
warm build, RISC-V probe or full Phase 3 retry was performed after this failure.

## Exact final candidate and bounded result

- Frozen integrated source: `cceddeb91c43645e5f70f5cc76ad61daa02562b3`.
- Pure-Simple producer: `/home/yoon/dev/simple-bootstrap-next-20261011/build/native_probe/hir-cache-owned-miss/simple`.
- Producer SHA256: `44a540d538241e202e2dc00440591c4fd9567474706c310f3c75367638325134`.
- Root construction: exit 0, three compiled, 1221 naturally cached, zero failed,
  19.0 seconds. This is construction evidence, not Phase 3 completion.
- Fixture: `test/fixtures/hir_codec_integer_three/main.spl`, SHA256
  `4bc61aa945783d48944d64e8d7f1728e3480b139b4641e5c798b6b34ccb7c949`.
- Actual source admission used immutable SCV
  `961b45080972e2cd5d76668fe112cc03ce111bcdeb6e24bc315cdec17999b6e2`.
- One CPU, one requested thread, 120-second external limit; compiler exit 0,
  elapsed 69.43 seconds, maximum RSS 2171392 KiB. Source HEAD, executable and
  fixture identities remained unchanged. No comparative speedup is claimed.
- Existing output executed once: exit 0, exact stdout `count=3\n`.

The ordinary `native-build` route still schedules one isolated HIR shard with
`--threads 1`. The log therefore contains two genuine worker sequences, not
duplicate output replay. Both report `HIRROUNDTRIP ok=true stable=true`, 3790
bytes, proving the corrected integer writer and dictionary ordering on this
fixture. The shard reports `CACHE_STORED` and PASS, but the final worker again
reports HIR work=1, hits=0, misses=1, stores=1. This is a remaining cache reuse
failure despite stable codec bytes and a correct executable.

The initial evidence harness expected one receipt and consequently marked the
run FAIL before executing the artifact. Read-only log classification established
the actual two-worker failure; the corrected receipt retains FAIL. No compiler
command was repeated to repair the harness assumption.

## Durable evidence

All paths below are relative to
`/home/yoon/dev/simple-final-frontend-cache-replay-20261011/build/native_probe/hir-v8-qualification/phase3/44a540d538241e202e2dc00440591c4fd9567474706c310f3c75367638325134/cceddeb91c43645e5f70f5cc76ad61daa02562b3/integer-three/`:

- `cold/receipt.json`, `cold/build.log`, `cold/time.txt`, `cold/program`.
- `cold/offline-loader.gdb`, `cold/offline-loader.log`.
- `cold/offline-cursor.gdb`, `cold/offline-cursor.log`.
- `hir/queue-1610746-0/599e4d1fb174d07e57c30cd2d6ac82179ea99e94f074d33dcd3c22c3438d94d9.terminal`.
- `hir/9823014693c5890e7ad5b177045cb660226734ce890ab91a66b886e35a14c90e.hir`.

The queue's stored key exactly matches the single retained `.hir` filename.
The retained header includes v8 and the exact producer SHA above. It is not a
missing-key result. The shard's original header was overwritten, so equality
of its header with the final header was not independently captured.

## Native first-rejection evidence

Offline GDB launched this exact producer with `--help`, stopped at `spl_main`,
and called its existing native loader on the retained entry. The isolated
inferior received the retained header's exact frontend scope and private cache
directory; no production process environment or file was changed. This is a
diagnostic function call, not an actual warm-build qualification or a forced
cache hit. No return values or executable instructions were patched.

The loader passes header validation, then rejects the warning marker before
entering the strict HIR decoder. Scratch scope begin/end before the call and
again after it each return 1. Thus this deterministic rejection does not depend
on nesting a second scratch scope; a separate outer-scope issue is not ruled
out merely by this isolated call.

The retained file has header newline at byte 286, warning marker `W` at byte
287 and marker newline at byte 288. Native breakpoints establish:

| Operation | Actual arguments/result | Required meaning |
|---|---|---|
| `rt_text_find(raw, newline, start)` | start register x2 = 2296 | raw byte offset 287 |
| search result | x0 = 2393 | next marker newline 288 |
| `rt_slice(raw, start, end, ...)` | start=2296, end=2393 | matching index representation |
| decoded slice range | bytes 287 through 299 | just `W` |

2296 is the tagged integer encoding `287 << 3`. The two-argument text-search
runtime expects a raw i64 offset, so it searches from byte 2296 and correctly
returns raw byte position 2393. The generic slice path subsequently interprets
2393 as a tagged integer (299), producing `W\n0\nspl-hirc`. The comparison with
`W` fails at native address `0x119dcf8`, and load returns nil (native value 3).
The HIR codec is never entered on this path.

Relevant pure-Simple lowering is
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, the
two-argument `index_of` / `find` / `find_str` arm around line 2886. It documents
the raw i64 ABI but directly forwards the lowered start local and returns the
raw result. The inferred cache cursor uses erased tagged locals in the observed
producer. The runtime's raw-offset contract is also explicit in
`src/compiler_rust/runtime/src/value/collections.rs:4127` and
`src/runtime/runtime_native.c:4758`; no runtime implementation was modified.

Next scoped work should repair the pure-Simple raw/tagged boundary for valid
text offset searches and add typed plus inferred-cursor tests, including zero,
three, missing delimiters and nonzero offsets. Do not bypass warning parsing,
ignore identity checks, force cache hits or replace the call silently with an
unrecorded workaround. A future authorized session must qualify that repair
and then prove actual cross-worker reuse before retrying Phase 3.

## Separately scoped envelope parser repair (source only)

The fresh branch based on `a841af5f063a043cdabef9e70bc5defeeb68bf9f` retains
this seed-generated machine-code defect as evidence. The adjacent Pure-Simple
MIR offset repair does not retroactively change the observed producer.
`doc/05_design/hir_cache_envelope_reader.md` establishes the line-protocol
contract and byte-preservation proof before implementation. The cache envelope
now uses the shared canonical `FlatPoolReader`, validates split/join identity,
and reconstructs the exact remaining body fields. It does not normalize bytes,
bypass warning validation, change cache authority or relax strict HIR admission.

Parser regressions and the actual native loader regression cover warning count
three, escaped/Unicode warnings, malformed envelopes, stale and unstable entries,
retained warnings and subsequent scratch scope reuse. They are authored, not
executed. The source-contract test's outdated existence-only `has` and raw-env
expectations are also aligned with the already established scoped validation and
environment facade. No constructor or native build was run for this source-only
task; the prior three-cycle serialization failure remains terminal.
