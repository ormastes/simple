# C4 scope reader runtime qualification — 2026-10-25

The additive reader implements the actual backend's dictionary slot order. It
does not admit full SOURCE storage accounting or reserve historical allocations.
The shared account and HIR construction lane remain separate prerequisites.

## Native C boundary: executed

`src/runtime/test/rt_dict_scope_read_selfcheck.c` includes the real native owner
and links `runtime.c`. Its allocator wrappers count real malloc/calloc/realloc
calls; one real header is retained/reissued to force address reuse through the
normal dictionary constructor. This is allocator fault injection, not a forged
owner or substituted dictionary implementation.

Command (from the owned checkout):

```sh
cc -std=gnu11 -O1 -w -ffunction-sections -fdata-sections -Isrc/runtime -Isrc/runtime/platform src/runtime/test/rt_dict_scope_read_selfcheck.c src/runtime/runtime.c -Wl,--gc-sections,--allow-multiple-definition -Wl,--wrap=malloc,--wrap=calloc,--wrap=realloc,--wrap=free -lm -lpthread -ldl -o /tmp/c4-native-scope-read-selfcheck
/usr/bin/time -f 'isolated_reader_process maxrss_kib=%M elapsed_seconds=%e' /tmp/c4-native-scope-read-selfcheck
```

Observed: 2,049 live bindings; 300,000 scalar reads; zero allocator calls during
reads; 0.012664 seconds; isolated reader maximum RSS 1,616 KiB; exact address
reuse observed. Earlier direct-wrapper RSS values inherited an unrelated high
water mark and are not reader RSS evidence.

Executed assertions cover empty/rehash/tombstone/clear/reinsert keys order,
replacement, UTF-8 bytes, wide signed integer ID, invalid key/value types,
forged/freed/reused owner, stale epoch, backing revision, epoch exhaustion,
zero/exact/one-under fuel, nonblocking lock refusal and ordinary behavior after
reader exhaustion. The bound is at most 193 units: three membership walks of
at most 64 probes plus one scalar payload operation. It is not a machine
instruction count. Collision exhaustion is an unavailable read, never empty.

## Pure Simple and typed facade: incomplete execution evidence

Exact diagnostic producer:
`/tmp/phase3-stage3fix-1690/canonical-admission/stage2/aarch64-unknown-linux-gnu/simple`,
SHA-256 `7934d8c2e119a56098c49c0d996c52070eb962e156ce3855a723d29824cbf550`.
This is focused Stage 2 evidence, not Stage 4 or release qualification.

The array, numeric and memory modules compiled to objects. The full string
module failed HIR with two fatal diagnostics; the unchanged HEAD string module
reproduced the same two failures. Fatal text remained absent even with
`SIMPLE_DUMP_COMPILE_ERRORS=1`. Logs are retained under
`/tmp/c4-scope-read-pure-20261025/` and
`/tmp/c4-scope-read-pure-baseline-20261025/core_string-inscope.log`.

The two-module typed facade/account closure passed HIR, then the selected
producer's MIR worker crashed with signal 11, exit 117. The immediately prior
diagnostics report imported `MirLoopResourceLimitsV1` and
`MirLoopResourceSnapshotV1` changing from empty to complete field lists. No
artifact was published. This is a concrete compiler crash, not a passing test.

The direct fixture `test/fixtures/compiler/dict_scope_read_probe.spl` remains
unexecuted here. It checks original-account charges across two/copy views,
close/stale rejection and exact/one-under budgets. No shared-account aliasing,
typed extern ABI, or pure runtime execution PASS is claimed without execution.

Pure compact dictionaries retain their remove-swap order. Their header allocator,
descriptor and promotion-byte accounting use one `dict_header_bytes_v1` owner
(64 bytes). Pure validation costs the dictionary linked-registry length plus
the bounded string and numeric registry capacities. This is a concrete
performance deficit for large live heaps under the frozen work limit; repeat
owner lookup needs a bounded generational index before broad pure SOURCE
qualification. No alternate insertion-order mirror is introduced.

The selected hosted archive owns Rust `rt_dict_new/keys/set`, verified with
`nm -A`; C and pure core layouts cannot certify that provider. Its counterpart
and actual SOURCE acceptance belong to the separately reviewed Rust/HIR lanes.
