# HIR v7 decodes but fails native round-trip stability

Status: OPEN; qualification FAIL. This supersedes neither the preserved Phase 3
timeout nor its integer-three encoding diagnosis. No new Phase 3 run occurred.

One parent-authorized changed-source qualification used:

- Source `5ecfff3d23a31e2f7a5b3c3d1be752f14c53f7f1`.
- Pure-Simple producer SHA-256
  `19fcd4ccac312e83cdb4baee72e43398a08b498de98ac9a620c476abc6a49d21`,
  built successfully from 1,223 modules with zero failures.
- Fixture `test/fixtures/hir_codec_integer_three/main.spl`, SHA-256
  `4bc61aa945783d48944d64e8d7f1728e3480b139b4641e5c798b6b34ccb7c949`.
- Cranelift, `core-c-bootstrap`, CPU 0, one thread, 120-second deadline;
  `SIMPLE_BOOTSTRAP=1`, `SIMPLE_NO_STUB_FALLBACK=1`,
  `SIMPLE_HIR_CODEC_ROUNDTRIP=1`, `SIMPLE_M4_WORK_RECEIPT=1`.
- Separate phase/producer/entry-bound HIR, frontend and native cache paths.
  The producer and source fixture remained unchanged during qualification.

The actual compiler reported:

```
HIRROUNDTRIP ok=true stable=false bytes=1879 reason=reencode
[hir-cache] hits=0 misses=1 stores=1
[M4 lower] module=test.fixtures.hir_codec_integer_three.main work=1
```

This is progress from the old producer's `ok=false reason=decode`, but is not a
successful HIR cache qualification. The cause of the changed re-encoded bytes
has not yet been identified. Do not assume it is harmless dictionary order,
discard identity fields, relax byte stability, or force a cache hit.

The native build exited zero in 7.07 seconds with maximum RSS 199,440 KiB.
Its artifact exited zero and printed exactly `count=3`. The self-check returns
the **original** HIR module when re-encoding differs, so that execution does not
prove the decoded HIR preserves executable behavior. The 40.60-second,
342,300-KiB old-producer probe used a different tiny fixture and includes runtime
link work; these are diagnostic observations, not a paired speedup claim.

At the first failed round-trip verdict, warm-cache, RISC-V and broader builds
were not started. The already-running cold command finished within its deadline.
No owned compiler remained afterward. Native unit specs were not run because
there is no qualified test runner. There were no retries or compiler rebuilds.

Evidence is in `/home/yoon/dev/simple-final-frontend-cache-replay-20261011/`
under `build/native_probe/hir-v7-qualification/phase3/`
`19fcd4ccac312e83cdb4baee72e43398a08b498de98ac9a620c476abc6a49d21/`
`integer-three/`: `receipt.json`, `cold.log`, `cold.status`, `cold-run.log`,
`cold-run.status`, the artifact and private cache. The receipt binds exact file
hashes and environment values.

Next authorized investigation must compare the first encoded module against
its decoded/re-encoded form under this exact producer, identify the first
semantic difference and repair its owner. A fresh bounded qualification then
needs stable bytes, actual warm HIR hits with work zero, truthful execution,
and remaining full Phase 3 gates. Current status remains FAIL.

## Exact frame comparison and cycle 2 source correction

An offline GDB diagnostic started the same producer with `--help`, paused at
`spl_main`, and called its native decoder and encoder on the retained frame.
It did not restart frontend compilation or construct another compiler. GDB
allocated input bytes in that isolated inferior and invoked existing functions;
it did not patch instructions or force return values. Both frames contain 1,879
bytes and 569 lines. `original.hirblob`, `reencoded.hirblob`, `frame.diff`,
`offline-reencode.gdb`, `offline-reencode.log` and `symbol-frame-map.json` are
retained beside the qualification receipt.

The only difference is `SymbolTable.symbols`, rows 8 through 171 (zero-based).
Original keys are `[3, 0, 1, 2]`; re-encoded keys are `[2, 3, 0, 1]`. Each complete
record has identical tokens, including its key, SymbolId, type, visibility and
other fields. Prefix and suffix are byte-identical. The record hashes are:

| Key/name | SHA-256 of the complete key/value record |
|---|---|
| 3 / print | `80734cd434717b0645ffae9cedb3b3370277fbaec8f9c28ec33af9d3ae506bde` |
| 0 / main | `bc89b40590ec91ba6c76a91b8b931f680fa129285ef18841602a0d1ae0a61bfa` |
| 1 / main | `df0ee50c47426874b65e01952c5d5d33319187e762226f24bd9018db9aa4cb14` |
| 2 / values | `c8bac4ed5c492314b70c47d065008a998dbb06d823dc98670257d12e5a385e8c` |

The generator's claim that `.keys()` follows insertion order is false on the
native provider: `rt_dict_keys` walks occupied hash buckets. Decoding changes
the dictionary's bucket layout, so the legacy encoder must sort a typed key
snapshot instead of assuming enumeration is stable. This establishes the
cause for this fixture; it does not certify arbitrary modules as lossless.

The cycle 2 source change applies the existing merge-sort helpers to all 30
generated dictionary snapshots: 20 text, seven SymbolId and three i64. The
generator dispatches by that exact key type and fails on an unsupported type.
The generated sites were mechanically updated to that generator-equivalent
form; the actual generator could not be executed because no qualified runner
exists. Generator parity execution remains pending. Live dictionaries and IDs
are unchanged. Integer ordering removes the same invalid `i64 == nil` check as
the integer writer repair; actual nullable text/node ordering remains intact.
Merge passes use separate source and scratch arrays. Legacy codec version v8
rejects old bucket-order records. Canonical availability remains closed.

Production cache publication and admission now require decode/re-encode byte
identity regardless of the diagnostic flag. A failed check refuses publication
before temporary-file creation or returns a cache miss before incrementing hits.
Ordinary cache loading owns a transient decode/re-encode scope and promotes only
the returned module and warnings. Shard transactions call the explicit
already-owned-scope entry point and retain their existing reclamation protocol.
Store validation also runs within its existing owned scope. Ownership failures
remain fatal rather than returning a dangling graph.
Existence probes validate in their own scratch scope without promoting HIR and
restore the previous warning root before reclamation. The current source has
no active `hir_cache_has` call sites; shard loading uses the owned-scope API.

New regressions exercise the real legacy codec, opposite symbol dictionary
insertion orders, preserved ID/tag three, generated optional presence frames,
and a structurally decodable dictionary permutation that strict cache admission
must refuse. The source repair has not yet been compiled or run. Additional
sorting and round-trip checks add work; no performance or memory improvement is
claimed. The parent will coordinate one cycle 2 construction and bounded
qualification before considering a genuine Phase 3 attempt.

### Pre-qualification ownership review correction

Review of cycle 2 source found that normal cache loading unconditionally
promoted its optional result. The native promotion API rejects a nil root, so
a missing, stale or unstable entry would panic after closing its scope instead
of returning a miss. Cycle 2 construction is not qualification evidence.
Promotion is now conditional on a present decoded result; it retains the
optional wrapper together with the module graph and new warnings. Misses leave
the previous persistent warnings untouched. Scope closure remains unconditional.
`hir_cache_has` never promotes the discarded graph and restores prior warnings.

The native-only regression now calls actual store/load/has functions, retains
a successful optional result across missing/stale/unstable misses, checks old
warnings and successfully begins/ends a subsequent scratch scope after each
call. These tests are authored, not executed: no qualified SSpec runner exists.
Root coordinates the third and final changed-source construction; no fourth
cache-feature verification cycle is allowed in this session.
