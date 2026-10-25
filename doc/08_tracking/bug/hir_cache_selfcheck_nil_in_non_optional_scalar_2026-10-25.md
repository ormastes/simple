# HIR cache codec self-check rejects entries: nil_in_non_optional_scalar

- Date: 2026-10-25
- Status: FIX 2 (first fix insufficient; pending stage-3 rerun confirmation)
- Seen in: ad-hoc Stage 3 (frozen admitted Stage 2 compiling the
  `src/app/cli/bootstrap_main.spl` closure, 1453 modules, Windows
  x86_64-pc-windows-gnu), logs `build/s3-mine/build.log`,
  `build/s3-bis-aeA/build.log`, `build/s3-bis-cmA/build.log` in the
  `wt-rel3-new` worktree.

## Symptom

313 lines like:

```
[hir-cache] SELFCHECK FAILED module=src/compiler/00.common/diagnostics/span.spl ... reason=decode bytes=60349 cause=reader kind=malformed detail=nil_in_non_optional_scalar line=7711/11766 token=N; entry not stored
```

The encoder writes a nil token (`N`) where the generated decoder
(`src/compiler/20.hir/generated/hir_codec.spl:152-164`, scalar readers)
requires a non-optional scalar. The round-trip self-check then refuses to
store the entry, so the shard's HIR work is recomputed / not reusable.
Estimated ~85% of HIR shard work is wasted on this run.

## Likely cause (unverified)

A HIR field declared non-optional in the codec schema carries nil at
encode time under native Stage 2 (uninitialized/defaulted field, or a
schema/type mismatch between the HIR definition and the generated codec).
The failing line index points at the specific field; decode one failing
entry with the reported `line=` to name it.

## Next step

Name the field from `line=` for `span.spl`, then fix either the producer
(never leave it nil) or the schema (make it optional). Do not loosen the
self-check.

## Root cause (2026-10-25, static analysis)

`HirImpl.method_return_is_array` / `method_return_is_optional` are
`Dict<text, bool>`. The generated encoder read them as
`w.put_bool(node.method_return_is_array[dk])`. Under staged-native codegen
the field-projection temp is typed i64, so `lower_dict_runtime_read` resolves
the dict value type as i64 and decodes the bool word with the integer `>>3`
arm (11 -> 1, 0 -> 0). `HirCodecWriter.put_bool` renders `"{v}"` and maps only
`true`/`false`, so `1`/`0` were written as `N`, and the decoder's
`nil_in_non_optional_scalar` guard refused the entry. Every module with an
`impl` that has methods hit it right after the impl's inline `methods` list,
matching the varying `line=` offsets.

## Fix

`src/app/compiler_schema/codec_gen.spl` now emits a typed
`val dmK: Dict<K, bool> = <field>` local for every Dict<_, bool> value read;
the generated `hir_codec.spl` was updated to the same text (2 sites). The
self-check was not loosened. Spec:
`test/01_unit/app/compiler_schema/hir_codec_nil_scalar_reject_spec.spl`
("HIR codec Dict<_, bool> encode"). Not yet confirmed by a native stage
rerun: no runnable pure-Simple binary was available on this host for the
current source (the seed rejects current stdlib).

## Fix 1 insufficient (2026-10-25, later)

Stage 2 built at `d72188e68ec` (contains fix 1, `184d31e1c69`) still logged
313 `SELFCHECK FAILED ... nil_in_non_optional_scalar token=N` in
`wt-rel3-new/build/s3-perfile2/build.log` (hits=239/1495). The typed local
still yields the int-decoded word 1/0, which `put_bool` renders as neither
`true` nor `false` and writes as `N`. Fix 2: the generator branches on the
value (`if dmK[dkK]: w.put_bool(true) else: w.put_bool(false)`), so only
literals reach `put_bool`. The regenerate also picked up a stale-codec gap:
`HirSymbol.generic_param_count` was not encoded at all (a hit silently lost
it); the checked-in `hir_codec.spl` now matches generator output byte for
byte. Self-check not loosened. Unconfirmed until a stage-3 rerun shows
`selfcheck_failed` near 0 (whether these two Dict<_, bool> fields are the
ONLY N source is not proven -- no failing entry is stored to decode).

## Failure-only quarantine diagnostics (2026-10-25, source change pending execution)

The generated required-scalar rejection now appends its owning field to the
existing `nil_in_non_optional_scalar` reason. Enum fields also include the
variant, for example `HirExprKind.IntLit.value`; the decoder still rejects
the same bare `N` token.

When a write-time self-check fails, an operator may set
`SIMPLE_HIR_CACHE_FAILED_DIAGNOSTIC_DIR` to a dedicated evidence directory.
That failure branch alone reads the setting. It writes a payload and an SDN
manifest under `hir-selfcheck-quarantine-v1`; this namespace is never scanned
by the HIR cache loader. The manifest is published last with exclusive,
no-replace file operations. Payload plus reserved metadata is capped at 1 MiB.
Over-limit payloads record their byte count and omission reason without writing
the blob. If the setting is empty or capture I/O fails, the original
self-check refusal remains unchanged.

Focused specs assert `FlatPoolReader.failure_detail` for enum and struct
fields, and exercise the production quarantine writer with a small payload,
an over-limit payload, an existing destination, and an empty opt-in directory.
They verify payload bytes/hash, manifest fields, omission metadata, and
no-overwrite behavior. They have not been executed with a qualified Simple
runtime; the new generated-code diagnostic and quarantine artifact remain
source-reviewed, not runtime-qualified.

The opt-in is available on the canonical CLI worker route without another
environment allowlist: `src/app/cli/native_build_main.spl:902-912` builds the
`native_build_worker.spl` command, and `:965-976` launches it with
`process_spawn_async` after changing only the shard queue/owner variables.
`src/lib/nogc_sync_mut/io_runtime.spl:659-660` delegates that API to the raw
process-spawn operation with no replacement environment, so the worker
inherits the CLI process environment. The builder-owned clean-environment
lists in `src/app/bootstrap_builder/worker.spl:53-78` and
`grouped_native_run.spl:157-174` are separate build orchestration routes and
do not launch this canonical native-build worker; no broad allowlist was
changed. End-to-end propagation through a qualified CLI/runtime remains
unexecuted.
