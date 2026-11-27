# Inline `None`: corrected attribution for the retained string-builder failure

Bug: `mir_enum_payload_inline_none_lowered_as_nil_2026-11-10` (P1).
Investigation: 2026-11-10, `01a1c3cc/p1_enum_opt`.

Status: open. The separately alleged `HirTypeKind.Array` and `HirExprKind.IntLit`
sites have not been resolved by this investigation.

The retained string-builder failure does **not** demonstrate that the native compiler converted
`None` into `NilLit`. Its actual frozen input contains a bare `nil` at the exact
reported location. The MIR diagnostic correctly rejects that input. This
corrects the diagnosis; it does not qualify a new compiler or the full bootstrap.

## Exact input and failure

The retained stage3 log is
`C:/dev/p3new/stage2new/build_s3b.log.err.prev1`. Line 31115 reports:

```text
enum construction 'compiler.mir.mir_instruction_kinds.MirInstKind.Call':
payload type mismatch at 0: nil outside unsafe into optional payload slot
(declared 'LocalId?'); use None
function=apply module=compiler.mir_opt.string_builder_opt
string_builder_opt.spl:197:71
```

The retained source is under
`C:/dev/wt/p4-compiler/build/scv/snapshots/scv-revision-v2-f7e66732320182776d9cdaa29c362987d9411eb449da1f4e078b146e595f4ec9/`.
Its `src/compiler/60.mir_opt/mir_opt/string_builder_opt.spl:197` reads:

```simple
insts.push(MirInst(kind: MirInstKind.Call(nil, sb_fn_operand(SB_PUSH_FN, MirType.i64()), [sb_op, p.suffix]), span: src[i].span))
```

The file is 15,387 bytes. Its SHA256 is
`fdbc34e31e5151dd88f3edd04defb370229f374c32b453214660fc390f195a21`.
The complete bytes exactly equal the Git blob at both
`099d1c57f92:src/compiler/60.mir_opt/mir_opt/string_builder_opt.spl` and
`d974d6723ae^:src/compiler/60.mir_opt/mir_opt/string_builder_opt.spl`.
This is an exact file comparison, without newline normalization.

The snapshot receipt binds revision
`scv-revision-v2-f7e66732320182776d9cdaa29c362987d9411eb449da1f4e078b146e595f4ec9`
to inventory/tree
`257b9255fccfc26a6c565683ae007550744a456ffe149c0c910a96d51e96ae1d`
and 15,614 files. Its inventory contains this exact row:

```text
src/compiler/60.mir_opt/mir_opt/string_builder_opt.spl|sha256_fdbc34e31e5151dd88f3edd04defb370229f374c32b453214660fc390f195a21|15387
```

The log's source-load and HIR records use this snapshot under
`p4-compiler`; the diagnostic span retains the earlier `stage2-rel` root but
the same snapshot revision and file location. That path difference is not
evidence of a changed token. The original `stage2-rel` snapshot directory is no
longer present, so the following retained cache evidence supplies the path-to-input
identity link instead of assuming equal snapshot directory names prove equal bytes.

The frontend cache entry
`C:/dev/p3new/stage2new/cache_s3/default/frontend/bfa4d9f11343b103f6343a741ab07b10.fpc`
stores the exact diagnostic `stage2-rel/.../string_builder_opt.spl` path at line
2518. Its second line binds input identity `I` to the frozen source SHA256 above
and body checksum `C` to
`b7d9c2a38538f7726042a1725bdb6f9f64cfa126101630b055600d3fb5253a35`.
SHA256 of all bytes after its first two newline-terminated lines equals that
checksum. SHA256 of the entire cache entry is
`c512bcf4689b0cd98e8bcef399a669e9d4e5ab1566e7ac0d36f0885c3d600a5e`.
The checksum and input-identity contract is defined in
`src/compiler/10.frontend/frontend_parse_cache.spl`; neither a cache filename
nor a directory name alone establishes input identity.

`C:/dev/p3new/stage2new/run_s3b.ps1` selects `stage2_new4.exe`, disables HIR
cache with `SIMPLE_HIR_CACHE=0`, and enables SCV cold inventory/freeze fallback
with a 7,200-second minimum snapshot age. These settings and the frozen input
must be considered before attributing a failure to the current checkout.

## Source history and remaining scope

Commit `d974d6723aed093cf00da80f9cf354aad91068b0` changed the rejected
`MirInstKind.Call(nil, ...)` sites to `MirInstKind.Call(None, ...)` on
2026-11-09. The later `1a195a28c638` change introduced typed optional locals
as a workaround. This investigation leaves those source forms unchanged:
neither weakening the bare-`nil` rejection nor removing a workaround is
justified by the retained failure.

The existing `enum_payload_inline_none_contexts_spec.spl` records prior
interpreter and small native reproducer coverage. That historical coverage is
not a new PASS and is not used here to claim current full-graph verification.
The evidence established here is the exact frozen input and its agreement with
the diagnostic, not a newly executed product regression.

The stage3 campaign remains failed: its terminal log reports 1,110 failed
modules, 1,616 claims, and `all_stopped=true`. Line 53318 independently reports
`E-BACKEND-LLVM-CONST-TYPE` in
`compiler.driver.driver_mir_shard_export_v1.driver_mir_shard_export_write_one_v1`.
That failure and other incomplete bootstrap work remain with the bootstrap
campaign owner. This record does not resolve them or infer their root causes.

A future report of `None` becoming `NilLit` needs the actual admitted/frozen
source containing `None`, its identity, and the failing compiler boundary.
The supplied retained string-builder failure cannot support that transformation
claim. The other alleged sites and current full-graph verification remain open;
this forensic correction must not close the broader bug record.
