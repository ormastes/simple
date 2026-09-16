# Imported trait method metadata is absent in per-file native HIR

- Filed: 2026-09-08
- Severity: P0 Stage4 blocker
- Status: compiler gap open; attempted defining-module generic facade did not unblock Stage2
- Exact site: `src/compiler/00.common/cache_contract/virtual_source_registration_v1.spl:43`

`gateway` is explicitly authored as `CacheGatewayV1`, but that trait is defined
in another compilation unit. The HIR module's `trait_infos` contains local trait
definitions only. Because trait names alias to `Any`, MIR cannot recover the
imported vtable slot and emits a bare static `virtual_source_store` call. LLVM
then correctly fails closed rather than inventing an extern.

The current Rust change preserves authored trait-owner hints and proves local
trait dispatch (focused test: 1 passed, 0 failed), but it cannot manufacture an
imported method signature. A defining-module facade was attempted with the
generic constraint preserved end-to-end; canonical Stage2 still lowered its
`gateway.virtual_source_store()` body as a bare static call and failed closed.
A general fix must carry imported trait definitions and slot signatures through
`pipeline/native_project/imports.rs` into per-file HIR, including generic
constraint owners. That is the exact unblock condition for the next session.
