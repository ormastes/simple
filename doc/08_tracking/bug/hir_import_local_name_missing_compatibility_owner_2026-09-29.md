# HIR compatibility facades export a deleted import-name helper

Status: source correction prepared; native execution pending review and a
refreshed pure-Simple producer. No full bootstrap qualification claimed.

The frozen Linux source 6772d23f5e2b5bd79c22152780d5183440ac342e, compiled by
pure Stage2 SHA256 569203737fe7bdfafd6f52cfe1c1c8d6a30ed17b741217a08c267058e2f8283c,
fails its streaming HIR phase on `src/compiler/20.hir/hir.spl`: the items facade
has no exported item `imported_symbol_local_name`. Authoritative retained stderr
is `linux-6772d23f5e2-early-phase3-diagnostic-20260929/cache/diagnostics/native-build-stderr-532969-1.log`
under `/mnt/simple-bootstrap-6b2`; its first fatal is source index 113. The later
invalid-export-origin diagnostics are a separate causal investigation.

Commit 28c19da98654e4e5ea1c1a67a09401ef82e94722 removed the real helper from
`hir_lowering/items.spl` while the compatibility imports and exports in
`hir.spl` and `hir_lowering/__init__.spl` remained. Current main
69db9bfa59aef6bc0c05150731a3d809a54d2d3b still has those references and no
production declaration. The historical helper selects `alias` when
`has_alias` is true, otherwise `imported_name`. Named import resolution had
inlined the same behavior. This is a genuine missing source owner, independent
of the already merged typed reexport-carrier and bootstrap Dict length fixes.

Restore the helper in `_Items/lowering_helpers.spl`, already reexported by
the items facade, and call it from named import selection. Preserve all facade
exports and the existing empty-alias behavior. Do not fabricate export origins
or remove diagnostics to accept a missing declaration.

The focused native component imports the real owner and all three compatibility
facades under aliases. It checks alias selection, the ordinary name despite an
unused alias value, and empty/equal aliases. Compile it using the admitted fresh
pure producer, bind the output hash, then require actual execution exit 0 and
exact `IMPORTED_SYMBOL_LOCAL_NAME_COMPONENT_PASS` stdout. The existing
`test/03_system/compiler/compiler_import_alias_resolution_spec.spl` also imports
the public package facade and checks DriverOptions/BackendOptions aliases and
the ordinary CompileOptions name. It remains in the current Git tree, although
the isolated checkout's sparse rules omit its physical file. Its assertions
are part of the future focused plan; the old document's Rust-intrinsic claim
does not replace native evidence. No tests or builds have run for this correction.
