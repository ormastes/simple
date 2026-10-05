# Imported-global reference traversal dereferenced an absent expression

The Phase2 compiler with SHA256
`edcd1f43720d11aa611f8b1868e35809e78bf0c6de64781891293ad76d0f4eb7`
passed Hello, then the DB/web probe terminated with SIGSEGV during MIR lowering.
The saved core is
`/var/tmp/simple-item5-phase2-20261005/build/item5-db-web-gdb-detail/compiler.core`;
the adjacent `gdb.log` records the real compiler command and backtrace.

The fault at `0xa18be6` is the dereference of `expression.kind` in
`mir_global_reference_ids`, called by `register_imported_global_bindings`.
The instruction immediately follows `rt_enum_payload` and pointer-tag removal.
Offline core inspection shows a live `HirNode.Expr` at `0x1a225020`: enum ID
`0x469db73e`, discriminant `0xf58574ef`, payload **3 (nil)**. Masking the payload
produces zero. This is a nil payload in a valid enum, not evidence of an invalid
enum tag or of a reclaimed arena object. The precise producer of that absent
expression has not been established.

Generated `hir_children_of_expr` already defines nil input as an empty leaf.
The custom imported-global scan now follows the same contract before reading
the expression kind. Non-nil expressions retain the original reference and
child traversal. This does not suppress missing provider diagnostics or make
unresolved methods valid.

The focused regression in `imported_global_storage_binding_spec.spl` places
nil between a `Var` and a `NamedVar`, repeats the first reference, and requires
both IDs in order without duplication. It also checks the generated visitor's
nil-leaf contract. **Not executed**; source review and diff checks alone
do not qualify this regression. A combined repaired Phase2 build and actual
DB/web retry are owned by the parent session, separate from this source patch.

The combined repaired Phase2 candidate (`3658` hash prefix) passed both Hello
qualification checks. Its actual DB/web retry completed MIR with exit 1 instead
of SIGSEGV; the nil-expression crash disappeared and the remaining explicit
MIR errors were collected. Evidence:
`/var/tmp/simple-item5-phase2-20261005/build/item5-db-web-mir-repaired/native-build.log`
(final reported elapsed time 31337 ms). This is a passing crash regression, not
a passing application build. The independent numeric conversion runtime
mismatch is tracked separately and is not attributed to this guard.

The standalone `test/fixtures/compiler/provider_global_nil_reference_probe.spl`
constructs HIR values directly and calls the same production walker, without
copying its implementation or invoking a test parser fixture. It checks nil-leaf
handling, both reference IDs in order, and deduplication. For the qualified
compiler and runtime archive selected by the build owner:

Use the single positional entry without `--source`: the bootstrap CLI selects
the direct driver for that shape; explicit source roots select the coordinator.

```sh
"$QUALIFIED_PHASE2" native-build \
  test/fixtures/compiler/provider_global_nil_reference_probe.spl \
  --target x86_64-unknown-linux-gnu --backend llvm \
  --runtime-bundle core-c-bootstrap --runtime-path "$RUNTIME_AUTHORITY" \
  --entry-closure --threads 1 --cache-dir build/provider-global-nil/cache \
  --mode one-binary --output build/provider-global-nil/probe
build/provider-global-nil/probe
```

The actual standalone build traversed a 324-module closure and terminated with
exit 139 after HIR (154027 ms), before reaching MIR or producing the executable.
Evidence is `build/item5-provider-global-nil/build.log` and its adjacent RSS
receipt in the WSL source snapshot. This is a separate, unresolved large-closure
compiler crash. Neither the native probe nor the SSpec executed their reference
assertions; no ordered-reference or deduplication PASS is claimed. The
direct crash regression is the original DB/web build progressing past this
traversal without a signal; a later explicit MIR error is progress, not a passing
application build.
