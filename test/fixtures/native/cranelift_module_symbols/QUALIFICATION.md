# Qualified macOS native naming projection

Evidence root: `/Users/ormastes/simple-tmp/cranelift-provider-naming-20260923/build/native_probe`.
Source base: `cd0f23020d1acfc1187657fb6574da6777c7ebd3` plus the naming patch.
This is bootstrap-defect evidence, not a general seed-based test workflow.

The producer and compiler-backfill authority directory is
`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/evidence/macos-enforced-bd544/stage2-disk-reclaim-b9107f6/frozen-failure/runtime-authority`.
The admitted capsule directory is
`/Users/ormastes/simple-tmp/macos-runtime-guard-pagesize-20260923/build/evidence/runtime-guard-pagesize/canonical/core-c-bootstrap`.
Its manifest reports65 checks, status=pass, and archive SHA256
`7496e6c5e8dbfd769b1bab6c23078928f744dadd923069fa6cd80620fca2d998`.
Do not replace it with the default generated core archive: that archive contains
strong named Cranelift bridge traps. Do not skip capsule gates or alter members.

The canonical generated startup object was reused unchanged from
`/Users/ormastes/simple-tmp/stage2-result-identity-20260923/build/native_probe/provider-qualification/native-objects-YI22ld/_main_stub.o`.
SHA256 `3299c3bbf396a314d567149916899ba34da6df8059995cbf5bf556c6072810ca`.
Its source is the frozen producer's generated `_main_stub.c`; it sets args,
initializes the runtime/modules, calls spl_main, and shuts down. The link map
confirms the actual fixture spl_main is live and the weak fallback discarded.
Archive generation also emits the concrete module-initializer caller.

## Recorded command shape

Run from the isolated source worktree. `provider_dir`, `capsule_dir`, and
`main_obj` mean the exact paths above. `probe_dir` is one private entry/cache
directory, not shared by concurrent builds. Compiler/tool paths come from
the frozen `macos-enforced-bd544/llvm23-env.sh` (LLVM23).

```sh
perl scripts/resource/process-tree-rss-watchdog.pl \
  --max-rss-kib=5859375 --timeout-seconds=180 \
  --receipt="$probe_dir/archive.rss.env" -- /usr/bin/time -l env \
  SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 \
  SIMPLE_PACKAGE_INDEX_COLD_INIT=1 SIMPLE_KEEP_NATIVE_OBJS=1 \
  SIMPLE_LIB="$PWD/src" SIMPLE_NATIVE_BUILD_CACHE_DIR="$probe_dir/cache" \
  "$provider_dir/simple" native-build --verbose --backend cranelift \
  --runtime-bundle core-c-bootstrap --runtime-path "$provider_dir" \
  --entry-closure --threads 2 --cache-dir "$probe_dir/cache" \
  --mode one-binary --emit-archive --entry "$probe_dir/probe.spl" \
  --output "$probe_dir/probe.a"

perl scripts/resource/process-tree-rss-watchdog.pl \
  --max-rss-kib=5859375 --timeout-seconds=120 \
  --receipt="$probe_dir/link.rss.env" -- /usr/bin/time -l "$CC" \
  -fPIC -Wl,-dead_strip -Wl,-map,"$probe_dir/probe.map" \
  -o "$probe_dir/probe" "$main_obj" \
  -Wl,-force_load,"$probe_dir/probe.a" \
  -Wl,-force_load,"$capsule_dir/libsimple_runtime.a" \
  "$provider_dir/libsimple_compiler_backfill.a" \
  -L/opt/homebrew/lib -lm -lSystem -lz -lffi -ledit -lzstd -lxml2 \
  -lncurses -lobjc -liconv -lc++ -framework CoreFoundation \
  -framework Security -framework SystemConfiguration -framework IOKit \
  -framework CoreServices -framework Foundation -framework AppKit \
  -framework Metal -framework CoreGraphics
```

All runtime invocations use the same watchdog, cap5859375, timeout30, and
`/usr/bin/time -l`. Run each emitter from its own probe_dir so alpha.o, beta.o,
and caller.o remain isolated. Link those three objects directly with the same
clang, still under watchdog/time. Red must fail for alpha.value/beta.value;
green must link and its consumer must return0. Collect LLVM23 llvm-nm and
llvm-objdump --disassemble --reloc on the three objects and green consumer.
`contracts.spl` uses a separate contracts-cache, same archive/link composition.

The minimal smoke substitutes smoke.spl/smoke.a and uses only canonical
cranelift_new_aot_module/free_module, rejects a zero handle, prints
`cranelift-provider-create-dispose-pass`, and returns0. It passed before any
naming verification and independently received Astra review PASS.

Native naming evidence: both emitters0; red link1 with qualified undefined
symbols; green link0/run0; nineteen contracts0 with pass marker. Fifteen guard
receipts are quiescent with no observer errors. Exact helper-source projection
identity was checked against the baseline and patched production adapter.
No full compiler rebuild, bootstrap, deployed CLI, general SSpec, or release
qualification is implied. Preserve historical failed-provider receipts.
