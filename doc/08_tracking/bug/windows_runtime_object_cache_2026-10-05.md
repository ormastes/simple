# Windows C runtime object cache

Status: source implementation prepared; native correctness, concurrency, memory,
and performance qualification pending. This change does not meet or claim the
requested complete-compile target of 0.1 seconds.

The measured 916be Hello builds used one 65-byte Simple module. Cranelift took
361.635 seconds cold; LLVM took 141.597 seconds with the SCV snapshot already
present but a separate frontend/object cache. Neither was a fully warm build.
The object-to-executable timestamp intervals were approximately 41 and 50
seconds. They include runtime compilation and linking and do not isolate either
cost. The runtime compiler unconditionally disabled its object cache on Windows.

The new clang-cl adapter preprocesses each runtime translation unit into a
private `.i` file and compiles that same file. Content hashes cover the actual
preprocessed bytes, compiler and adjacent DLLs, ordered semantic arguments,
expanded compiler plan, target/profile/ABI, and relevant environment. Unsupported
injected arguments or external code-generation inputs use the original compile
path. Strict admitted-tool mode retains its existing cache bypass.

Objects publish into a content-addressed store before an atomic versioned index.
Readers validate the index and object bytes, copy privately, and publish to a
previously absent output. Existing output paths, including hard links, are never
opened for overwrite. Cache IO failures remain misses; failed cache publication
does not turn a successful compilation into failure. Toolchain drift invalidates
the build, and changed preprocessed bytes cannot publish an object.

Source tests from agent checkpoint `71df8e0640d` cover four metadata cases and
three real filesystem cases. These seven cases are authored but UNRUN. A local
clang-cl `-###` dry-run confirmed that `.i` selects `cpp-output`; no object was
produced by that check. This is compiler-driver contract evidence, not native
validation of the Simple implementation.

Remaining verification: actual helper execution, cold/warm output equivalence,
same-size preserved-mtime nested-header edits, macro/toolchain changes,
configuration/response-file refusal, concurrent writers, failed publication,
and elapsed-time plus peak-RSS comparison. Preprocessing and hashing still cost
time on hits; whole source admission and linking remain separate bottlenecks.
Live bootstrap source snapshots and caches were not changed by this work.

**Revalidated 2026-11-02: still plausible because source implementation prepared; native correctness, concurrency, memory,; no merged fix commit with a passing regression is cited in this doc.**

**2026-11-03 (rtobjcache lane):** implementation is on release/1.0.0 (b8201121d43, 15b5c8b8161, 506a01b127a). Seed `bin/simple.exe test` on a clean worktree: `test/01_unit/compiler/backend/runtime_object_cache_material_spec.spl` 6/6 pass (6.6 s wall), `test/02_integration/compiler/runtime_object_cache_io_spec.spl` 3/3 pass (6.8 s wall). Still pending (status fix-implemented-verification-pending): native clang-cl cold vs warm runtime-object compile on Windows with wall time and peak RSS, same-size preserved-mtime header edit, concurrent writers. Repro: build any hello module with `SIMPLE_RT_OBJ_CACHE_DIR=<dir>` twice using a pure-Simple stage3 and compare `[RT-COMPILE]` trace times.
