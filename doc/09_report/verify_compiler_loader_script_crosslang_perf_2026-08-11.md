# Verification: compiler, loader, and script cross-language performance B+B

## Passing evidence

- Loader negative-cache focused spec: 5/5 PASS; exact repeated miss, caller-sensitive adjacency, and reset invalidation.
- Loader and byte fixture optimizer analyses completed; no automatic source rewrite was applied.
- Cross-language report contract PASS and shell syntax PASS.
- Actual harness launch exits 2 and rejects the deployed Rust bootstrap seed before measurement.
- Byte fixture now exits 1 on `requested=1048576 actual_len=0`, eliminating the former false-green row.
- Changed Simple files linted without changed-file errors; emitted warnings are pre-existing imported-surface findings.
- Direct environment/runtime guards: working PASS, staged PASS.
- Generated-spec layout guard: 0 executable `.spl` files under `doc/06_spec`.
- Stub/placeholder scan of owned source, tests, and harness: clean.
- Interpreter byte extern accepts checked signed and unsigned ABI shapes; focused Cargo tests pass.
- Retained comparable-result schema now records raw samples, p50/p95, maximum RSS, executable hash, self-host verdict, requested/actual mode, fallback, exit, and checksum for Simple/C/Rust/Go/Python/Bun; focused generated-fixture contract passes.
- A real Stage 2 compiler was admitted at isolated HEAD `7731b4c139448d84b4ff50e2fbdbdf5e3ac0128e`, SHA-256 `775e724d57c2675625ff9d590dec6ce88d8f08cf90b6bda65eca68a6d406504a`.
- The tiny Cranelift reproducer is non-vacuous at the source boundary (one module, two functions) and fails closed in 0.02 s at 30,720 KiB with `modules=1 functions=0`.
- A producer containing the entry-function ownership repair advanced the full Stage 3 receipt from `modules=573 functions=0` to `modules=573 functions=26`. This is direct success evidence for that repair, but not Stage 3 admission.
- Isolated cycle-3 patch `/mnt/data/bs2/final-e73-cycle3/cycle3.patch` (`ebae2ad...`) passed focused gates, and `/mnt/data/simple-authority-tuple-682c2` passed isolated authority-tuple tests. These are scoped source/test results only.

## Release-blocking failures

- FAIL — `bin/simple` SHA-256 `df2da4952028ebbe3e89d0a2255d34c93e63522ad779d3444c5a0c82d3a0f5a0` identifies as the Rust bootstrap seed. No admitted current pure-Simple compiler is available.
- FAIL — changed SSpec cannot receive authoritative pure-Simple `spipe-docgen` or `sspec-maintain scan` evidence; the hand-maintained mirror is not a substitute.
- FAIL — NFR-001/002/003 lack admitted before/after p95, maximum RSS, and syscall proof. The diagnostic seed is intentionally rejected.
- FAIL — required compiler/core/lib, MCP, LSP, and MCP integration checks cannot produce qualifying evidence without the admitted runtime.
- FAIL — working numbered-artifact guard reports unrelated concurrent `mission_critical_infra_hardening_v2` and `check-sosix-fs-registered-buffer-client-v1` artifacts. Staged guard passes; these files are outside this lane and were not modified here.
- FAIL — one isolated bootstrap attempt at committed HEAD `664070dece71a1937f353805f3e34afbe60121f2` exits 101 before Stage 1: committed runtime exports and `HeapObjectType::WideInt` are inconsistent. The required fixes currently exist only inside another session's 96-path dirty authority tree, so no safe Stage-4 artifact can be produced or deployed from it.
- FAIL — the admitted Stage 2 cannot produce Stage 3: the full 573-module run fails at `functions=0` after ~981 s with 22,668,904 KiB maximum RSS. A patched-source retry through the same frozen producer repeats the receipt at 22,715,552 KiB (14:25.84), but this is not valid patch validation because the producer does not contain the patch. The formerly recorded implication that this disproved the source repair is retracted.
- FAIL — interpreter `[u8]` remains `Arc<Vec<Value>>`; the 4× payload RSS target requires a first-class packed-byte value across shared indexing/mutation/bridge surfaces already owned by concurrent dirty lanes.
- FAIL — after the entry repair produced `functions=26`, Stage 3 terminated with SIGSEGV and emitted no compiler. Retained gdb frames are `MirLowering.remember_local_hir_type <- maybe_copy_array_value <- lower_stmt_impl`; immediately preceding unresolved `push_scope`, `exec_stmt`, `eval_expr`, and `pop_scope` calls were lowered to const-0 placeholders. This is corrupted MIR/type-owner evidence, not a safe location for a fallback guard.
- FAIL — the repaired-entry Stage 3 peak was 22,741,020 KiB (~21.69 GiB). NFR memory admission remains red even though entry non-vacuity improved.
- FAIL — Stage 2 timing is not comparable: run2 compiled 815 modules in 1091.8 s plus 74.4 s link (1166.2 s total), while a concurrently contended canonical build compiled 829 units in 1721.4 s. Closure and contention differ, so neither is an admitted before/after row.
- FAIL — authority transport copied 2,486,332 KiB across 3,092 files for a required three-artifact tuple of 155,637,552 + 374,787,590 + 17,203,864 bytes (~522 MiB). The tuple fix is isolated and tested, but shared integration is blocked by another lane's dirty `scripts/check/lib/bootstrap-stage3/authority.shs`.
- FAIL — native object caching now has parent-serialized per-module publication,
  content-addressed same-directory temp/fsync/rename object commits, directory
  barriers, persisted digest/format/target metadata, and cache-hit validation.
  The executable Simple owner/cold-link crash-restart gate remains blocked by
  the independently tracked `verification_ir.spl` parse failure, so this is
  implemented source hardening rather than admitted release evidence.
- FAIL — the third recovery cycle's corrected Stage 2 ran for 1500.04 s at 98% CPU and 925,880 KiB maximum RSS, then timed out with exit 124 and no candidate. Passing focused gates for `cycle3.patch` cannot substitute for an emitted and admitted compiler.
- FAIL — the `cd0277de18e722bab990cefdf12da63c07e41999` Stage 2 attempt exited 2 with no emitted or admitted Stage 2 executable. Retained log `/mnt/data/bs2/perf-integrated-cd027/logs/x86_64-unknown-linux-gnu/stage2-native-build.log` (SHA-256 `c9c10ba878b0f2154efcddf25fc1bb91949e79790141fc402a3b81598039d07d`) records 46 failed files versus 65 in the prior `eda2d6ce920` run; 29 are `ANY` canonical-owner/type-precedence failures. This reduces the census but does not change the release blocker; the feature remains active, not dev-done.

## Resume gates

1. Finish or isolate concurrent compiler work and deploy a provenance-admitted Stage-4 pure-Simple CLI.
2. Run the changed SSpec through pure-Simple SPipe docgen and `sspec-maintain scan` once.
3. Run the same admitted loader/compiler/script workloads once before/after and retain p50/p95, RSS, checksums, and failed metadata probes; require at least 90% fewer failed probes and no p95/RSS regression.
4. Run the compiler/lib/MCP/LSP checks and MCP integration test once.
5. Have the owners of unrelated numbered artifacts resolve their working-tree guard findings.
6. Build and admit one patched Stage 2/next producer, then let that producer run the Stage 3 reproducer once; editing only the source consumed by a frozen producer cannot validate the compiler-owner repair.
7. Before memory changes, add bounded phase RSS plus runtime object-count telemetry. After correctness, evaluate the architecture-safe sequence: canonical Stage 3 streaming surfaces, shared `HirLowering.begin_module`, pre-MIR parser release, indexed flat-HIR ownership, and reserved/chunked accumulators.
8. Reject unresolved receiver-method calls before MIR mutation, then replay the exact array-copy/type-ownership regression once with a newly built producer; do not add a crash-site default.
9. Integrate the verified authority tuple after the `authority.shs` owner conflict clears, then retain size/hash/path receipts proving no recursive authority-tree copy.
10. Integrate the eager per-object cache patch and run one cold failing-batch/retry/link sequence; require reusable valid objects and no partial executable publication.

STATUS: FAIL
