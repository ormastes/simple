# Authorized Phase 2 configured smux build

Status: FAIL before compilation; zero test cases executed. User explicitly authorized interim Phase 2 feature verification while Phase 3 is unavailable, without rebuilding Phase 2.

Compiler: `C:/dev/simple-disk-headroom-warm-bootstrap-storage-20261025/output/stage3/simple.exe`, SHA-256 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`. Source head: `bae69fc813b`, including explicit library-mode source changes. No compiler or runtime files were changed.

Command arguments: `native-build --source src --entry-closure --entry src/app/hosted_apps/smux_client.spl --library-mode nogc-sync-mut --output build/review/phase2-authorized-smux-probe/smux.exe`.

The bounded owned process returned exit 1 with `Error: unknown option: --library-mode`. Receipt status is complete/child-exit. Log limit was 65536 bytes, timeout 20 seconds, termination grace 2 seconds. Private retained artifacts: `build/review/phase2-authorized-smux-probe/compile.log` and `compile.receipt`. This was an option-admission probe, not a frontend or native-code generation attempt. No executable was emitted and no suite ran.

The user authorization resolves the phase-policy restriction for interim work; it does not add the missing option to these immutable compiler bytes. Removing the option would not verify the selected generic-import policy. Directory inference, internal-worker marker spoofing and seed fallback were not used. The next prerequisite is a compiler executable containing the already-authored explicit library-mode implementation, or a separately reviewed compatible configuration interface with equivalent semantics. Phase 3 qualification remains separate from interim Phase 2 evidence.
