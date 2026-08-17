# Enterprise Suite — Cross-OS Re-verification (lane W15-C, 2026-08-17)

Lane `.spipe/simple_enterprise_suite` W15-C. Re-verifies AC-17 (one codebase,
host + SimpleOS, no per-OS fork) against the wave-13/14 additions.

## Binary identity (produced every piece of evidence below)
- Compiler: `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
  (symlinked into this worktree as `bin/simple`), ELF x86-64, 59,536,728 bytes,
  BuildID `d219df7dee27059f4b61a5393a6d1b253535ea13`. This is the deployed
  default-tooling binary (`bin/release/<triple>/simple`).
- OVMF gate seed: `/mnt/data/worktrees/simple-main/src/compiler_rust/target/release/simple`
  (59,485,368 bytes), passed via `SEED=` env (no build, no other worktree touched).

## 1. Cross-OS SMF gate — PASS, coverage extended
`scripts/check/check-enterprise-cross-os.shs` verdict:
`PASS — 9 probe(s) checked, each compiles host + x86_64-unknown-simpleos with SMF magic`
(was 8 probes; +1 this lane). Each probe artifact begins with SMF magic bytes
`53 4d 46 00` on BOTH targets.

### Coverage audit of the wave-13/14 additions
- **Store audit chain** (`enterprise_store/store.spl` audit_log + the
  sha256-chain in `records.spl` `audit_append`/`audit_verify_chain`): already
  transitively compiled by `store_probe_main.spl` (imports `store_open/close/
  verify`) and now ALSO by the new session probe (session.spl imports
  `records.audit_append`). COVERED.
- **`enterprise_session/session.spl`** (frozen identity module: credential hash,
  token derive, `session_entropy_min_len` floor): was a **coverage hole** — no
  probe reached it. Added `src/app/enterprise/session_probe_main.spl` which calls
  `session_setup`/`session_issue`/`session_entropy_min_len`, forcing the module
  into the SMF set for both targets. COVERED (and it caught a real regression —
  §2).
- **Web-app dispatcher** (`src/app/enterprise_store_app/main.spl`
  `store_app_handle`, `auth_routes.spl` `store_app_handle_bearer`): a probe
  reaching this path FAILS standalone-SMF with 11 interpreter-required functions
  (`http_method_from_text`/`http_status_from_code` [PatternMatch],
  `sha256_bytes`/`sha256_u8_hex`/`str_*` [CollectionOps], all from
  `std.common.net.http_core`). This is the **documented standalone-SMF-codegen
  debt**, not a regression: the app layer runs INTERPRETED in-guest on SimpleOS
  (state L4 CLOSED, in-guest proven), it is not a standalone SMF artifact. It is
  therefore deliberately NOT wired as a required SMF probe — doing so would turn
  the fail-closed gate RED for a known limitation. The dispatcher's cross-OS
  proof is the in-guest interpreter path (§3), not this SMF gate.

## 2. Real regression found and fixed (kept ONE codebase)
`enterprise_session/session.spl` imported `std.common.crypto.sha256.sha256_text`
directly (credential_hash + session_token_derive). That pulls the slice/`[v; n]`
CollectionOps of `sha256_bytes`/`sha256_u8_hex`/`str_*` into the standalone-SMF
closure, so session.spl was **NOT cross-OS-compilable** (host rc=1, simpleos
rc=1, both "cannot compile to standalone SMF: 9 function(s)…"). This is the exact
defect `enterprise_store/audit_hash.spl` (`audit_sha256_hex`, digest-identical to
sha256_text) was created to fix in W4-B — session.spl reintroduced it.

Fix: route session.spl through the SMF-safe facade
`enterprise_store.audit_hash.audit_sha256_hex` (same digest, no per-OS fork).
After the fix the session probe compiles host rc=0 + simpleos rc=0, both with SMF
magic `53 4d 46 00`.

## 3. In-guest OVMF gate — BLOCKED (unrelated pre-existing kernel bug)
`scripts/check/check-enterprise-store-in-guest-ovmf.shs` (real OVMF pflash boot;
never `-kernel`, never isa-debug-exit). Prereqs present on this host:
`qemu-system-x86_64`, OVMF at `/usr/share/OVMF/OVMF_CODE_4M.fd`, seed via `SEED=`.
It advanced past seed/OVMF checks and into the SimpleOS kernel build, then FAILED
building `build/os/simpleos_entstore_uefi128.elf` for a cause OUTSIDE the
enterprise suite and unrelated to this lane's edit:

    callable ABI mismatch for 'SharedDmaMapping.can_release':
    Instance target declares 1 parameter(s), call supplies 2 explicit
    argument(s) and 1 receiver slot(s)
    FAILED FILES: src/os/kernel/memory/memory_swap_coordinator.spl
                  (MemorySwapCoordinator.can_release_swapped)
                  src/os/kernel/memory/memory_swap_runtime.spl
                  (memory_swap_runtime_can_release_range_in)

No transcript is fabricated. The blocker is a kernel `memory_swap` codegen bug in
`src/os/kernel/memory/`, not `src/app/enterprise_store_app/**` or
`src/lib/**/enterprise_*`. It must be fixed by the OS/kernel lane
(`SharedDmaMapping.can_release` arity mismatch) before the in-guest gate can boot.

### Resume command (after the kernel DMA arity bug is fixed)
    cd <this worktree>
    SEED=/mnt/data/worktrees/simple-main/src/compiler_rust/target/release/simple \
      sh scripts/check/check-enterprise-store-in-guest-ovmf.shs

## Files changed this lane
- `src/lib/nogc_sync_mut/enterprise_session/session.spl` — fix: use SMF-safe
  `audit_sha256_hex` facade instead of `sha256_text`.
- `src/app/enterprise/session_probe_main.spl` — NEW cross-OS probe covering
  `enterprise_session`.
- `.spipe/simple_enterprise_suite/state.md` — W15-C entry.
- this report.
