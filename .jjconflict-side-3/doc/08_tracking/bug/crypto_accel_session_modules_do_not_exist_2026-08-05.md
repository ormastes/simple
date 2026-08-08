# All three GPU accelerator session modules do not exist, and the coverage manifests count them as covered

**Status:** OPEN — manifest half FIXED (see Next steps 2); module half changed
state mid-day. `src/lib/gc_async_mut/crypto_accel/{cuda,metal,vulkan}_session.spl`
appeared at `2026-08-05 06:36:14` from a parallel session and are still
untracked. Everything below describes the tree BEFORE that. Whether the three
providers now resolve their session types, and whether they still drop to the
interpreter, is NOT re-verified here.
**Found:** 2026-08-05
**Component:** `src/os/crypto/x25519_mlkem768/{cuda,metal,vulkan}_ntt_provider.spl`,
`src/app/test/x25519mlkem768_{coverage_contract,critical_inventory}.spl`
**Attribution:** measured on the Rust bootstrap seed; no pure-Simple binary
exists in this worktree.

Surfaced while measuring the JIT-drop blast radius
(`pem_decode_superlinear_and_jit_dropped_2026-08-05.md`): 4 of the 16 real
whole-module drops were x25519 NTT providers, and the cause was not a compiler
gap.

## The defect

Each of the three GPU NTT providers imports a session type from a module that
is not in the repository:

| provider | lines | imports | type used |
|---|---|---|---|
| `cuda_ntt_provider.spl:7` | 476 | `std.gc_async_mut.crypto_accel.cuda_session.{CryptoCudaSession}` | 4x |
| `metal_ntt_provider.spl:5` | 307 | `std.gc_async_mut.crypto_accel.metal_session.{CryptoMetalSession}` | 5x |
| `vulkan_ntt_provider.spl:5` | 347 | `std.gc_async_mut.crypto_accel.vulkan_session.{CryptoVulkanSession}` | 3x |

Verified directly:

- There is **no `crypto_accel` directory anywhere** under `src/`
  (`ls -d src/lib/*/crypto_accel` -> no match).
- `CryptoCudaSession`, `CryptoMetalSession` and `CryptoVulkanSession` are
  declared **0 times** in the entire tree
  (`grep -rnE '^\s*(class|struct|trait|type)\s+Crypto(Cuda|Metal|Vulkan)Session\b' src/`).

So 1,130 lines of GPU acceleration code are written against three types that do
not exist.

## Why it is silent

An unresolved `use` is only a **WARN**, and the run still exits 0. The missing
type therefore erases to ANY, every field access on it becomes
field-access-on-ANY, and the seed's HIR lowering drops the **whole module** to
the interpreter with a `[jit-fallback] cannot infer field type` message on
stderr. Nothing fails; the provider simply never JIT-compiles.

This is the failure mode that makes delete-verification and load-bearing checks
fail-open in this repo: exit status cannot distinguish "imported and working"
from "imported, absent, and erased to ANY".

## The coverage manifests count the phantom files as covered

Both campaign manifests list all three non-existent files alongside files that
genuinely exist:

| manifest | paths listed | missing on disk |
|---|---|---|
| `x25519mlkem768_coverage_contract.spl` | 37 | **3** (8.1%) |
| `x25519mlkem768_critical_inventory.spl` | 24 | **3** (12.5%) |

The missing entries are exactly `src/lib/gc_async_mut/crypto_accel/{cuda,metal,vulkan}_session.spl`.
Every other listed path resolves. So the campaign's own coverage accounting
includes three files that have never existed, and neither manifest checks
existence — the same shape as the "coverage illusion" recorded in
`network_coverage_illusion_and_spec_tree_duplication_2026-08-05.md`.

At least 10 spec files reference these providers. Whether those specs pass
today, and what they would be measuring if they do, is **not established here**
and should not be assumed either way.

## Next steps

1. Decide whether the `crypto_accel` session layer was ever written. If it was
   lost (this tree has had two confirmed history wipes), recover it; if it was
   never written, the three providers are aspirational and should say so.
2. ~~Make both manifests fail when a listed path does not exist.~~ **DONE
   2026-08-05.** `x25519_mlkem768_coverage_absent_in()` in
   `src/app/test/x25519mlkem768_coverage_contract.spl` is the gate; the three
   session paths were RETAINED as declared-blocked rows (named in every verdict
   line, counted as blocked, never as covered) rather than removed, since silent
   removal is what AC-8 forbids. The modules then landed at `2026-08-05 06:36`
   from a parallel session (still untracked), the gate's stale-block check went
   RED on exactly that, and the block was retired — the declared-blocked set is
   now empty and all 37 paths resolve. `_critical_owner_paths()` in the calibrator now
   delegates to the contract list so the two manifests cannot drift, and its
   `main()` fails with `reason=manifest-path-absent`. Runnable check:
   `test/01_unit/app/test/x25519mlkem768_manifest_existence_gate_spec.spl`
   (GREEN `Results: 8 total, 8 passed, 0 failed`; RED on an injected phantom
   `Results: 8 total, 6 passed, 2 failed`). A stale block — a declared-blocked
   path that later appears on disk — also turns the gate RED, so the block
   cannot outlive the gap. Status of AC-8 after the fix:
   `doc/09_report/x25519mlkem768_ac8_coverage_status_2026-08-05.md`.
3. Only then re-measure the JIT-drop radius — fixing this defect and the
   already-tracked `WineVmOpResult.region` one removes 7 of the 16 measured
   drops, and neither is a compiler bug.

## Reproduce

```
ls -d src/lib/*/crypto_accel                                   # no match
grep -rnE '^\s*(class|struct|trait|type)\s+CryptoCudaSession\b' src/ | wc -l   # 0
grep -n '^use ' src/os/crypto/x25519_mlkem768/cuda_ntt_provider.spl | head -1
```
