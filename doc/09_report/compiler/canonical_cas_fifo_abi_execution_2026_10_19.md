# Canonical CAS bounded FIFO ABI execution — 2026-10-19

**PASS: 21 C-provider ABI cases.** Native 14/14 and compatibility 7/7 exited 0.
Root ran the actual reviewed C providers; this is not a Simple `cas_put` run.
Simple CAS11, Rust-provider execution, full compiler/MCP/LSP checks, baseline
old-provider runtime reproduction, coverage and release qualification are UNRUN.

## Source and execution identity

- Reviewed source: `aa5cb90ddbbd98f0acf304af4bba16c81b6c2184`, on CAS fix
  `fe1bb38b5d2826d00a2167b82dbaf78e0c9042eb`.
- Independent source review: `/root/astra_warning_authority_review`, ACCEPT_STATIC;
  original CAS files remained unchanged throughout provider qualification.
- Root-owned retained evidence: `/tmp/simple-fifo-abi-aa5cb90.gIMNVC`.
- Original run-packet Markdown SHA-256:
  `16d021cbbbb6f32f50f1c156ffa5da5f3173d14f0d4fa436f73d3c389660c6b6`.
- Companion verbatim-block script SHA-256:
  `64bb253165cd482ab0460a85c2a6761d0643fa940a8ac6844e081095fc7569a3`.
  Root's original extraction used the same three blocks; this companion's
  shebang/provenance header is not a claim of byte identity to root's extraction.
- Failed-only cycle-2 script SHA-256:
  `dfb54f7ff077093dacf3459e466272ceeb762d9b808ec0a49f93801b90830a17`.

The packet snapshotted 31 source/header/harness files from the immutable commit.
Native linked the complete actual `runtime_native.c` object. Compatibility linked
actual `runtime.c` plus the relocation-retained native string-support closure.
Symbol allowlists, linker traces/maps and hashes passed. No copied helper,
renamed reader, stub, duplicate suppression or Rust seed was involved.
The qualified configuration is the isolated default hosted-C GNU/Linux provider;
this does not qualify a different memory-owner build or running compiler binary.

## Two bounded qualification cycles

Cycle 1 compiled the actual native provider and harness successfully, then failed
at linking because compiler-selected `mold` attempted to reserve 8 GiB under the
1 GiB address-space ceiling. The original `native-link.stderr` and exit 1 remain
preserved. No runtime test ran in that cycle; this was a linker-environment
failure, not an old-provider FIFO baseline execution.

Cycle 2 selected available `/usr/bin/ld.bfd` (GNU Binutils 2.42), keeping every
memory/time ceiling. It reused these exact successfully compiled objects:

- `runtime_native.o`: `e5da269c280ca81cbca0246eb85b180056013398fdd95eaadaf636b1a1f86d04`
- `native-probe.o`: `8dce1f4c76bb75841a1e67ccbc78360788d1971b19056bff810b8cf41ed9b311`

Only the failed native link and previously unrun stages executed. The root
reported terminal exit 0 for cycle 2. All compile/link/attribution/hash checks
passed; native and compatibility tests each ran once. No source change, higher
limit, parallel build, successful-step replay or additional runtime run followed.

| Measured step | Wall time | Maximum RSS | Exit |
|---|---:|---:|---:|
| Native provider compile, cycle 1 | 1.67 s | 149,308 KiB | 0 |
| Native link, explicit bfd, cycle 2 | 0.02 s | 13,584 KiB | 0 |
| Native ABI cases | 0.14 s | 1,624 KiB | 0 |
| Compatibility provider compile | 0.41 s | 60,112 KiB | 0 |
| Compatibility ABI cases | 0.07 s | 1,636 KiB | 0 |

The recorded ceilings were 120 s / 1 GiB per compile/link and 60 s / 256 MiB
per test process. Harness cases additionally used independent child alarms and
parent kill/reap deadlines. Timings are this isolated harness's measurements,
not CAS latency, compiler startup, or general memory-budget claims.

Seven private-root fixtures per lane exercise unwritten FIFO refusal at positive
and zero bounds, exact UTF-8/NUL bytes, empty content, oversize, symlink and
directory refusal. Native runs both text/byte lanes; compatibility runs text.

## Actual case output

Native:

```text
PASS text FIFO without writer (wait_status=0)
PASS text FIFO zero limit (wait_status=0)
PASS text ordinary counted UTF-8/NUL (wait_status=0)
PASS text empty zero limit (wait_status=0)
PASS text oversize refusal (wait_status=0)
PASS text symlink refusal (wait_status=0)
PASS text directory refusal (wait_status=0)
PASS bytes FIFO without writer (wait_status=0)
PASS bytes FIFO zero limit (wait_status=0)
PASS bytes ordinary counted UTF-8/NUL (wait_status=0)
PASS bytes empty zero limit (wait_status=0)
PASS bytes oversize refusal (wait_status=0)
PASS bytes symlink refusal (wait_status=0)
PASS bytes directory refusal (wait_status=0)
PASS bounded FIFO provider contract: 14/14 cases
```

Compatibility:

```text
PASS text FIFO without writer (wait_status=0)
PASS text FIFO zero limit (wait_status=0)
PASS text ordinary counted UTF-8/NUL (wait_status=0)
PASS text empty zero limit (wait_status=0)
PASS text oversize refusal (wait_status=0)
PASS text symlink refusal (wait_status=0)
PASS text directory refusal (wait_status=0)
PASS bounded FIFO provider contract: 7/7 cases
```

## Retained evidence receipt hashes

All paths below are relative to the root-owned evidence directory above. Full
maps, symbols, commands, timings, exit statuses and source/object hashes remain
there; these hashes bind the retained files without embedding large link maps.

| Evidence file | SHA-256 |
|---|---|
| `source.commit` | `6c0c0129052a47aba737756f0f250a04f79feac44d837592d5b2a76e1522c5c1` |
| `source.manifest` | `64385a9ea2d879c6c826b190c8db686d1100701efefb21b975ed80e005332ed4` |
| `source.sha256` | `f4221288fb530d5bb37bbf834a80e98f6ea76a14ce586a4b2645119566a11b03` |
| `archive.sha256` | `c67c81666c90acf4b4238caf76b7c24690b34b84bcbcee8769940892c844a59d` |
| `reviewed-hash-check.log` | `f382f6b8a899f37db95e9e350f7e758c31a95f7d54bcadbe37b461492186be07` |
| `toolchain.txt` | `fbc896f77a95ba95b94d954135dd27956f2c5095c044935fcba28a4f6d44cf53` |
| `cycle2-linker-identity.txt` | `55cb6a9a8adb37464f0001de6fe74f109c57019c5dda6fb2b7e540a9f49ef26e` |
| `cycle2-reused-object-check.log` | `2a61d198e63b027cd30221205a00242b2393b9a16fd8ab885416e618d72e3937` |
| `native-compile.time` | `41ae4faf47b79d89f82dd6746f35023147b1392033e6578adfb6ad1222c8e516` |
| `native-link.stderr` | `0f09f23b8e7f2841e0b11724a9e47eb2a1b51ec28d144e5536fb6dbee52017c4` |
| `native-link-cycle2.stderr` | `317a7b8aae0a6ecd9c63628f75a6656097b2bb5c9a7c57ca78405a5632b4c2c0` |
| `native.map` | `2c4f0e7aa4ff9026c589dcad8c1a2fd6a8389112875acb60521af96c087ce697` |
| `native.symbols` | `3286f030f0865fb150a7a51dfcf854f5a4430951c948b600f341986ba2e9846e` |
| `native-artifacts.sha256` | `828fcc8c3007edbbdacfdffc5fb7ce6c9e805f866b7b72cd92fa9532457213e1` |
| `native-run.stdout` | `940989c53412a391c2f1b72ed520e2707a7edcc7ee04b29fb971ff3fb6671dad` |
| `native-run.time` | `7ba51015ad377141c487c8229da8c919acc5966855a6b372dabc21cae01e9125` |
| `native-run.exit` | `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa` |
| `native-string-support.map` | `45c426d47e9de5e8f4fc3ec438ab88be13a6b66d9651ad1e175a1e91e9193be8` |
| `string-support.actual` | `133a5dfd92b7eb09f241cab4e24e29f0b8808731f0c8aa8b48ae21d04cf87b64` |
| `string-support.all-symbols` | `13c12e387e1503f6f3ff51967704c0b380c803b4522f72231762e9183e06cb8f` |
| `compat-link.stderr` | `8e627be7b75fea0377abf4e2f1ad17e37eb6ddfced9aadc26bacf740d9b310d0` |
| `compat.map` | `f4685bf7bd9a8b0022b86afb52ba5876ae68c60537a42fb49557584625462020` |
| `compat.symbols` | `480bc935050a829ab6a959663b062cc3867b9a777e952c8e4085fd73d9e3ed32` |
| `compat-artifacts.sha256` | `de218948e76970e5baa498cc82b9fd82b73bb5d9d165ebeb8962f36dd6b0fec0` |
| `compat-run.stdout` | `8655a1c874ec4da3234df27027899f739e8a5746bc118c69ec8320b3921521a5` |
| `compat-run.time` | `72e6a15dc4053e053502e602efc1c1728f4c7df7531575a058a6d4768341e67c` |
| `compat-run.exit` | `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa` |

See [combined qualification](canonical_cas_fifo_qualification_2026_10_19.md),
[original run packet](canonical_cas_fifo_abi_run_packet_2026_10_19.md), and
[provider defect](../../08_tracking/bug/bounded_regular_read_fifo_open_2026_10_19.md).
External receipt/header/provenance readback remains mandatory. A C-provider
FIFO PASS does not establish execution of the eleven Simple CAS regressions.
