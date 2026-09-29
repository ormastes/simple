# macOS Phase 2/3 CI installs stale LLVM bottles

Status: provisioning fix validated offline; macOS 15 CI requalification pending.

PR #1375 at `bbdc5555836247b07d98be246d440ae3bafc1d01` failed in
[run 35812382432](https://github.com/ormastes/simple/actions/runs/35812382432).
Homebrew poured LLVM and LLD 23.1.0 while Rust already reported LLVM 23.1.1.
The exact 23.1.1 gate correctly failed before bootstrap; missing evidence artifacts
were a downstream consequence.

## Change and authority

Explicitly refresh runner Homebrew metadata. Admit only official `homebrew/core`
LLVM 23.1.1 revision 1 and LLD 23.1.1 revision 0 `arm64_sequoia` bottles:

| Formula | SHA256 |
| --- | --- |
| LLVM | `4ca75cd24ea8f06f85ad16113dc274bbd2496e3330cb0765e69b142a39749876` |
| LLD | `0a3b3975ef21e47f18f7c20823f3e927bf006d92483733bea8434cf8c981efe2` |

Authority is immutable Homebrew commit
[`7383a810b541351e197e114b3de06490b5357dbc`](https://github.com/Homebrew/homebrew-core/tree/7383a810b541351e197e114b3de06490b5357dbc/Formula/l),
independently read through the GitHub contents API for `llvm.rb` and `lld.rb`.
Both formulae identify the upstream LLVM 23.1.1 source archive SHA256 as
`ebe9be46fe8756d58c5b198ffad0fa2a766257add81a4dc52179bfacc7888ee6`.

Fetch the bottles through Homebrew, hash the cached archives against admission,
and reinstall those verified local archives. Reinstall replaces any same-version
preinstalled source build. Formula/version/hash drift fails before installation.
The subsequent Rust/Clang/LLVM/LLD version gate is unchanged.

Provisioning has a 15-minute workflow timeout, a 6 GiB free-space prerequisite,
and explicit bottled installation. The free-space check is not a disk quota.
Homebrew manages declared dependency bottles; this change does not pin the
entire dependency closure. No LLVM build, installation, or bottle download ran
on the shared local host during verification.

## Validation

- `macos_phase23_llvm23_provision_test.shs`: PASS. Executes the installer with
  simulated Homebrew/host IO. Accepts reviewed metadata and exact downloaded
  hashes; rejects stale 23.1.0, changed SHA/URL/revision/tap, missing platform
  bottle, simulated downloaded digest mismatch, wrong architecture/OS, low disk,
  and failed update. Hashing and Homebrew IO are mocked; no real corrupt archive
  was downloaded.
- `macos_phase23_llvm23_pin_contract_test.shs`: PASS. Exact 23.1.1 accepted;
  23.1.0, 23.1.10, failed probes, and missing linker rejected before CI env write.
- `macos_phase23_rust_toolchain_test.shs`: PASS.
- Real host pin: PASS on installed Homebrew LLVM 23.1.1_1, LLD 23.1.1, and
  Rust LLVM 23.1.1. These are Tahoe bottles, not macOS 15 runner qualification.

Local executable SHA256 observations (not portable bottle pins):

| Cellar executable | SHA256 |
| --- | --- |
| `llvm/23.1.1_1/bin/clang` | `8daf964b5d524b4754d4300f370d9956a1de8f3815ce5828bb8fd8ad087b0b78` |
| `llvm/23.1.1_1/bin/llvm-config` | `014b9b437826150356ed795deffecfd50a6d3170b24b225e5fc38596acb29553` |
| `llvm/23.1.1_1/bin/llvm-ar` | `bf7b91eb57fc1fd8469f697a0951d7fa54cc04927f804921292739313c3784f3` |
| `lld/23.1.1/bin/ld64.lld` | `1f80841d925f7b7d875d88e593e6e12dd496ab9227fc60f6ce9b07f73df6c81e` |

The actual macOS 15 bottle installation and Stage 2/3 evidence remain CI gates.
