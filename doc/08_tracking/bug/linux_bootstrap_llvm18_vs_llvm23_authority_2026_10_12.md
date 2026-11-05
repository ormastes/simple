# Linux native bootstrap CI provisions LLVM18 against LLVM23.1 contracts

Status: OPEN; source and focused fixtures qualified, real installation/bootstrap pending.

Actual Linux diagnostic38162989607 stopped at runnerfixture preflight. Independent source mismatch: native workflow installs LLVM18+Polly18 while compiler Cargo.toml requires llvm23-1-force-static on non-Windows. Local primary apt metadata only offers23.1.2; the generic major23 installer cannot provision exact23.1.1 and is not used by this candidate. Official LLVM release metadata provides LinuxX64 archive2014958380bytes SHA256832aeb58d105de1cabc7b982dd2c65de0610f7377df48ae8fc2dd8e97420a15c. Exact tag resolves signedreleasecommit6dfe1677ab8dffbc6ec13d53a1e0215d75147689.

Dedicated installer uses gh release download to bounded temporary storage; validates size/digest before inspecting or extracting; requires sufficient measured expansion disk; cleans staging on failure. Immutable archive cache is keyed by digest and rehashed each use. Only pin helper publishes environment after actualtoolversions/prefix/Rust all agree at23.1.1. LinuxCranelift retains clang18/lld18/llvm18dev. DatedRust action matches reviewed toolchain-file pin2ee1f60, required in diagnostic integration.

Focused evidence: one valid toolchain binding +8negativecases PASS; actual selected workflow commands with isolated package/installer fixtures +7negative removals PASS; corruptarchive size and realSHA rejection precede extraction PASS. Archive-size precondition alone is mocked for digest-negative test; real2GBdownload/installation and compilerexecution remain UNEXECUTED. Evidence /mnt/c/Temp/simple-linux-llvm23-toolchain-20261012. Previousrun remains immutable.

Other platforms remain unqualified: nativeMac multiplatform still llvm@18/LLVM_SYS_180_PREFIX; dedicatedMac23.1.1job separate. Crossarchitecture LLVM18reader/setup and Windows contracts are not qualified by this change. LocalLLVM23.1.2 remains untouched.

Official archive Polly/PollyISL and static LLVM availability is unexecuted. Installer requires those archive-owned libraries before publication; no floating apt Polly may be mixed. Native Mac multiplatform and cross-platform LLVM18 contracts remain outside this Linux candidate.

**Revalidated 2026-11-02: still plausible because OPEN; source and focused fixtures qualified, real installation/bootstrap pending; no merged fix commit with a passing regression is cited in this doc.**

## Resolution (2026-11-03)

2026-11-03: workflow now installs the exact LLVM 23.1.1 archive via scripts/setup/install-linux-phase23-llvm23.shs + pin-linux-phase23-llvm23.shs; real CI run still pending.

## Verification Evidence (2026-11-05)

Environment: aarch64 Linux host; `/usr/lib/llvm-18` and `/usr/lib/llvm-23` present (`clang-18` at /usr/bin, `clang-23` at ~/dev/llvm/install/bin, `opt-23` at /usr/bin).

Worktree: `/tmp/wt-libbug-llvmauth`, branch `work/libbug-linux-llvmauth-20261105`, base `origin/release/1.0.0` (adfeae3765c).

Named check executed:

```
$ cd /tmp/wt-libbug-llvmauth && sh test/01_unit/scripts/linux_phase23_llvm23_workflow_test.shs
Actual Linux workflow wiring: valid commands + seven negative removals PASS
```

Result: PASS on first run, no fixes needed. The test exercises the real workflow steps `Install FreeType (Linux)`, `Install C tools (Linux Cranelift)`, and `Install exact LLVM authority (Linux LLVM)` from `.github/workflows/rust-bootstrap-multiplatform.yml` (lines ~372-380) with mocked sudo/apt, a fake installer, and a fake toolchain; verifies the pin helper publishes `LLVM_SYS_231_PREFIX`, the Cranelift apt deps (libfreetype6-dev, libunwind-dev, clang-18, lld-18, llvm-18-dev) are requested, and seven single-element removals are each rejected.

Note: the named check is pure sh+embedded-python and does not invoke the Simple CLI; the phase1 snapshot binary substitution for `bin/simple` was not required for this check.

Sanity-confirmed in worktree: `scripts/setup/install-linux-phase23-llvm23.shs`, `scripts/check/pin-linux-phase23-llvm23.shs` exist and the workflow references them; workflow YAML unchanged.

Scope note: this verifies the workflow wiring/fixture level only; the real ~2 GB LLVM 23.1.1 archive download, installation, and full native bootstrap execution remain unexecuted (as the doc already records).
