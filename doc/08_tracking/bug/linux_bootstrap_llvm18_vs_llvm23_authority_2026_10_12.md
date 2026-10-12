# Linux native bootstrap CI provisions LLVM18 against LLVM23.1 contracts

Status: OPEN; source and focused fixtures qualified, real installation/bootstrap pending.

Actual Linux diagnostic38162989607 stopped at runnerfixture preflight. Independent source mismatch: native workflow installs LLVM18+Polly18 while compiler Cargo.toml requires llvm23-1-force-static on non-Windows. Local primary apt metadata only offers23.1.2; the generic major23 installer cannot provision exact23.1.1 and is not used by this candidate. Official LLVM release metadata provides LinuxX64 archive2014958380bytes SHA256832aeb58d105de1cabc7b982dd2c65de0610f7377df48ae8fc2dd8e97420a15c. Exact tag resolves signedreleasecommit6dfe1677ab8dffbc6ec13d53a1e0215d75147689.

Dedicated installer uses gh release download to bounded temporary storage; validates size/digest before inspecting or extracting; requires sufficient measured expansion disk; cleans staging on failure. Immutable archive cache is keyed by digest and rehashed each use. Only pin helper publishes environment after actualtoolversions/prefix/Rust all agree at23.1.1. LinuxCranelift retains clang18/lld18/llvm18dev. DatedRust action matches reviewed toolchain-file pin2ee1f60, required in diagnostic integration.

Focused evidence: one valid toolchain binding +8negativecases PASS; actual selected workflow commands with isolated package/installer fixtures +7negative removals PASS; corruptarchive size and realSHA rejection precede extraction PASS. Archive-size precondition alone is mocked for digest-negative test; real2GBdownload/installation and compilerexecution remain UNEXECUTED. Evidence /mnt/c/Temp/simple-linux-llvm23-toolchain-20261012. Previousrun remains immutable.

Other platforms remain unqualified: nativeMac multiplatform still llvm@18/LLVM_SYS_180_PREFIX; dedicatedMac23.1.1job separate. Crossarchitecture LLVM18reader/setup and Windows contracts are not qualified by this change. LocalLLVM23.1.2 remains untouched.

Official archive Polly/PollyISL and static LLVM availability is unexecuted. Installer requires those archive-owned libraries before publication; no floating apt Polly may be mixed. Native Mac multiplatform and cross-platform LLVM18 contracts remain outside this Linux candidate.
