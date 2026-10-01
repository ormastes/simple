# Linux Stage 2 bootstrap reports an AVX-512 owner routing error

Status: open. Observed on WSL Ubuntu 22.04 at source `12b26fb1306` on 2026-09-28.

The Linux `--backend=cranelift --mode=dynload --full-bootstrap --stop-after-stage2` run built and linked a 35,544 KB Stage 2 pure-Simple compiler (`1015 compiled, 0 failed`, 738.4 seconds). Its required hello-world frontend smoke then exited 134 with `non-SIMD instruction reached AVX-512 instruction owner`. The bootstrap rejected and preserved that candidate; no Stage 2 receipt or later stage is admitted.

Evidence: `build/bootstrap/windows-linux-20260927/linux/console.log`, `logs/x86_64-unknown-linux-gnu/stage2-native-build.log`, `stage3/x86_64-unknown-linux-gnu/stage2-sanity.env.frontend-failure.log`, and `stage2/x86_64-unknown-linux-gnu/simple.rejected` in `/home/ormastes/simple-multihost-bootstrap-main`.

The owner panic is in `src/compiler/70.backend/backend/native/x86_64_avx512_lower.spl`. The exact MIR variant reaching that panic has not been captured. `x86_avx512_handles` already rejects empty shape maps and has separate pattern arms. An experiment at `12b26fb1306` also added an explicit nonempty-shape guard and replaced the conditional expression in `isel_block_with_x86_simd`; the same smoke still panicked. That experiment is excluded from the proposed fix branch because it did not solve the failure.

Next investigation: capture the MIR instruction variant and planned AVX-512 shape count at the `isel_avx512_frame_inst` call in the self-hosted Stage 2 compiler; compare with the Rust seed's behavior on the same hello-world fixture. Add a scalar hello-world regression to the owner routing tests and rerun a fresh Stage 2 admission before proceeding to Stage 3. The session retry cap was reached, so no further retry was made here.

Related: [AVX-512 native remaining limits](avx512_native_remaining_limits_2026-09-10.md).
