# SimpleOS and RISC-V Evidence

[Back to the project showcase](../../EVIDENCE_SHOWCASE.md).

Status is generated from validated manifests; missing manifests cannot become a
live claim.

<!-- evidence-showcase:generated:start -->
## Generated evidence status

Status is derived from validated manifests. Missing manifests resolve only to `contract-only` or `planned`.

| Status | Count |
|---|---:|
| `live-pass` | 0 |
| `historical-pass` | 0 |
| `contract-only` | 3 |
| `blocked` | 2 |
| `unsupported` | 0 |
| `planned` | 0 |

## Critical capabilities

| Capability | Status | Claim boundary | Target | Proof | Resume |
|---|---|---|---|---|---|
| Ordered RISC-V Linux boot login and shell transcript | `blocked` | missing-prerequisite:build/os/buildroot/rv64/buildroot-manifest.txt | qemu-riscv64 | [manual](../../doc/06_spec/03_system/os/evidence/linux_riscv_qemu_login_evidence_spec.md) · [spec](../../test/03_system/os/evidence/linux_riscv_qemu_login_evidence_spec.spl) | `sh scripts/os/build&#95;riscv&#95;buildroot.shs rv64 &amp;&amp; RISCV&#95;ARCH=rv64 sh scripts/os/build&#95;riscv&#95;linux&#95;assets.shs --all &amp;&amp; sh scripts/os/check&#95;riscv&#95;linux&#95;qemu.shs rv64` |
| Ordered SimpleOS boot login shell and command transcript | `blocked` | missing-prerequisite:build/os/simpleos&#95;riscv64.elf | qemu-riscv64 | [manual](../../doc/06_spec/03_system/os/evidence/simpleos_rv64_login_evidence_spec.md) · [spec](../../test/03_system/os/evidence/simpleos_rv64_login_evidence_spec.spl) | `bin/simple os build --scenario=riscv64-smoke &amp;&amp; SIMPLE&#95;EVIDENCE&#95;SIMPLEOS&#95;RV64&#95;LOGIN=1 bin/simple test test/03&#95;system/os/evidence/simpleos&#95;rv64&#95;login&#95;evidence&#95;spec.spl --mode=interpreter --timeout 120` |
| SimpleOS dynamic HTML page insert query and refresh flow | `contract-only` | Executable contract exists; no validated evidence manifest | — | [manual](../../doc/06_spec/03_system/os/evidence/simpleos_qemu_dynamic_db_page_evidence_spec.md) · [spec](../../test/03_system/os/evidence/simpleos_qemu_dynamic_db_page_evidence_spec.spl) | — |
| Current-source SimpleOS QEMU WM event and keyframe correlation | `contract-only` | Executable contract exists; no validated evidence manifest | — | [manual](../../doc/06_spec/03_system/os/wm/simpleos_wm_fullscreen_spec.md) · [spec](../../test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl) | — |
| Physical ARM SimpleOS Clang filesystem hello-world execution | `contract-only` | Executable contract exists; no validated evidence manifest | — | [manual](../../doc/06_spec/03_system/os/evidence/simpleos_physical_arm_clang_hello_evidence_spec.md) · [spec](../../test/03_system/os/evidence/simpleos_physical_arm_clang_hello_evidence_spec.spl) | — |
<!-- evidence-showcase:generated:end -->

Next implementation evidence is specified in the
[system-test plan](../../doc/03_plan/sys_test/evidence_showcase.md).
