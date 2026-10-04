# Self-hosted CI provisioning lacks LLVM prerequisite

After PR2405 repaired the missing bin/simple setup, GitHub jobs reached the actual bootstrap prerequisite check and failed before executing tests. Path Normalization job111346295691/run37171874846 and cache-promotion job111346296026/run37171874874 report that admitted LLVM23 is not installed. This is not a failing path-normalization assertion or cache-promotion test.

Provision the same reviewed LLVM23.1.1 Linux x64 archive used by aot-lane-fences, with SHA256832aeb58d105de1cabc7b982dd2c65de0610f7377df48ae8fc2dd8e97420a15c, verify its version/tools, and export its prefix through GitHub environment/path files. Both consumer jobs select an explicit x64 hosted runner and nightly Rust before the shared bootstrap provider. The Rust seed remains bootstrap-only.

Local validation covers shell syntax and workflow prerequisite ordering, including missing and late LLVM setup rejection. Actual Linux installation and full hosted bootstrap remain unrun locally on this Windows host. No release admission is implied.