# FreeBSD CI Rust tests killed after a successful bootstrap build

## Evidence

In [Rust Bootstrap Multiplatform run 36465343947](https://github.com/ormastes/simple/actions/runs/36465343947), FreeBSD job 109074434770 built `simple-driver` with the bootstrap profile in 9m 00s. The next command, `cargo test --workspace --lib`, was still compiling workspace test targets when the VM action printed `Killed` and reported `ssh exited with code 137` at 2026-09-28 18:57:51 UTC. Its log contains no Rust compiler error immediately before the kill. Exit 137 establishes SIGKILL of the command path; the log does not prove whether guest or host memory pressure caused it.

The workflow leaves Cargo build concurrency and the Rust test harness thread count at their CPU-derived defaults inside the FreeBSD VM. The VM action documents 6144 MB as its default guest memory. Running fewer simultaneous compilers and test threads is a bounded attempt to lower peak memory without omitting workspace libraries or tests.

## Change and verification

On release source `42ea10e42a899f1dc58d60e76c8de076add0ede3`, limit the FreeBSD command to `cargo test --workspace --lib -j 1 -- --test-threads=1`. Cargo documents that `-j` limits build jobs and `--test-threads` controls the test harness separately. The workflow continues to build `simple-driver` and run all workspace library tests.

This local workflow change has syntax and diff checks only. A new GitHub FreeBSD job on this exact patch is required to determine whether it resolves exit 137. The separate local full QEMU bootstrap remains unqualified after its three-run cap and two-hour Stage 2 timeout.

## Full bootstrap blockers outside this CI command

The `--full` QEMU wrapper currently resumes Stage 4 directly, without the scheduler lineage admission now required by `bootstrap-from-scratch.sh`. The bootstrap engine also limits Stage 4 full CLI capsule preparation to Linux and macOS. A FreeBSD full bootstrap needs a scheduler-mediated lineage and actual FreeBSD Stage 4 support before the wrapper can qualify it; removing either guard without implementation would only hide a missing authority or platform capability.
