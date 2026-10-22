# Native command symlink rejected during seed fingerprint

Status: CLAIMED by distributed-control runtime recovery. Owner: scripts/check/lib/bootstrap-stage3/authority.shs, bootstrap_stage3_canonical_native_command.

Reproducer: source authority.shs and call bootstrap_stage3_canonical_native_command /usr/bin/llvm-config-23. Before fix: exit 1. Tool is installed: physical /usr/lib/llvm-23/bin/llvm-config, version 23.1.2. Fresh canonical bootstrap stopped with seed fingerprint cannot canonicalize llvm-config.

Cause: the PATH-selected native command resolver reused the receipt artifact helper's intentionally strict symlink-leaf rejection. Installed system-tool aliases need physical executable resolution; receipt-named compiler artifacts still forbid symlink leaves. Fix belongs to bootstrap authority shell owner, not Rust compiler or runtime.

Change: resolve an executable regular-file target through Cwd::abs_path; normalize any returned Windows native spelling, then apply canonical-file validation. Dangling aliases, cycles and nonexecutables fail closed. Receipt canonicalization is unchanged.

Verification and landing pending. Exact/adjacent fixtures must cover installed llvm-config, relative aliases with spaces, cycles, dangling and nonexecutable targets, and unchanged artifact alias rejection.

## Focused verification

PASS: sh scripts/check/check-bootstrap-native-command-alias.shs exercises relative native aliases, chained links and paths with spaces, plus artifact-alias, dangling-link, cycle and nonexecutable rejection. The exact installed llvm-config selection now resolves to /usr/lib/llvm-23/bin/llvm-config (exit 0). Native Windows execution NOT_RUN; full bootstrap retry and landing pending.
