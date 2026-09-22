# Stage2 lexer optional environment save traps on its disabled path

Date: 2026-09-22. Base: `0e3f5af9d5651b16c0cfc0f46d73aa9b22e30456`.
Status: targeted native regression PASS; independent Astra review PASS; rebuilt
Stage2 admission pending.

## Cause and scoped fix

Stage2 compiled 899 modules, then positional hello-world admission crashed with
SIGILL/132 after entering parse. Crash report
`simple-2026-09-22-220621.ips`, incident
`4D1E6A9F-9014-4510-BB14-D7C234176216`, names
`compiler__frontend__core__lexer__current_core_lexer_save+1168`.
The rejected compiler SHA-256 is
`141ad185697d0a5f91673a42f28edb69599abb4ebc3cba874642c052ceedcf45`.
It remains preserved under the parent worktree's
`build/bootstrap/macos-enforced-bd544-stage2/stage2/aarch64-apple-darwin/simple.rejected`.

The helper has an early bare return when environment saving is disabled and a
terminal `env_set(...)` call, whose declared result is `bool`. Without a return
annotation, the bootstrap producer's `hir/lower/module_lowering/function.rs`
selects `TypeId::ANY` for a body ending in a value-producing expression.
`codegen/instr/body.rs` intentionally traps on a valueless return from a
nonvoid function. Rejected-binary disassembly shows the disabled branch at
`0x1001119a4` jumping to `0x100111c60`, `udf #0xc11f` (+1168).

Declare the side-effect-only helper as `-> ()`. This establishes its actual
contract; it neither fabricates a result nor disables the backend trap. Token
advancement, owner-slot rebinding, optional environment writes, and runtime
ownership remain unchanged. The final `env_set` boolean is intentionally unused.
This is related to the preceding progress-helper return trap, but does not
involve wildcard binding: this helper directly ends with the boolean call.
General inference/diagnostics for incompatible bare and value returns remain a
compiler follow-up, outside this focused pure-Simple fix.

## Native regression and evidence

Worktree: `/Users/ormastes/simple-tmp/macos-stage2-lexer-save-20260922`.
Evidence: `build/native_probe/lexer_env_save` within that worktree.
Fixture: `test/fixtures/native/lexer_optional_env_save.spl`, importing the real
lexer and environment facade. Its 53-module native closure checks all token
kinds/text/line/column values for `alpha(beta)\ngamma`, EOF, saved position,
line/column, both line-start values, open/closed parenthesis depth, pending
dedents and the current indent wire value. Disabled saving must leave the
initial saved fields intact while the in-memory token stream still advances.
Comparison failures print a diagnostic and exit 1 through the existing facade.

Before changing the helper, the native fixture exited 132 with the environment
flag unset; flag `1` passed all checks. After the annotation, independent
processes with unset, empty, `0`, and `1` all exited 0 and printed exactly
`lexer-optional-env-save-pass`. `green-save.disasm` contains normal returns for
both paths and no `udf` instruction in the helper.

The initial fixture's plain `assert(...)` did not link in `core-c-bootstrap`
(`_assert` undefined). Explicit checked comparisons plus `std.io_runtime.exit`
make the fixture executable with the existing core ABI, without adding runtime
symbols or stubs. That initial failed build is retained in `red-build.log`.
This is a concrete native assertion-surface limitation, not a regression result.

This is a **bootstrap-only focused native build**, using the exact frozen
producer/runtime authority from the failed Stage2 build. It is not production
self-hosted verification or Stage2 admission. Producer SHA-256:
`3ff20095e350af7f0b5cc150fd59872b073955eced1e10f3e264ca4a1e37c0a6`.

Reproduction (red uses the base helper; green uses the annotation):

```sh
authority=/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-runtime-authority
probe_dir=build/native_probe/lexer_env_save
probe_name=green
perl scripts/resource/process-tree-rss-watchdog.pl \
  --max-rss-kib=5859375 --interval-ms=100 --timeout-seconds=180 \
  --receipt="$probe_dir/$probe_name-build.rss.env" -- \
  env SIMPLE_BINARY="$authority/simple" SIMPLE_NATIVE_BUILD_RUST=1 \
    SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 \
    SIMPLE_PACKAGE_INDEX_COLD_INIT=1 SIMPLE_LIB="$PWD/src" \
    SIMPLE_LLVM_BIN=/opt/homebrew/Cellar/llvm/23.1.1_1/bin \
    /usr/bin/time -l "$authority/simple" native-build \
    --backend cranelift --runtime-bundle core-c-bootstrap \
    --runtime-path "$authority" --source src/compiler --source src/lib \
    --entry-closure --threads 2 --cache-dir "$probe_dir/cache" \
    --mode one-binary --entry test/fixtures/native/lexer_optional_env_save.spl \
    --output "$probe_dir/$probe_name" >"$probe_dir/$probe_name-build.log" 2>&1
env -u SIMPLE_BOOTSTRAP_LEX_ENV_SAVE /usr/bin/time -l "$probe_dir/$probe_name"
env SIMPLE_BOOTSTRAP_LEX_ENV_SAVE= /usr/bin/time -l "$probe_dir/$probe_name"
env SIMPLE_BOOTSTRAP_LEX_ENV_SAVE=0 /usr/bin/time -l "$probe_dir/$probe_name"
env SIMPLE_BOOTSTRAP_LEX_ENV_SAVE=1 /usr/bin/time -l "$probe_dir/$probe_name"
```

The successful red build is named `red-fixed-fixture-build.log` to distinguish
it from the original fixture's link failure. The private cache was retained;
both successful builds report 53 compiled, 0 cached, 0 failed.

| Measurement | Red | Green |
|---|---:|---:|
| Build wall time | 8.36 s | 9.20 s |
| Peak sampled process-tree RSS | 316,800 KiB | 328,352 KiB |
| Enabled-run maximum RSS | 9,437,184 bytes | 9,388,032 bytes |
| Enabled-run wall time (coarse timer) | 0.00 s | 0.00 s |
| Observer errors / restarts | 0 / 0 | 0 / 0 |
| Quiescent | 1 | 1 |

Green unset first launch was 0.34 s with 9,371,648 bytes max RSS. Empty/0/1
launches were 0.00 s at the timer's resolution, 9,355,264–9,388,032 bytes max
RSS. Builds are below the unchanged 5,859,375 KiB cap and 1 GB ordinary target.
These short samples do not establish a speedup or statistically significant
regression. The annotation adds no loops, allocations or I/O and removes
boxing of the unused boolean result.

Native fixture SHA-256:

- Red: `7f39b2767ae31d06d10b19daa459c4cdf82bcc32da39392c503d599f4eb7e9d4`.
- Green: `1f7f03f54848fc0b63f2857a073763423146d88a91dbbafb678abc97d32b97ab`.

Source SHA-256:

- Base lexer: `e274fa7539a5c1b8c08e05d4c4731538017abf8e3df472be151fbe7e25caf3f1`.
- Fixed lexer: `9fe06c5b639508aef82e575600d116327fc5f512458fc3ddb2031aae6821de2f`.
- Fixture: `a091fadce027f1a94a731db34cb81ae2205a1579855e05b564d4383eddc49ab3`.

Independent Astra review PASS, no blocking findings: the unit contract matches
both callers, all saved-state side effects are preserved, the native regression
assertions are meaningful, and hashes/resource evidence match. Review scope
explicitly excludes rebuilt Stage2 admission. Whitespace, working/staged
direct-env runtime guards and the zero-executable-spec layout gate pass.

## Remaining boundary

The parent bootstrap lane must rebuild Stage2 and rerun admission with its
existing dynload policy, ownership pins and memory observer. This isolated
worktree has no deployed `bin/release/aarch64-apple-darwin/simple`; full compiler,
library and MCP checks and native MCP smoke require an admitted self-hosted
runtime. They are not replaced by seed runs. No full bootstrap, deployment or
push was performed here.
