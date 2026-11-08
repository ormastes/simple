# LLVM bootstrap text byte_len dispatch prerequisite

Status: source repaired; independent source review approved; compiler/runtime verification pending.
This is the explicitly authorized narrow Rust bootstrap-host prerequisite
exception. No Simple language implementation or existing caller is changed.

## Confirmed peer failure and shared source gap

The peer bootstrap at `D:/dev/wt/boot-r14` recorded source commit
`880c5975bd7286f5660aa3d11cbd60370357aed8`, dirty-source fingerprint
`8e0a2e69a754fa0506fe12689fd7db4375b34da53a3c53c0ba25144831d2b62f`,
and executed published seed SHA256
`f3ae8e7a60b26aa42e6f42cd81824dcc9f69f635ed8b69d1fef180c9b94ed68d`.
Its retained stage2-native-build.log reports unresolved `str.byte_len` across
string-core, SDN and buffer consumers. Initial command:
`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2`.
Exact native-build argv remains in that owner's stage2 command transcript.

Bootstrap owner audit:
`D:/dev/simple-node-attribute-bootstrap-20261106/build/node-attributes-qualification/byte-len-prerequisite-audit.sdn`.
Peer log:
`D:/dev/wt/boot-r14/.simple/storage/build/bootstrap/logs/x86_64-pc-windows-msvc/stage2-native-build.log`.
The audit binds the peer and own frozen 7ffb05cc LLVM functions.rs to the same
SHA256 `c7eb9d5621f4d0a25e74028309ed3d3037fce151cc000ef62e9a669914d858e4`,
which lacked a byte_len dispatch entry. The Rust Cranelift dispatcher already
maps byte_len to rt_string_len. The own 7ffb05cc closure has **not** exhibited
this failure; shared owner bytes establish a source gap, not an observed own
bootstrap failure or proof that the own closure reaches that path.

## Repair boundary

Repair checkout: `D:/dev/simple-byte-len-prerequisite-20261107`, based on latest
fetched release commit `b37cca889050455644210376e8a9706cd617f0e5`.
Baseline functions.rs Git blob: `d1fa4d4c12ec6ca6d63f47d489c897a735dc57d9`.

Qualified ordinary calls, static method calls and explicit builtin-method
MIR now recognize byte_len for str/text/String/string. Qualified calls also
accept the existing canonical string-core owner and `_dot_` spelling. The
selected existing ABI is exactly `rt_string_len(i64 receiver) -> i64`, which
counts UTF-8 bytes. Wrong arity and proven nontext receivers fail closed.
Unrelated qualified user methods keep their exact callee; no bare-name
byte_len shortcut is introduced.
Nontext guards recognize exact builtin owners, preserving namespaced user
owners such as `User__String` and `custom.str` rather than stripping namespaces.

Existing len and char_count dispatch remain unchanged. This repair does not
rewrite language callers to len, alter codepoint semantics, or claim to
qualify any pre-existing length behavior beyond preserving those routes.
No runtime/provider or active bootstrap source/cache/lock is changed.

## Regressions and verification limits

Five Rust tests in llvm/functions.rs materialize and verify LLVM IR for all
text aliases and dotted spellings, all three MIR call routes, exact runtime
ABI, malformed arity, nontext receivers, unknown methods, direct user-method
precedence, unchanged len/char_count routes, and actual parsed source.

`test/fixtures/native/text_byte_len_dispatch/main.spl` supplies four runtime
assertions: UTF-8 byte length 6 versus codepoint count 2 for `é🙂`, ASCII length
3, and empty length 0. These runtime assertions are authored, not executed.

Whitespace checks passed. No Cargo build/test, seed execution, Simple suite,
or native fixture execution was started in this repair lane. Rust IR tests
remain unexecuted pending an independently owned toolchain/build; they are
bootstrap-host tests, never a substitute for admitted self-hosted Simple
tests. The active 88237 build and other owners' Cargo targets remain untouched.
Source review and landing do not qualify a rebuilt seed or bootstrap. Replay
requires new immutable producer/source/runtime identities and retained results.

## 2026-11-08 note (lane-f-p2helper): frozen pure-Simple stage2 side, plus `fill_span`

Rebuilding the Phase 2 subsystem helpers with the frozen stage2 `stage2.ef0681fc0e1.exe`
(source 2026-10-27) on `release/1.0.0` @ `01a8acae210` fails MIR with
`unresolved method call: byte_len` at 45 (generator) / 36 (verdict) sites and
`unresolved method call: fill_span` at `src/lib/common/crypto/secure_memory.spl:57,78,94,106`.
Neither method name occurs in `src/compiler` at `ef0681fc0e1`; both arms landed 2026-11-07
(`4183b795175`, `f680394dddf`). Any producer frozen before 2026-11-07 therefore cannot lower
current `src/lib`; this is a producer-vocabulary gap, not a receiver-type one. Evidence:
`doc/08_tracking/bug/phase2_subsystem_helper_mir_failures_2026-10-05.md` § 2026-11-08.
