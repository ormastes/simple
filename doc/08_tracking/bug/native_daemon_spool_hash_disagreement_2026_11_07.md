# Native daemon spool path hash disagrees within one executable

Status: OPEN, report-only (not registered in bug_db). Proposed priority P1.
Group: compiler/runtime; attribution between lowering, inlining and runtime remains unproven.

Observed on aarch64 Linux using unadmitted pure-Simple compiler SHA256
`afae09d224390a57d675a128a052626c3aa665c032481928332ebdc2859d7350`.
Source base: `662c9c4fe01b07f3712faeccab945ee69fcd889c`, plus the daemon
publication regression fixture and envelope-admission guard in this PR.

Reproducer: `test/fixtures/daemon_sdk/publication_regression.spl`, selection
`success`. It uses the real request writer, runner and checked acknowledgement.
Expected: successful response publication removes the same request path.
Observed: response is published, acknowledgement attempts a different path,
and the success assertion fails. Do not weaken the expectation.

Syscall evidence from `build/daemon-publication-native/deletion.trace`:
- Request write/rename: `requests/0_3875265_1794017034495863.req`.
- Response write/rename: `responses/3875265_1794017034495863.resp`.
- Acknowledgement unlink: `requests/-8547548619830576675_3875265_1794017034495863.req` returns `ENOENT`.

All request paths use `daemon_request_path_for`, which calls `hash_text`.
The same request identity must hash consistently at writer, reader and cleanup
call sites. The trace establishes disagreement; it does not prove which
compiler or runtime function caused it. No compiler repair was attempted.

Related historical symptom: [cross-lane hash disagreement](rt_hash_text_cross_lane_disagreement_2026-09-07.md).
That report concerns older lanes and remains historical evidence; this is a
fresh within-executable observation, not proof its original cause returned.

Build: LLVM, `core-c-bootstrap`, entry closure, one thread,
`SIMPLE_NO_STUB_FALLBACK=1`; build exited 0, fixture exited 1.
The diagnostic compiler is not admitted. Admitted SSpec and runtime gates are
BLOCKED; this report does not certify a production regression or a repair.

## Argument representation audit, 2026-11-07

One new bounded GDB observation used the retained `program-v3` executable,
SHA256 `62b0b1cb21cf4136647b062c3f39629413af4ee7178b0688ac3411860a6d5b5a`.
Command: `timeout 30 gdb -q -batch -x hash-arguments.gdb program-v3`, with
`run success` and a breakpoint at `rt_hash_text`. The inferior exited 1 at
the unchanged successful-acknowledgement assertion; no source was rebuilt.

All three calls received the same bytes `42656_1794027161092870`:

| Call | Argument | Low tag bits | Representation |
|---|---|---|---|
| 1 | `0xaaaaaabe9b90` | 0 | Raw C string |
| 2 | `0xaaaaaabec320` | 0 | Raw C string |
| 3 | `0xaaaaaabf01f1` | 1 | Tagged string, bytes at untagged pointer +16 |

Each stack was `rt_hash_text` ← `io_runtime.hash_text` ←
`daemon_request_path_for`. Disassembly shows the Simple hash wrapper forwards
its argument directly. The linked hash function requires a tagged string and
returns zero for rejected raw pointers. This identifies the first failing
boundary as inconsistent text representation entering the strict runtime hash
decoder; the SDK uses one path algorithm throughout.

The upstream producer of the mixed representation still needs isolation.
Do not replace the SDK hash algorithm or label an extern char-pointer bridge
as the proven cause: this executable's wrapper has no such bridge. A compiler
repair must cover computed/interpolated text, stored request fields and decoded
request identities without relaxing expected successful acknowledgement.

Evidence: `/home/yoon/dev/simple-daemon-exact-lock-owner-20261107/build/daemon-hash-audit-20261107/`
contains `hash-arguments.gdb` and `hash-arguments.log`. This diagnostic is not
admitted-toolchain qualification and does not resolve the open bug.


## Canonical interpolation producer repair candidate, 2026-11-07

Source audit at base `5854838c6124cfa9deb6c0d985814dd9db8bfe0e` identifies
`MirLowering.lower_string_interpolation` as a raw text producer: it unwraps
all operands with `bootstrap_coerce_to_raw_str` and concatenates with
`rt_strcat`, returning the raw pointer as language text. This explains how
computed request identities can reach the strict hash decoder as raw pointers
while decoded file text is tagged. Native confirmation of the patched producer
is still required; the existing trace alone does not prove all producers.

The candidate changes only the interpolation producer. Literal segments use
`rt_string_new` with a raw byte pointer and explicit byte count; rendered
operands retain their existing scalar dispatch through `coerce_concat_operand`.
`rt_strcat_tagged` preserves operand lengths and returns owned tagged text.
The MIR local is recorded as tagged. Runtime decoders, provider hash algorithms,
SDK path selection, and raw-pointer APIs remain unchanged.

Regression: `test/fixtures/compiler/native_interpolation_text_hash_boundary_main.spl`.
It checks a computed identity, struct/array storage, file serialization and
substring decoding against a nonzero known hash and every expected byte. It
also checks embedded NUL in both literal segments and interpolation operands,
Unicode bytes, and integer/bool/float formatting. Run the native executable in
a private working directory because it writes one temporary SDN file.

Validation so far: `git diff --check` PASS. No compiler build or executable
regression was run: the root owns native build slots. This is a source repair
candidate, not an admitted verification PASS or a claim that the daemon fixture
now succeeds. The cause repair budget is not reset by this isolated worktree.

Affected real compiler pipeline regression
`test/01_unit/compiler/backend/numeric_interpolation_abi_spec.spl` now follows
renderer SSA words through the ABI `inttoptr` into tagged concat and checks
counted constructor length SSA for NUL/Unicode prefixes. The old assertion of
raw concat was intentionally updated to the repaired representation contract.
Its companion manual was updated without fabricating execution evidence.
The native probe also covers Unicode in a literal segment, independently of
Unicode supplied as an interpolation operand. These executable checks remain
pending native-slot/toolchain validation.

Static pre-commit gates: direct-env-runtime-guard `--working` and `--staged`
PASS; existing numeric scalar ABI shell contract PASS; staged whitespace check
PASS; executable spec files under `doc/06_spec` count `0`. No executable compiler
pipeline or native probe PASS is claimed by these static checks.
