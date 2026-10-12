# Cranelift Result match ghost witness abort

Status: source repaired; rebuilt-compiler behavioral verification pending.

The Stage 2 compiler matrix failed `src/app/_cg/f07/main.spl` with worker
SIGABRT (-134). The admitted compiler digest was
`041e685fdbb0bb24eeec571a28d8bea57537909cd642116372bf4a8407fce1c8`,
source snapshot digest `943290180a3f49edceb9dd8738ca1fbfc74c1d67d212416643779fb7a61178be`,
runtime snapshot digest `9d133448d05c36ee56e5f5d5f8aeb48bcaf21b47844a3d55a15716c3fa55ac9b`.
The retained matrix receipt is
`/mnt/wsl/simple-dbc-native-recovery-20261012/build/ice/200671_4266603401317398814/ice_receipt.tsv`.

A bounded reproduction using the admitted pure-Simple runtime capsule and
`native-build src/app/_cg/f07/main.spl --emit-object --backend=cranelift --threads 1`
reported `E-BACKEND-CRANELIFT-INST-ResultMatchSemantic` before object emission.
The debugger initially followed an auxiliary `uname` child and yielded no
backtrace; its retained log is `/mnt/wsl/dbc-result-abort-gdb.log`. This is
diagnostic evidence, not a passing build or complete backtrace.

`MirInstKind.ResultMatchSemantic` is explicitly a verification-only witness
with no runtime effect. Match lowering already emits discriminator branches,
payload extraction and merge copies before appending it. LLVM and native x86
backends already erase this ghost marker. Cranelift lacked the corresponding
arm and reached its unsupported-instruction panic.

The repair adds that explicit arm without changing Result representation,
try propagation, executable branches, or the default rejection of unsupported
instructions. `test/fixtures/compiler/cranelift_result_match_try_witness.spl`
checks both successful payload arithmetic and the exact propagated error.
Run `sh scripts/check/check-cranelift-result-match-try-witness.shs COMPILER OUTPUT_DIR`
using the rebuilt pure-Simple compiler and its admitted runtime capsule.
The regression is NOT_RUN until that compiler exists.
