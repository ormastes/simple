# Staged canonical Windows downstream: P3a -> P3b -> P4

This replaces the earlier split-entry P3a-to-CLI proposal with the explicitly
requested independent production release sibling described below. The actual
Phase3 parent pin remains null until verified.
The source stays exactly93f7; the wrapper checkout is separately hash-bound to
PR11275 merge ed9c404d, with its reviewed topic head also recorded. Its helper/config
bytes are recorded and rechecked, never copied into frozen source.

The first hosted job consumes only verified Phase3a job138350557255 in
run45366816359/control4e69b62fcfa. It verifies actual archive, source/runtime/tool
ancestry, Windows owner/cap, complete product companions and genuine native Hello.
It runs canonical --phase=p3b --p3a-bin=<actual> --p3a-sha256=<actual>, file/MinGW,
LLVM/threads2, fresh build root and the matched runtime. No P3a rebuild or new
P3a Hello occurs. New output is phase3-b/simple.exe and its canonical native Hello.

The dependent hosted Phase4 job consumes that same-run uploaded artifact ID,
checking API run/head/name/digest plus actual bytes and complete P3b qualification.
Only then it runs canonical --phase=p4 --p3b-bin=<actual>, preserving all wrapper
source roots, CUDA policy and products: release/debug CLIs and four essentials.
Canonical release entry is src/app/cli/main.spl, which exports main_and_help;
the prior early product used src/app/cli/_CliMain/main_and_help.spl directly.
This product/config distinction is recorded. Canonical P4's intrinsic producer
Hello gate stays intact; no extra external parent Hello is added.

Existing retained behavior checks run on the actual canonical release executable
p4-from-p3b/bin/simple.exe: version/help, exact run output, positive1/0 and
negative0/1 tests, then actual LLVM native Hello. There is no second CLI build.
Three tracked qualification fixtures are staged before first SCV; smoke caches,
storage and temp are distinct from the compiler generation. All outputs/companions
and original source/runtime/tool/wrapper identities are rechecked.

Each runner independently samples75% physical/commit available with2GiB reserve;
real worker estimates/admission remain unchanged, disk is measured without an
invented fixed floor. P3b owner18000s, P4 owner16200s, each job350minutes leaves
bounded intake/qualification/upload time. Full canonical P4 may not finish or fit;
no product is skipped or claimed from another cohort. Terminal failures and exact
receipts remain evidence. Outputs are provisional; no formal admission/deployment.

No dispatch, parent reexecution or native test occurred while staging these
controls. Final actual-parent/wrapper binding review is required before sole use.

Final parent binding: run45366816359/job138350557255/control4e69b62fcfa, artifact windows-93f7-phase3-retained-45366816359. The original failed run45357104625 is not accepted. phase3_parent remains null until actual artifact/PE/Hello pins are verified. Wrapper is landed mergeed9c404d, compiled source remains93f7. No dispatch until root confirms verified parent.

## Requested parallel Windows DAG

The identical verified final P3a starts independent hosted sibling jobs: P3b and direct-P4 release CLI. Each uses a one-role matrix with fail-fast:false; direct-P4 has no needs edge to P3b. The direct product uses supported native-build with the exact landed canonical release entry/configuration (main.spl, CUDA-disabled source, LLVM/GNU dynload prod/release/strip, two threads and Stage4/file-worker policy). It records producer_generation=P3a; it does not pass P3a as --p3b-bin or claim canonical P3b lineage. Release CLI behavior is tested on that actual executable. It builds no duplicate debug/tools or equivalent same-parent CLI.

The later canonical P3b-to-P4 job still needs only genuine successful P3b and builds the canonical release/debug/essentials bundle using that next compiler. Its release CLI gets its own behavior verification. All three jobs are Windows-native with independent resources/caches. Original parent pins remain null: no dispatch until verified real parent and root confirmation.
