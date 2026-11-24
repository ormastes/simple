# Staged Windows 93f7 Phase3 and early full CLI

The actual native Windows proof is now bound in `handoff.json`: run45353936171,
control276251ef, artifact14903265381, with full ZIP/compiler/Hello hashes and size.
Its upstream same-run `binding.json` is retained alongside the controls. Final
binding review is required before the one authorized temporary dispatch. The
existing registered `bootstrap-sanity-evidence.yml` is used only on this work ref.
No compiler
or native Hello is repeated for the parent: the controller verifies the retained
proof and reconstructs identical bytes from its immutable artifact/package pins.

The matrix schedules Phase3 and early full CLI on separate Windows runners with
fail-fast disabled. Each independently verifies the same qualified Phase2 tuple;
neither reruns the parent's native proof. Early CLI is explicitly Phase2-produced,
not true Phase4. Its full accepted source scope/prod/dynload entry is preserved,
with the supported single low-memory worker and batch4. Three exact staged test
fixtures exist before SCV initialization. The resulting executable must pass
version/help, exact run output, positive1/0 and negative0/1 tests, and its own LLVM
native Hello. Smokes use separate product-generation storage/cache and bounded
owners. No resource reservation or failure in one runner affects the other.

True Phase4 remains dependent on genuine Phase3 plus its retained Hello; it must
never consume the early result as a substitute. Existing provisional Windows
full-CLI machinery can reuse this product/smoke slice with a reviewed new Phase3
artifact intake, but the f6f7 and Linux lineage gates are not rebound here. No
duplicate true-Phase4 controller or automatic dispatch is created.

The untouched 93f7 standalone owner builds Phase3a using the actual Phase2 PE,
GNU ABI, LLVM, file compilation and two workers, then executes its own candidate
Hello. This is provisional, not scheduler admission or a Phase3b/fixpoint claim.
The runner independently admits min(75% available physical/commit memory,
available minus 2GiB). No product-specific 10GiB minimum is asserted: the actual
canonical two-worker policy retains its estimates/coordinator reserve and can
refuse the measured budget. Its supported host reserve is explicitly the same
2GiB retained by the outer admission. Available output-volume disk is recorded;
this standalone entrypoint has no fixed disk floor, and actual I/O failures remain
fatal rather than being converted to success. The outer real
Windows Job has a finite five-hour deadline, and the workflow has 50 minutes
additional intake/upload allowance. No local resource reservation is made.

Retain product companions, native Hello output and logs, exact product manifest,
original parent proof, resource/owner records, SCV inventories and caches. A true
Phase4 intake must verify this actual candidate and its Hello plus runtime/tool
tuple before a fresh full-CLI build; these records do not fabricate direct-product
compiled authority receipts. Source and parent/tool files are rehashed at exit.

Unproven: native Phase3 success, hosted memory sufficiency, and downstream full
CLI capability. No full build or fixture execution was performed while staging.
