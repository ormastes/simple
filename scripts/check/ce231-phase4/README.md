# Staged ce231 Phase3 → full CLI

No dispatch or compiler execution has occurred. Actual parent run, artifact ID and compiler SHA remain required inputs; never substitute the earlier Phase2 pairing artifact.

The expected parent controller is d18104ea541e35a2fdcbe3561461605c0e6d38ac. Source is ce231b5b898d797c98d44a9b59a4859a7d792a7b. Parent artifact must be `ce231-child-phase3-RUN`, with a successful terminal GitHub run, exact ZIP digest, newly built Phase3 binary, complete/quiescent/enforced build owner, and separate Phase3 product `qualification.json`/native Hello build/run receipts. Exact Hello is `early-full-cli-ok\n42\n`. The parent's earlier resolver pairing tests Phase2 and is insufficient.

The runtime is the ce231 source-bound artifact 14871469985 from run 45286831153, ZIP SHA256 5f24b108c986147526e7edf732346af4bb25f90d5d3bc260449841aed2c01fe9. Its manifest hashes must match the actual Phase3 qualification runtime. This does not relabel the older fd366 runtime.

For a future private workflow ref, copy `parent_gate.py`, `prepare-parent.py`, and `phase4-from-ce231-phase3.py` into `scripts/check/ce231-phase4/`, and use workflow.yml as a temporary diagnostic workflow. First independently retain the successful parent run/artifact identity and actual compiler SHA. Only then supply the three workflow inputs. `prepare-parent.py --help` documents an intake-only invocation; it never starts a compiler. Do not dispatch merely because the controller branch exists.

The full CLI uses the same full source set/entry and prod LLVM options as the earlier staged controller, with one admitted per-file worker, explicit batch4, fresh source-local caches and a finite 14400-second owner capped at 75% of actual available RAM, requiring at least 2 GiB outside that cap. No 8 GiB clamp applies: previous full-product failures exceeded 11 GiB and isolated freeze exceeded 9 GiB; the small-fixture budget does not establish a full-product ceiling. Product qualification has independent caches/storage/tmp, uses the newly emitted product, and retains version/help, interpreter run, counted 1/0 positive test, counted 0/1 negative test with exact exit1, and native Hello. No early Phase4-from-Phase2 work is repeated. No MCP or additional product fanout is included.

This is provisional product evidence, not managed Phase4 admission: compiled authority/runtime capsule receipt prerequisites are still unavailable. Native Hello does not replace SSpec/compiler/core/lib/MCP gates. A successful parent is not currently asserted by this staged plan.

Resource feasibility remains unproven for this new compiler: a supported single-worker route and 75% owner do not promise the whole CLI fits. The actual parent and hosted availability must be assessed before dispatch. Parent Phase3 build cap is independently sampled as min(75% available, available minus 2 GiB), its Hello compiler cap 4 GiB, and its Hello execution cap 256 MiB; those receipt budgets do not constrain downstream full-product sizing.

The copied old controller's duplicate smoke-directory creation was removed. New negative-test exit checking requires exactly 1, rather than accepting arbitrary nonzero termination. Syntax and gate checks are recorded separately; no product result is implied.
