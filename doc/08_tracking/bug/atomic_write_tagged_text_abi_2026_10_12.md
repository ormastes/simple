# Atomic snapshot publication receives raw pointers instead of tagged text

Status: OPEN; source correction prepared, changed compiler provider unqualified.

Actual P2 027c producer and matching runtime 594f/935f compiled the reporting logger owner. Production gc-sections strict link succeeds. Seven progress stdout assertions pass, but no persisted snapshot appears. Bounded debugger traces prove the correct environment key is read, publication and native atomic write are each reached seven times. At rt_file_atomic_write, rdi is a raw C pointer to /mnt/c/Temp/... rather than a tagged text handle; content is likewise raw. The actual C owner uses rt_core_as_string on both values and rejects tag 0. This is separate from environment lookup and validation.

Add both atomic variants to boxed_text_arg_indices at [0,1], retaining full byte extents and mode semantics. Runtime providers remain unchanged; host regression uses SOSIX aliases. Neither collapse optional values nor accept raw pointers in the runtime.

Evidence: /mnt/c/Temp/simple-manual-lanes-20261011/p2-mir-progress-actual-logger/{env-diagnostic.log,persist-diagnostic.log,atomic-abi.log,platform-gc-run-receipt.json}. Regression fixtures exercise actual atomic write/readback including multiline content and empty replacement; native execution with a corrected compiler is pending. Registry SSpec is unexecuted because the qualified application test CLI is unavailable.

Focused registry owner qualification: corrected element-wise eight native invariants PASS (compile0/23.98s/object42264/link0/run0), exact committed SCV bytes bound in /mnt/c/Temp/simple-manual-lanes-20261012/atomic-boxed-registry-elements. Initial array-comparison fixture run1 retained; no claim on native array equality semantics. This qualifies registry output only; changed compiler atomic-write roundtrip and required full CLI gates remain unqualified.
