# Bootstrap verification timeout loses the compiler worker policy

On Linux AArch64 release `03acdb2a8c37afe108a3a66ea961cef18b6b1763`, the
canonical bootstrap resolves a 7208960 KiB cap for 20 workers with the
supported 5120 MiB base knob. The Stage 2 full-CLI verification prerequisite
still exits 88 at a 5941472 KiB tree peak against a 5859375 KiB limit. Its
watchdog receipt records `compiler_jobs=0`, `cap_source=unspecified` and
`cap_bound=unspecified`. The enclosing Stage 2 build had correctly propagated
its worker declaration; the independent verification timeout owner had not.

`run-process-group-timeout.shs` previously used a fixed default and forwarded
neither native-build workers nor cap provenance. It now resolves the shared
tree RSS policy for native-build argv and passes its cap, positive worker
count and provenance to the independently enforcing watchdog. Other commands
retain an undeclared worker count. The legacy cap override retains its
precedence and is validated against the same ceiling. This changes no
admission gate, timeout, stub policy or memory-enforcement mode.

`scripts/bootstrap/tests/process-timeout-worker-policy-test.shs` exercises the
real wrapper/watchdog with a short fixture workload: selected native worker
cap and provenance reach the receipt; an ordinary command's `--threads` does
not widen its compiler ceiling; an excessive explicit cap is refused before
execution. Expected selected caps come from the policy on the actual host,
so the handoff test remains valid on smaller CI machines. All three scenarios
pass. The existing tree RSS policy suite passes all 16 cases.

The wrapper is independent of the requested architecture and applies to both
ARM and RISC-V native-build verification. Real compiler-test admission and
full-CLI completion remain pending a bounded retry; these shell fixtures do
not establish either Phase 3 or Phase 4 PASS.
