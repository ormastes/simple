# Parse fibers reserved the entire shared queue before parsing

The Phase 2 derived full-CLI run observed parse worker 4/7 claiming and parsing
all 3,024 source files while its peers parsed zero. That process reached
13,207,768 KiB RSS; the parse phase eventually completed successfully. This is
separate from the HIR aggregate-cap failure corrected by PR #5285.

`_driver_run_parse_fibers` acquired every available atomic queue claim while
building its entry array, then started the first fiber. An early child could
therefore reserve the whole inventory before other children finished loading
source metadata. Atomic ownership prevented duplicates but did not provide
useful work sharing.

The repair limits outstanding reservations to a window of sixteen source files.
The child executes that window before attempting further claims. Peers retain
the same atomic queue, cache keys, and recovery behavior. A window skips entries
already claimed by peers and advances its cursor even when it acquires nothing.
The final partial window remains executable. Errors and completion counts are
aggregated across windows. Import keys are scoped to the current window;
outside-window imports follow the existing outside-child rule and cannot park
on a producer absent from that fiber run.

## Evidence and limits

The executable probe is
`test/01_unit/compiler/driver/parse_fiber_claim_window_v1_probe.spl`. It invokes
the production scheduling helper with an exclusive-claim callback and verifies
bounded initial reservation, a second child's opportunity to acquire work,
exact forty-file coverage, disjoint ownership, skipped peer claims, a partial
tail, and empty/completed inventory handling.

The admitted Cranelift Phase 2 producer
`e3a7e65cdad2aea37939056f5f115053733e342a89f0507eaec3ede9212233d6`
compiled the probe under pinned runtime/tool authorities with `--threads 20`,
a 300-second timeout, and an unchanged 48 GiB RSS cap. Build exit was zero;
watchdog peak was 2,860,244 KiB. Original admission binding and before/after
target-source/tool hashes matched. Probe artifact SHA-256:
`0751077b0bc809690f99ddc6d8b2c9a07719989cb8892c84c191785b2fa51e48`.
Executing the native artifact returned zero and reported passing claim-window
checks. Local diagnostic evidence is retained under
`/tmp/simple-parse-fiber-window-probe-20261029`.

Independent Astra review found no P0/P1/P2 findings. This evidence validates the
scheduling helper; it does not establish a full-CLI RSS improvement, actual
concurrent filesystem scheduling, cross-window parse-error behavior, or full
compiler qualification. The full workload must be rerun using a rebuilt
compiler/worker that contains this driver change. Reusing the old admitted
producer alone does not install the fix into its compiled driver.
