# Phase3 post-HIR access violation and retained owner transport

Status: OPEN; ownership repair authored, native validation UNRUN. Exact fault
instruction is not established. Do not label this AV fixed from source review.

Evidence: windows-restart-20261004/p3-next916be-cranelift80/artifact/result.json
records compile_exit139/admittedfalse. build.rss.env reports abnormal Windows
status0xc0000005; worker tmp/native-build-stderr-9092-2.log (SHA256
94ce26870562293a504da85c791107e4d149318446ff43eb2d4b142d5fc86c82)
ends after1142/1142 HIR modules and cache summary. Profiling was unset, so the
absence of optional phase markers cannot identify which later operation faulted.
mem_snapshot_finish, summary field reads, context publication and subsequent
validation remain in the unresolved interval. No debugger attachment/dump used.

The retain-all implementation still copied the complete CompileContext for
summary reads and returned a context/verdict tuple for the caller to reinstall.
The streaming sibling already commits in place. The August20 SimpleOS incident
record documents earlier recovery after removing that ownership pattern; this
is supporting precedent, not proof of this Windows fault's exact cause.

Repair: retain-all lowering exposes a canonical me owner operation returning
only bool. Production orchestration consumes it directly and never converts a
malformed tuple plus zero errors into success. Summary reads use the owner.
The original tuple API remains a compatibility wrapper for existing callers;
general class/tuple code-generation correctness is not claimed repaired.

Regression coverage: existing dense physical alias lifecycle test now consumes
the scalar owner verdict and verifies committed HIR. A missing-surface case
checks false verdict, recorded error and retained sources. Existing route
contract test is updated to forbid synthetic recovery success. These tests and
all native correctness/RSS/time measurements are UNRUN. The ongoing streaming
successor is independent diagnostic evidence and must not be restarted.

Memory/performance review: removes a closure-sized local and production tuple
transport; adds no new retained aggregate or module scan. Later validation must
compare retained and streaming outputs/diagnostics and measure peak RSS/time on
the same frozen closure with a corrected producer. Existing log_phase boundaries
must be enabled in that bounded run before drawing a narrower fault conclusion.
