# Native generated Result.unwrap is unresolved in MIR

Status: compiler bug open; generator uses explicit Result matching pending
native qualification. This does not claim that Result.unwrap is unsupported
language syntax or that the compiler bug is fixed.

The patched runner09e8 generated a prelude that calls the actual
file_read_regular_no_follow_bounded(text,i64)->Result<text,text> provider,
rejects is_err(), then calls unwrap(). Admitted attempt11 bdd4 accepted HIR
but failed MIR at generated entry.spl:25:30 with unresolved method call: unwrap.
The bounded direct diagnostic completed79 MIR modules:78 succeeded,1 failed.
There was no executable or assertion verdict. The preceding is_err() did not
produce the reported failure. Root cause in return/method-owner propagation
requires compiler investigation; a method ABI conclusion is not established.
The method diagnostic reports receiver_has_type=false/kind=-1. Source review
suggests loss of initializer-derived type through a top-level global store,
but retained HIR evidence is still needed to establish that cause.

Evidence: /tmp/simple-phase2-runner-native-attempt11-20261030/plain-run3/
direct-diagnostic/build.log lines44055 and44200-44202. The selected entry is
under detached plain3 checkout SCV revision0899b6c0be51c96eaf0f105b3110e229f86a9ef5d4b8b678a739f7b8e15df2b3.

Generator revision matches the Result directly: Ok(value) supplies manifest
text; Err(_) panics before length/digest checks. The existing canonical source
semantic_link_source.spl uses this same provider with Ok/Err matching. This
preserves refused-read behavior and valid empty input, no-follow/size policy,
manifest length+SHA verification, and normal-profile MC/DC. It is an explicit
application-level alternative while the concise unwrap compiler defect remains
recorded; no semantic checks are disabled.

Regression remains the actual normal-profile plain and native SSpec cases via
the rebuilt runner. Native results are pending; source inspection alone does
not qualify the new generated expression.
