# Daemon SDK direct-write fallback violates atomic publication

The shared no-GC sync SDK protocol explicitly promises atomic temporary-file
publication. Both request and response writers instead fall back to writing
the final `.req`/`.resp` path directly if staging or rename fails. Readers treat
final-path existence as publication, so that fallback can expose a partial
message or destroy an earlier complete final message. The async SDK reexports
this owner and therefore shares the defect.

Remove only the direct-final fallbacks. Successful staging and rename retain
their behavior; failed rename retains temporary-file cleanup. Failure returns
the existing empty request path or false response status. No serialization,
message digest, source identity or admission check changes. The Windows runtime
rename owner already uses wide replace-existing rename; a provider swap is not
needed for this repair.

The public client propagates an empty request path. The generic poller currently
ignores a failed response write and clears its request, so the client can time
out; this change does not add or promise retry behavior. That preexisting error
handling limitation is separate from exposing a partially published message.

`test/fixtures/compiler/native_daemon_atomic_response.spl` uses a real public
FileHandle on Windows: its held read handle must deny replacement while an
ordinary direct write remains possible. It then calls the production response
writer and requires failure, unchanged prior bytes and removed temporary file.
After closing the handle, normal successful replacement must still work.
The request fallback removal currently has source review only.

The one bounded native baseline uses admitted producer 5dd, a matching runtime
capsule, one worker, enforced 4 GiB RSS cap and normal 1 GiB reserve. Evidence
root: `D:/dev/simple-sdk-atomic-response-evidence-20261030`; baseline inputs are
hash-bound in `baseline-source-files.sha256`. The unchanged baseline compiled
61 modules and exited 0; its actual control execution exited 1:

- `rename_succeeded=false`, `direct_write_allowed=true` establish the real
  held-handle failure condition rather than a fake writer or general I/O error.
- `response_published=true`, `old_final_preserved=false` reproduce the contract
  violation in the production response owner; `temporary_removed=true` confirms
  the failed rename path cleaned up staging before the direct write.

Executable SHA256:
`e711fd6c13519047a2cfdc7cb124246796b4f88c9a27975857c1f19e06124152`.
Build/run peak RSS was 3,308,412/1,928 KiB; both process-tree receipts report
quiescent=1. Post-run fixture/protocol/FileHandle hashes match the baseline
manifest. Evidence is retained under `baseline-01`; this is a reproduced
failure, not a repaired PASS. A changed-source run of the same fixture is
authorized only after the primary workload's resource slot becomes available.
Independent source review is clear; repaired native execution and required
compiler/lib/MCP/LSP checks remain pending. No broad qualification is claimed.

This contract defect is established from source. Whether the intermittent
source92 startup failure actually entered the fallback is unproven; the most
recent debugger-observed startup acknowledged successfully. Do not attribute
that intermittency to this repair without branch-specific runtime evidence.
