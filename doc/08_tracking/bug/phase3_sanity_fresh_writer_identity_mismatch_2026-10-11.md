# Phase 3 sanity control fresh-writer identity mismatch

Status: open. Bootstrap admission remains blocked for this control profile.

Observed on release_phase3 source 0cdf4748c3af2867383ec385bd568caa45da9a7c.
`python scripts/bootstrap/tests/sanity-base-controls-test.py
ControlTests.test_actual_writer_mutation` fails before testing mutation:
`ValueError: changed actual fresh writer`.

The control profile `llvm-32867-qualification1-controls-v1` in
`scripts/check/lib/bootstrap-stage3/sanity-base-controls.py` pins
`FRESH_WRITER` to
`6ef8cd107ac6cc2575778cc9ddda69de425860fb86ddba2938a8fc42071cf52a`.
The current tracked writer
`scripts/check/lib/bootstrap-stage3/sanity-control-functions.shs` hashes to
`ed4787d0704093d70947a2bbd5aded47d93e1f229d38efb9355b611617e0a74e`.
The Git blob and working file have the same SHA256; this is not checkout
newline conversion.

The actual writer check is used by the composed sanity control admission
helper, so this is more than a stale synthetic fixture. Preserve the rejection
until the writer changes have been reviewed against this historical control
profile and fresh evidence binds the resulting writer identity. Updating the
pin solely to make this test pass would not establish qualification.

Separately, the shell-dispatch control test assumed Git Bash was installed in
`C:/Program Files/Git`. This host uses `C:/dev/tool/Git`; resolve Bash alongside
the Git executable to exercise the dispatch assertions. This path correction
does not resolve or bypass the writer mismatch.
