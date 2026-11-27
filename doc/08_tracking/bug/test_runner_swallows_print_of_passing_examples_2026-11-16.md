# Test runner does not show `print` output of passing examples (in some modes)

Symptom: evidence a spec prints (generated text, timings, device names) was missing from the run logs of
passing slang system specs when run in the multi-spec / live lanes, so a pass could not be told apart from a
skip by reading the log. Reported by the multimodal and pure-runner lanes (2026-11-15).

Repro status: NOT reproduced in the smallest case. A single-file `bin/simple.exe test x_spec.spl` with
`print "EVIDENCE-LINE-12345"` inside a passing `it` does show the line in the log (2026-11-16, Rust seed).
So the loss depends on something else (directory runs, output from nested helper calls, or the output
redirect/capture mode) and still needs a minimal repro.

Observed in: slang live specs under `test/03_system/lib/slang/feature/` run through `bin/simple.exe test`.
Workaround in the slang specs: evidence lines are also appended to a file under `build/probe/`
(`_record`, e.g. `mm_answers.txt`, `pure_evidence.txt`). Not fixed here.
