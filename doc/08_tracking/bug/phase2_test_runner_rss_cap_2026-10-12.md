# Phase 2 native test runner exceeds the enforced RSS budget

Status: reproduced; bounded scheduling/retention repair pending.

Producer 4c479a0d3f25bcb73a9c4c8fe1735b7743c65862076c73e079b7f7bc9c607036, source f7e315569, admitted phase2 runtime capsule. Non-delegated normal/slim compiler matrix used four build threads and two test workers. Test runner build ended status 88 after 418 seconds, with no fatal MIR diagnostics. Process-tree watchdog retained status=rss-cap-exceeded, peak_rss_kib=5948320, enforced limit=5859375. Ordinary compile RSS target remains 1000000000 bytes; it is not met by this tool build.

Evidence: /mnt/wsl/simple-dbc-native-bootstrap-20261012/stage2-compiler-tests/x86_64-unknown-linux-gnu/verification/logs/test_runner_build.log and summary.env in the same verification root. First investigate serialized tool/build scheduling and retained compiler state. Keep the resource guard enforced; do not replace status 88 with a compile PASS or infer test execution from absent MIR errors. General test runtime remains unqualified.
