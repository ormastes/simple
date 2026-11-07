# Parent-trackable worker NFR

NFR-WORKER-001: total retirement transaction <=5000ms caller budget, with one
absolute deadline shared by all outstanding owners; report uncertainty on expiry.
NFR-WORKER-002: live process owner count cannot exceed existing configured worker
capacity plus explicitly admitted nested capacity. Bound queue, environment,
argv, request/response and output bytes before launch; preserve backpressure.
NFR-WORKER-003: parent polls/drains all owners fairly while cleanup is active;
no full repository scans or shell-outs in the coordinator's hot poll path.
NFR-WORKER-004: record actual elapsed cleanup, maximum simultaneous owners,
retained output and platform/provider capabilities in focused native evidence.
No performance PASS until an admitted runtime exercises actual coordinator flow.
