# Strict group-stream broker protocol V2

Source: test/01_unit/lib/common/build_manager/group_process_stream_protocol_v2_spec.spl.
Status: AWAITING_VERIFICATION; authored source assertions, not generated/run proof.

| Requirement | Actual source scenario |
|---|---|
| GSTREAM-01 | Independent canonical ordered argv digest and strict encode/decode |
| GSTREAM-01 | Transport generation/deadline changes alter full owner identity |
| GSTREAM-01 | Full positive i64 generations/deadlines round-trip without changing V1 parser |
| GSTREAM-02 | Changed argv and missing positive deadline rejected |
| GSTREAM-01 | Leading-zero integers, trailing fields, wrong header and missing LF rejected |
| GSTREAM-02 | Portable path shapes/optional generic delegation; V1 argv/cwd restrictions retained |
| GSTREAM-02 | Windows drive/UNC spellings encode without claiming Windows native support |
| GSTREAM-03 | Ready receipt binds identity/generation/argv; zero generation rejected |
| GSTREAM-03 | Unlaunched proof distinct from ready/tree observations |
| GSTREAM-01 | Aggregate escaped data budget rejects before enormous payload construction |

The codec bounds each escaped field before appending and enforces16MiB during
construction. Linux actual delegation and grant expiry clocks remain owner
admission, not pure shape validation. Deadline controls launch admission only;
workload duration is never shortened because the grant or heartbeat expires.
Ready denotes an available owned transfer; no-reported-error on an exec channel
is not positive exec/attach proof. Full native broker tests remain pending.

Separate native transport evidence: ../io/piped_group_stream_transport_v2_evidence.sdn.
It qualifies only the captured pre-header-declaration transport snapshot, not
this unexecuted protocol spec, final head, or full broker/cgroup lifecycle.
