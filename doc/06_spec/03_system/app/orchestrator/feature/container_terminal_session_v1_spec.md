# Tagged terminal owner retention

Status: **NOT_RUN**. Authored manual matching `container_terminal_session_v1_spec.spl`; no native success, daemon capability, Host settlement, or Input/Geometry authorization evidence.

Requirements: ORCH-02 / HOST-02 owner retention and exact helper/plan association. The complete primary attach template and canonical helper fixture are reused. The deliberately invalid transfer has PID/generation zero and is not a native owner. No test constructs a primary session or fabricates a cleaned fact. Input-control state fixtures are pure metadata only.

| Scenario / step | Setup and action | Required check |
| --- | --- | --- |
| retains the transfer when canonical primary plan integrity fails | Change only the retained plan digest; call the actual constructor. | No session; original transfer retained; nonempty error. |
| rejects a helper request rebind before native input control | Change helper deadline request digest. | No session; original reference retained; rejection. |
| refuses a planning template as an actual native transfer | Confirm plan/helper integrity, then supply the invalid transfer. | No session; transfer retained; rejection before latch. |
| requires virgin controlled state rather than an inactive revoked slot | Call the actual constructor-consumed pure state checker with initialized metadata, uncontrolled/active changes, then a retained revoked revision. | Only virgin controlled metadata satisfies integrity; inactive prior installation rejects. No native observation claim. |
| rejects every retained attempt counter status and digest in virgin state | Individually change expiry, current/last sequence, accepted count, status, disposition, last revision/expiry and all current/last digests. | Every mutation rejects. |
| never accepts an invalid output transfer as native identity proof | Wrap the invalid transfer as output and call actual validation/identity/output match functions. | Validation and both identity correlations refuse. |

Primary fields are module-private in a public class. Metadata accessors expose plan/adoption/cleaned state, never the transfer or raw native owner. This prevents external construction/relabeling; copying a class is not noncopyability. Callers retain the canonical returned session. Identity equality excludes adoption/progress and grants no control or adoption rights.

The real collect/reap port requires exact lease/plan/helper/template correlation, then actual nonempty group cleanup proof before proof-bound reference-free retirement. It retains the historical actual `native_cleaned=true` fact if subsequent reap collection fails. Only canonical successful cleanup/reap sets that private fact. It neither cancels the group nor accepts a caller receipt. Cleaned primary owners remain retained pending actual Host ACK.

Native qualification remains required: real spawn transfer; exact positive generation/deadline/template; actual enable/state receipt with virgin controlled state; failure after enable retaining cleanup transfer; adoption and rebinding on a real owner; actual native cleanup/reap and error retention; Host settlement ACK. These paths are source-reviewed only and not simulated. No workload completion or write/resize right follows from cleanup or identity equality.
