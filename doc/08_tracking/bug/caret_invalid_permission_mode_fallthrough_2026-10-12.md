# Unknown permission mode falls through to tool execution

Status: source repair authored; runtime verification NOT_RUN.

Owner: src/app/llm_caret/tools.spl, permission_decision and run_tool. The original selector returned arbitrary policy.default_mode for an unlisted mutating tool. run_tool rejected only deny and ask, then dispatched every other string under its allow comment. Empty or unknown modes could therefore reach bash/write execution without an explicit allow decision. Read-only/allow-list/allow-all shortcuts also ignored malformed default policy. This is source-level call-chain evidence; no qualifying runtime was available to execute the old behavior.

The selector now rejects modes outside allow/deny/ask before shortcuts, and the dispatcher independently requires exact allow before invoking an executor. Valid policy construction and approval-denied behavior are preserved. Two source scenarios in tools_spec.spl test invalid mode decisions, including explicit allow shortcuts, and real gated bash marker noncreation. Execution remains NOT_RUN; successful formatting does not prove enforcement.

This local gate repair does not authenticate remote callers or approval events and does not confine provider subprocesses. F03 still requires the protected issuer/approval owner, trusted grant token and OS/service integration. Existing provider CLI permission prompts remain authoritative.
