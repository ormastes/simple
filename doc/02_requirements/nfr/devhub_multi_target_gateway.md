# DevHub multi-target gateway NFRs

- NFR-001: Invalid Confluence selectors and CR/LF-bearing configured or explicit
  headers fail closed before network I/O.
- NFR-003: No token value reaches raw API verbose output or Confluence/Bitbucket
  transport-error diagnostics.
- NFR-004: Legacy singleton Confluence configuration and direct provider routing
  remain supported when named targets or gateway fields are absent. An omitted
  Jira gateway leaves normal `JiraClient` command traffic direct, and an omitted
  Bitbucket gateway leaves both primary API and Data Center build-status URLs
  unchanged.
