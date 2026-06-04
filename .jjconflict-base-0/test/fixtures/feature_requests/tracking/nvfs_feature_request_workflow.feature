# Feature: NVFS feature-request workflow
# Anchors: doc/08_tracking/feature_request/README.md, TEMPLATE.md, nvfs_requests.md
#          doc/05_design/nvfs/from_spostgre.md (upfront primary channel)
#          memory: feedback_svllm_drives_nvfs_design.md
# Status: pending — README/TEMPLATE/nvfs_requests.md exist; scenarios lock the schema.

Feature: NVFS feature-request tracker enforces the primary vs secondary channel rule
  As a Phase 5+ engineer filing a new request
  I want the tracker to force upfront vs secondary discipline, a complete schema, and a closable lifecycle
  So that requests cannot silently drop and upfront items do not get duplicated as backlog

  Background:
    Given "doc/08_tracking/feature_request/README.md" exists
    And   "doc/08_tracking/feature_request/TEMPLATE.md" exists
    And   "doc/08_tracking/feature_request/nvfs_requests.md" exists

  Scenario: README distinguishes primary upfront channel from secondary tracker channel
    Given the README describes the tracker's purpose
    When  the README is read
    Then  it names the upfront docs as "primary" channel
    And   it names this tracker as "secondary" channel
    And   it cross-references "doc/05_design/nvfs/from_spostgre.md" and "doc/05_design/nvfs/svllm_requirements.md"
    And   it cites memory note "feedback_svllm_drives_nvfs_design.md" for the rule

  Scenario: TEMPLATE defines the required fields
    Given TEMPLATE.md is the canonical entry shape
    When  TEMPLATE.md is parsed
    Then  the fields id, title, Filed-on, Filed-by, Target, Priority, Status, Requested-semantics, Acceptance-criteria, Related-upfront, Related-design-doc are present
    And   the id pattern is "FR-NVFS-####"
    And   Status values are exactly: Open, Accepted, Implemented, Rejected

  Scenario: nvfs_requests.md header matches README and TEMPLATE
    Given nvfs_requests.md begins with a header and schema section
    When  nvfs_requests.md is inspected
    Then  it declares Target = nvfs
    And   it points to the owning design doc "doc/05_design/nvfs_design.md"
    And   it lists both upfront contributions: "from_spostgre.md" and "svllm_requirements.md"

  Scenario: Upfront items are cross-referenced, not re-filed
    Given the 7 S-entries in "from_spostgre.md §3 Required API surface" are the authoritative upfront items
    When  "## Upfront Contributions (primary channel — do not re-file here)" is inspected in nvfs_requests.md
    Then  it contains exactly 7 rows marked "[UPFRONT]"
    And   each row links to its matching "from_spostgre.md §S#"
    And   the section explicitly instructs authors not to re-file these as Open Requests

  Scenario: Open Requests section is empty at Phase 4
    Given Phase 4 produces no implementation code
    When  "## Open Requests" in nvfs_requests.md is inspected
    Then  no FR-NVFS-#### entries are present
    And   a note indicates entries land during Phase 5+ implementation

  Scenario: A new entry must fill the required fields
    Given an engineer copies the TEMPLATE block into "## Open Requests"
    When  the entry is saved without a Requested-semantics paragraph
    Then  the tracker convention flags the entry as incomplete
    And   the entry cannot be triaged to Accepted

  Scenario: Promoted entries reference their upfront origin
    Given an entry is promoted from an upfront item (exception case, e.g. a semantic split)
    When  the entry is filed under "## Open Requests"
    Then  "Related-upfront" names the origin "from_spostgre.md §S#"
    And   the title includes "(promoted from §S#)" so scanners can tell at a glance

  Scenario: Closing an entry requires a design-doc or issue link
    Given an entry is ready to close with Status = Implemented
    When  the closer attempts to flip Status to Implemented
    Then  "Related-design-doc" must contain a non-empty doc§section link OR "Related-issue" must contain a non-empty issue URL
    And   entries without either link cannot move past Accepted

  Scenario: Rejected entries require a one-line reason
    Given an entry is being closed with Status = Rejected
    When  the closer flips Status
    Then  "Notes" contains a non-empty rejection reason
    And   the entry remains in the file (append-only; no deletion)

  Scenario: Ids are monotonic and not reused
    Given two entries have ever been filed, even if one was Rejected
    When  a third entry is filed
    Then  the new id is strictly greater than both existing ids
    And   no previously-used id is reassigned
