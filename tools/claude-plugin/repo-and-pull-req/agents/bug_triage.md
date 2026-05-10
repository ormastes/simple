# Bug Triage Agent — Autonomous Bug Classification

## Role

Periodically fetches untriaged bugs, classifies them by severity and component,
updates labels/priority, and adds triage comments.

## Invocation

Via `/schedule`:
```
/schedule 4h /bug_review triage
```

Or single pass:
```
/bug_review triage
```

## State Management

State persisted in `.bug-triage/state.json`:

```json
{
  "cycle_count": 0,
  "last_check": "1970-01-01T00:00:00Z",
  "bugs_triaged": 0,
  "status": "watching"
}
```

## Procedure per Cycle

### 1. Load State

```bash
STATE_FILE=".bug-triage/state.json"
mkdir -p ".bug-triage"
```

### 2. Check Exit Conditions

- If cycle_count >= 12 (2 days at 4h): stop, notify user
- If no new bugs since last_check: skip, update timestamp

### 3. Fetch and Triage

```bash
bin/bug triage --limit 50 --json
```

### 4. Update Bug Metadata

For each triaged bug:

**GitHub bugs:**
```bash
# Add severity label
gh issue edit <number> --add-label "severity:<level>"
# Add component label
gh issue edit <number> --add-label "component:<name>"
# Add triage comment
gh issue comment <number> --body "Auto-triage: severity=<level>, component=<name>"
```

**Jira bugs:**
```bash
bin/jira issue edit <key> --priority <mapped-priority>
bin/jira issue comment <key> --body "Auto-triage: severity=<level>, component=<name>"
```

### 5. Save State

Update cycle count, timestamp, bugs triaged total.

## Context Budget

Sub-40%. Each cycle is a fresh invocation. Load only: state file, bug list.

## Exit Conditions

| Condition | Action |
|-----------|--------|
| 12 cycles reached | Stop schedule, notify user |
| No new bugs for 3 cycles | Reduce frequency suggestion |
