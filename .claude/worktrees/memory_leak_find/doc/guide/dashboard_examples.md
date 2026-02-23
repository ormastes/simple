# Dashboard CLI - Usage Examples

This document provides practical examples for using the Simple Dashboard CLI.

## Quick Start Examples

### Example 1: Daily Status Update

```bash
#!/bin/bash
# daily_update.sh - Get a daily status update

echo "=== Daily Dashboard Status ==="
./target/debug/simple src/app/dashboard/main.spl <<EOF
collect --mode=fast
status
trends --weekly
check-alerts
EOF
```

### Example 2: Pre-Commit Hook

```bash
#!/bin/bash
# .git/hooks/pre-commit - Run dashboard checks before commit

echo "Running dashboard checks..."
DASHBOARD="./target/debug/simple src/app/dashboard/main.spl"

# Collect fresh metrics
$DASHBOARD collect --mode=fast

# Check if any alerts triggered
ALERTS=$($DASHBOARD check-alerts)
if echo "$ALERTS" | grep -q "TRIGGERED"; then
    echo "Warning: Dashboard alerts triggered"
    echo "$ALERTS"
fi

exit 0
```

### Example 3: Weekly Report Generation

```bash
#!/bin/bash
# weekly_report.sh - Generate weekly report

DATE=$(date +%Y-%m-%d)
WEEK_AGO=$(date -d "7 days ago" +%Y-%m-%d)

echo "Generating weekly report..."

./target/debug/simple src/app/dashboard/main.spl <<EOF
export --format=html \
  --include=coverage,trends,alerts \
  --date-range=$WEEK_AGO:$DATE \
  reports/weekly-$DATE.html

compare --baseline=$WEEK_AGO --current=$DATE --format=json > reports/comparison-$DATE.json

echo "Report saved to reports/weekly-$DATE.html"
EOF
```

---

## Command Examples

### Status and Collection

**Display current metrics:**
```bash
$ simple dashboard status

==================================
  Project Dashboard Status
==================================

Coverage:        82.5%
Features:        85.0% (17/20)
TODOs:           145 (3 P0)
Tests:           95
P0 Issues:       3

Last Updated: 2026-01-21 12:00:00 UTC
```

**Collect metrics:**
```bash
# Fast collection (use cache)
$ simple dashboard collect --mode=fast

# Full collection (all sources)
$ simple dashboard collect --mode=full

# Incremental collection (only new data)
$ simple dashboard collect --mode=incremental
```

---

### Snapshots and Trends

**Take a snapshot:**
```bash
$ simple dashboard snapshot
✓ Snapshot created: doc/dashboard/history/2026-01/2026-01-21.sdn
```

**View trends:**
```bash
# Weekly trend
$ simple dashboard trends --weekly

Coverage:        80% → 82.5% ↑
Features:        80% → 85% ↑
TODOs:          157 → 145 ↓
Tests:           87 → 95 ↑

# Monthly trend with chart
$ simple dashboard trends --monthly --chart

Coverage Trend
 100% |
  80% |  ╱╲
  60% |╱  ╲
  40% |    ╲
   0% |─────────────────────

# Specific metric
$ simple dashboard trends --metric=coverage
```

---

### Exports

**Export to HTML:**
```bash
$ simple dashboard export --format=html report.html

✓ HTML report generated: report.html
  - Coverage chart: included
  - Trend analysis: 7 days
  - Alert status: 2 active
```

**Export with filtering:**
```bash
# Export specific sections
$ simple dashboard export \
  --format=html \
  --include=coverage,trends,alerts \
  --exclude=tests \
  report.html

# Export specific date range
$ simple dashboard export \
  --format=html \
  --date-range=2026-01-01:2026-01-21 \
  monthly-report.html

# Export with custom threshold
$ simple dashboard export \
  --format=json \
  --threshold=85 \
  metrics.json
```

**Export to JSON:**
```bash
$ simple dashboard export --format=json metrics.json

✓ JSON report generated: metrics.json
$ cat metrics.json | jq '.coverage'
82.5
```

**Export to Markdown:**
```bash
$ simple dashboard export --format=markdown report.md

✓ Markdown report generated: report.md
$ head -20 report.md

# Dashboard Report
## Coverage: 82.5%
## Features: 85%
...
```

---

### Configuration

**Initialize configuration:**
```bash
$ simple dashboard config-init

✓ Configuration initialized: doc/dashboard/config.sdn
```

**Validate configuration:**
```bash
$ simple dashboard config-validate

✓ Configuration valid:
  - Notifications: enabled
  - Alerts: 3 active rules
  - Export: HTML, JSON, CSV
```

**View configuration:**
```bash
$ simple dashboard config-show

[dashboard]
update_interval = 3600
snapshot_retention = 90

[coverage]
threshold = 80.0

[notifications]
enabled = true
channels = slack, email
```

**Update configuration:**
```bash
$ simple dashboard config-set coverage.threshold 85.0

✓ Updated: coverage.threshold = 85.0
```

---

### Phase 6 Features

#### Notification Testing

**Test Slack webhook (dry-run):**
```bash
$ simple dashboard notify-test --channel=slack --dry-run

[DRY-RUN] Would send Slack notification to https://hooks.slack.com/...
  Title: Dashboard Alert - Coverage Below Threshold
  Severity: critical
```

**Send real test notification:**
```bash
$ simple dashboard notify-test --channel=slack

✓ Test notification sent to Slack
  Webhook: https://hooks.slack.com/...
  Status: 200 OK
```

**Test email:**
```bash
$ simple dashboard notify-test --channel=email --dry-run

[DRY-RUN] Would send email
  To: team@example.com
  Subject: Dashboard Alert - P0 Issues Detected
  Severity: warning
```

**Test all channels:**
```bash
$ simple dashboard notify-test --all

Testing all notification channels...

[SLACK]
✓ Webhook valid (200 OK)

[EMAIL]
✓ SMTP configuration valid

[WEBHOOK]
✓ Generic webhook reachable
```

---

#### Alert Rules

**Add rules:**
```bash
# Critical: Coverage below 75%
$ simple dashboard alert-add "coverage < 75.0" --level=critical

✓ Rule added (ID: 1)
  Expression: coverage < 75.0
  Level: critical
  Status: active

# Warning: P0 todos above 10
$ simple dashboard alert-add "todos.p0 > 10" --level=warning

✓ Rule added (ID: 2)

# Info: Feature completion below 80%
$ simple dashboard alert-add "features < 80%" --level=info

✓ Rule added (ID: 3)
```

**List rules:**
```bash
$ simple dashboard alert-list

ID | Expression             | Level     | Status
───┼────────────────────────┼───────────┼────────
 1 | coverage < 75.0        | critical  | active
 2 | todos.p0 > 10          | warning   | active
 3 | features < 80%         | info      | active

Total: 3 rules
```

**Check alerts:**
```bash
$ simple dashboard check-alerts

Alert Evaluation Results
========================

Rule #1: coverage < 75.0
  Status: PASSED (82.5% >= 75.0%)
  Level:  critical

Rule #2: todos.p0 > 10
  Status: PASSED (3 <= 10)
  Level:  warning

Rule #3: features < 80%
  Status: TRIGGERED (85% >= 80%)
  Level:  info

Summary: 2 passed, 1 triggered
```

**Remove rule:**
```bash
$ simple dashboard alert-remove 3

✓ Rule removed (ID: 3)
  Removed: features < 80%
```

---

#### Comparative Analysis

**Simple comparison:**
```bash
$ simple dashboard compare --baseline=2026-01-01

Dashboard Comparison: 2026-01-01 → 2026-01-21

Metric           | Baseline | Current  | Change  | Trend
─────────────────┼──────────┼──────────┼─────────┼──────
Coverage         | 78.5%    | 82.5%    | +4.0%   | UP
Features         | 80.0%    | 85.0%    | +5.0%   | UP
TODOs            | 157      | 145      | -12     | DOWN
Tests            | 87       | 95       | +8      | UP
P0 Issues        | 5        | 3        | -2      | DOWN

Summary: 5 improvements, 0 regressions
```

**Compare specific metric:**
```bash
$ simple dashboard compare \
  --baseline=2026-01-01 \
  --metric=coverage

Coverage Comparison: 2026-01-01 → 2026-01-21

Baseline: 78.5%
Current:  82.5%
Change:   +4.0%
Trend:    Improving
```

**JSON output:**
```bash
$ simple dashboard compare --baseline=2026-01-01 --format=json

{
  "baseline_date": "2026-01-01",
  "current_date": "2026-01-21",
  "baseline": {
    "coverage": 78.5,
    "features_percent": 80.0,
    "todos_p0": 5
  },
  "current": {
    "coverage": 82.5,
    "features_percent": 85.0,
    "todos_p0": 3
  },
  "improvements": 5,
  "regressions": 0
}
```

---

#### Query Engine

**Simple queries:**
```bash
# Find P0 TODOs
$ simple dashboard query "todos where priority=P0"

Query Results:
ID | Priority | Area      | Status
───┼──────────┼───────────┼────────
1  | P0       | parser    | open
2  | P0       | codegen   | open
3  | P1       | runtime   | open

Results: 2 P0 items found

# Find complete features
$ simple dashboard query "features where status=complete"

Query Results:
ID | Category       | Name              | Status
───┼────────────────┼──────────────────┼─────────
1  | Language       | Pattern Matching  | complete
2  | Language       | Type Inference    | complete
3  | Infrastructure | Memory Safety     | complete

Results: 3 features found

# Coverage below 80%
$ simple dashboard query "coverage where percent < 80"

Query Results:
Level       | Percent
────────────┼────────
Unit Tests  | 75%
Integration | 70%

Results: 2 files below threshold
```

**Complex queries:**
```bash
# P0 and open
$ simple dashboard query "todos where priority=P0 and status=open"

# P0 or incomplete
$ simple dashboard query "todos where priority=P0 or status=open"

# With sorting and limit
$ simple dashboard query "tests where status=failed order by name limit 10"

# Contains filter
$ simple dashboard query "todos where area contains parser"

# Starts with filter
$ simple dashboard query "features where name starts_with Type"
```

**JSON output:**
```bash
$ simple dashboard query "todos where priority=P0" --format=json

{
  "entity": "todos",
  "count": 2,
  "rows": [
    {
      "id": "1",
      "priority": "P0",
      "area": "parser",
      "status": "open"
    },
    {
      "id": "2",
      "priority": "P0",
      "area": "codegen",
      "status": "open"
    }
  ]
}
```

---

## Scripting Examples

### Bash Script: Automated Daily Update

```bash
#!/bin/bash
# automated_daily_update.sh

DASHBOARD_CLI="./target/debug/simple"
DASHBOARD_SCRIPT="src/app/dashboard/main.spl"
DATE=$(date +%Y-%m-%d)
REPORT_DIR="reports"

mkdir -p "$REPORT_DIR"

echo "[$DATE] Starting automated dashboard update..."

# Collect metrics
echo "  - Collecting metrics..."
$DASHBOARD_CLI $DASHBOARD_SCRIPT collect --mode=full

# Create snapshot
echo "  - Creating snapshot..."
$DASHBOARD_CLI $DASHBOARD_SCRIPT snapshot

# Check alerts
echo "  - Checking alerts..."
ALERTS=$($DASHBOARD_CLI $DASHBOARD_SCRIPT check-alerts)
if echo "$ALERTS" | grep -q "TRIGGERED"; then
    echo "  ⚠ ALERTS TRIGGERED:"
    echo "$ALERTS"
fi

# Generate exports
echo "  - Generating reports..."
$DASHBOARD_CLI $DASHBOARD_SCRIPT export \
    --format=html \
    --include=coverage,trends,alerts \
    "$REPORT_DIR/dashboard-$DATE.html"

$DASHBOARD_CLI $DASHBOARD_SCRIPT export \
    --format=json \
    "$REPORT_DIR/metrics-$DATE.json"

echo "✓ Dashboard update complete"
echo "  Reports: $REPORT_DIR/"
```

### Python Script: Analyze Exported JSON

```python
#!/usr/bin/env python3
# analyze_metrics.py

import json
import sys

def analyze_metrics(json_file):
    with open(json_file) as f:
        data = json.load(f)

    coverage = data.get('coverage', 0)
    features = data.get('features_percent', 0)
    p0_todos = data.get('p0_todos', 0)

    print(f"Coverage: {coverage}%")
    print(f"Features: {features}%")
    print(f"P0 TODOs: {p0_todos}")

    # Alert if below threshold
    if coverage < 80:
        print("⚠ WARNING: Coverage below 80%")
        return 1

    if p0_todos > 5:
        print("⚠ WARNING: Too many P0 issues")
        return 1

    return 0

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python analyze_metrics.py <json_file>")
        sys.exit(1)

    sys.exit(analyze_metrics(sys.argv[1]))
```

---

## CI/CD Integration Examples

### GitHub Actions

```yaml
name: Dashboard Update

on:
  schedule:
    - cron: '0 9 * * *'  # Daily at 9 AM UTC

jobs:
  update-dashboard:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Collect Metrics
        run: ./target/debug/simple src/app/dashboard/main.spl collect --mode=full

      - name: Create Snapshot
        run: ./target/debug/simple src/app/dashboard/main.spl snapshot

      - name: Check Alerts
        run: ./target/debug/simple src/app/dashboard/main.spl check-alerts

      - name: Export Report
        run: |
          ./target/debug/simple src/app/dashboard/main.spl export \
            --format=html \
            dashboard-report.html

      - name: Upload Artifact
        uses: actions/upload-artifact@v4
        with:
          name: dashboard-report
          path: dashboard-report.html
```

### Jenkins

```groovy
pipeline {
    agent any

    triggers {
        cron('0 9 * * *')  // Daily at 9 AM
    }

    stages {
        stage('Collect Metrics') {
            steps {
                sh './target/debug/simple src/app/dashboard/main.spl collect --mode=full'
            }
        }

        stage('Create Snapshot') {
            steps {
                sh './target/debug/simple src/app/dashboard/main.spl snapshot'
            }
        }

        stage('Check Alerts') {
            steps {
                sh './target/debug/simple src/app/dashboard/main.spl check-alerts'
            }
        }

        stage('Export Report') {
            steps {
                sh './target/debug/simple src/app/dashboard/main.spl export --format=html dashboard-report.html'
            }
        }
    }

    post {
        success {
            archiveArtifacts artifacts: 'dashboard-report.html'
        }
    }
}
```

---

## Troubleshooting Examples

### Issue: No metrics collected

```bash
# Check what's collected
$ simple dashboard status

# Collect with verbose output
$ simple dashboard collect --mode=full --verbose

# Check data files
$ ls -la doc/dashboard/tables/
```

### Issue: Query returns no results

```bash
# First verify data exists
$ simple dashboard status

# Try simpler query
$ simple dashboard query "todos"

# Check entity name
$ simple dashboard query "features"

# Verify conditions
$ simple dashboard query "todos where priority=P0"
```

### Issue: Export fails

```bash
# Check configuration
$ simple dashboard config-validate

# Try different format
$ simple dashboard export --format=json test.json

# Check permissions
$ ls -la doc/dashboard/
```

---

## Performance Tips

1. **Use `--mode=fast`** for quick collections
2. **Filter exports** with `--include/--exclude` flags
3. **Limit queries** with `--limit` clause
4. **Cache results** when possible
5. **Schedule heavy operations** off-peak hours

---

## Next Steps

- Read the [Dashboard User Guide](dashboard.md) for comprehensive documentation
- See [CI/CD Setup Guide](dashboard_cicd.md) for GitHub Actions and Jenkins
- Check [SSpec Tests](../../simple/std_lib/test/unit/testing/dashboard_spec.spl) for test examples
