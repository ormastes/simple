# Simple Dashboard CLI - Complete Guide

The Simple Dashboard CLI provides comprehensive project monitoring and analytics through a command-line interface. This guide covers all features, configuration, and usage patterns.

## Table of Contents

1. [Overview](#overview)
2. [Installation](#installation)
3. [Quick Start](#quick-start)
4. [Commands](#commands)
5. [Configuration](#configuration)
6. [Phase 6 Features](#phase-6-features)
7. [Use Cases](#use-cases)
8. [Troubleshooting](#troubleshooting)
9. [Advanced Topics](#advanced-topics)

---

## Overview

The Dashboard CLI monitors your Simple language project by:
- Collecting metrics from multiple sources
- Analyzing coverage, features, TODOs, and tests
- Generating visual reports
- Tracking historical trends
- Sending notifications
- Supporting custom alert rules
- Providing comparative analysis
- Enabling SQL-like data queries

### Key Capabilities

- **Real-time Metrics**: Coverage, test counts, feature completion
- **Historical Tracking**: Snapshots and trend analysis
- **Data Export**: HTML, Markdown, JSON formats
- **Alert System**: Custom rules with multiple severity levels
- **Notifications**: Slack, webhooks, email integration
- **Advanced Queries**: Filter and analyze dashboard data
- **Comparative Analysis**: Compare metrics across dates

---

## Installation

### Prerequisites

- Simple compiler installed: `./target/debug/simple`
- Rust toolchain for building
- Git for version control

### Build from Source

```bash
cd src/app/dashboard
../../target/debug/simple compile main.spl
```

### Run Dashboard

```bash
# Run dashboard CLI
./target/debug/simple src/app/dashboard/main.spl

# Or if installed
simple dashboard [command] [options]
```

---

## Quick Start

### View Dashboard Status

```bash
simple dashboard status
```

**Output:**
```
╔════════════════════════════════════════╗
║        Project Dashboard Status        ║
╚════════════════════════════════════════╝

Coverage:        82.5%
Features:        85.0% (17/20)
TODOs:           145 (3 P0)
Tests:           95
P0 Issues:       3

Last Updated: 2026-01-21 12:00:00 UTC
```

### Collect Data

```bash
simple dashboard collect --mode=full
```

**Options:**
- `--mode=full`: Full data collection (all sources)
- `--mode=fast`: Quick collection (cache)
- `--mode=incremental`: Only new data

### View Trends

```bash
simple dashboard trends --weekly
```

**Options:**
- `--weekly`: Last 7 days
- `--monthly`: Last 30 days
- `--metric=coverage`: Specific metric

---

## Commands

### Core Commands

#### 1. Status
Display current dashboard metrics.

```bash
simple dashboard status
```

#### 2. Collect
Gather metrics from project sources.

```bash
simple dashboard collect [options]
```

**Options:**
- `--mode=full|fast|incremental`
- `--include=coverage,todos,features`
- `--exclude=tests`

#### 3. Snapshot
Create historical snapshot of current metrics.

```bash
simple dashboard snapshot
```

Creates file: `doc/dashboard/history/YYYY-MM/YYYY-MM-DD.sdn`

#### 4. Trends
Analyze metric trends over time.

```bash
simple dashboard trends [options]
```

**Options:**
- `--weekly`: Weekly trends
- `--monthly`: Monthly trends
- `--metric=coverage`: Specific metric
- `--chart`: ASCII chart visualization

#### 5. Check Alerts
Evaluate custom alert rules.

```bash
simple dashboard check-alerts
```

**Output:**
```
Alert Evaluation Results
========================

Rule #1: coverage < 75.0
  Status: PASSED (82.5% >= 75.0%)
  Level:  critical

Rule #2: todos.p0 > 10
  Status: TRIGGERED (3 <= 10)
  Level:  warning
```

---

### Phase 6 Commands

#### 6. Export
Export dashboard data to various formats.

```bash
simple dashboard export --format=html report.html
```

**Formats:**
- `--format=html`: Interactive HTML report
- `--format=markdown`: Markdown file
- `--format=json`: JSON data
- `--format=csv`: CSV spreadsheet

**Options:**
- `--include=coverage,trends,alerts`
- `--exclude=tests`
- `--date-range=2026-01-01:2026-01-21`
- `--threshold=80`: Coverage threshold

**Example:**
```bash
simple dashboard export \
  --format=html \
  --include=coverage,trends \
  --date-range=2026-01-01:2026-01-21 \
  report.html
```

#### 7. Config
Manage dashboard configuration.

```bash
simple dashboard config-init
simple dashboard config-validate
simple dashboard config-show
simple dashboard config-set key value
```

**Configuration File:**
Location: `doc/dashboard/config.sdn`

```
[dashboard]
update_interval = 3600
snapshot_retention = 90
max_alerts = 10

[coverage]
threshold = 80.0
include_branches = true

[notifications]
enabled = true
channels = slack, email
```

#### 8. Notify Test
Test notification channels without sending alerts.

```bash
simple dashboard notify-test --channel=slack --dry-run
simple dashboard notify-test --all
```

**Channels:**
- `--channel=slack`: Test Slack webhook
- `--channel=webhook`: Test generic webhook
- `--channel=email`: Test SMTP email
- `--all`: Test all configured channels

**Dry-run Mode:**
```bash
simple dashboard notify-test --channel=slack --dry-run
```

**Output:**
```
[DRY-RUN] Would send Slack notification to https://hooks.slack.com/...
  Title: Dashboard Alert - Coverage Below Threshold
  Severity: critical
```

#### 9. Alert Rules
Manage custom alert rules.

```bash
simple dashboard alert-add "coverage < 75.0" --level=critical
simple dashboard alert-list
simple dashboard alert-remove 1
```

**Add Rule:**
```bash
simple dashboard alert-add 'coverage < 75.0' --level=critical
simple dashboard alert-add 'todos.p0 > 10' --level=warning
simple dashboard alert-add 'features < 80%' --level=info
```

**Severity Levels:**
- `--level=info`: Information
- `--level=warning`: Warning (default)
- `--level=critical`: Critical

**List Rules:**
```bash
simple dashboard alert-list
```

**Output:**
```
ID | Expression             | Level     | Status
───┼────────────────────────┼───────────┼────────
 1 | coverage < 75.0        | critical  | active
 2 | features_complete < 80 | warning   | active
 3 | tests_count < 100      | info      | active
```

**Remove Rule:**
```bash
simple dashboard alert-remove 1
```

#### 10. Compare
Compare metrics between two dates.

```bash
simple dashboard compare --baseline=2026-01-01
simple dashboard compare --baseline=2026-01-01 --current=2026-01-21
```

**Options:**
- `--baseline=DATE`: Baseline date (ISO 8601)
- `--current=DATE`: Current date (default: today)
- `--metric=coverage`: Compare specific metric
- `--format=table|json`: Output format

**Output:**
```
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

#### 11. Query
Query dashboard data with SQL-like syntax.

```bash
simple dashboard query "todos where priority=P0"
simple dashboard query "features where status=complete"
simple dashboard query "coverage where percent < 80"
```

**Syntax:**
```
<entity> [where <condition>] [order by <field>] [limit <n>]
```

**Entities:**
- `todos`: TODO items
- `features`: Feature list
- `coverage`: Code coverage
- `tests`: Test results
- `plans`: Implementation plans

**Conditions:**
- `field = value`: Equals
- `field != value`: Not equals
- `field < value`: Less than
- `field > value`: Greater than
- `field contains value`: Contains substring
- `field starts_with value`: Starts with

**Examples:**
```bash
# Query P0 TODOs
simple dashboard query "todos where priority=P0"

# Find incomplete features
simple dashboard query "features where status=incomplete"

# Coverage below threshold
simple dashboard query "coverage where percent < 80"

# Complex queries with AND/OR
simple dashboard query "todos where priority=P0 and status=open"

# With sorting and limits
simple dashboard query "tests where status=failed order by name limit 10"
```

**Output:**
```
Query Results:
ID | Priority | Area      | Status
───┼──────────┼───────────┼────────
1  | P0       | parser    | open
2  | P0       | codegen   | open
3  | P1       | runtime   | open

Results: 2 P0 items found
```

---

## Configuration

### Configuration File Location

```
doc/dashboard/config.sdn
```

### Complete Configuration Example

```ini
# Dashboard Configuration

[dashboard]
# Interval between automatic updates (seconds)
update_interval = 3600

# How long to keep historical snapshots (days)
snapshot_retention = 90

# Maximum number of active alerts
max_alerts = 10

# Enable debug logging
debug = false

[coverage]
# Minimum acceptable coverage threshold
threshold = 80.0

# Include branch coverage
include_branches = true

# Files to exclude from coverage
exclude = tests/**, docs/**

[notifications]
# Enable notification system
enabled = true

# Active channels: slack, webhook, email
channels = slack, email

# Slack configuration
[notifications.slack]
webhook_url = https://hooks.slack.com/services/YOUR/WEBHOOK/URL
mention_on_alert = @dev-team
include_context = true

# Webhook configuration
[notifications.webhook]
url = https://your-api.example.com/dashboard
headers = Authorization: Bearer TOKEN
timeout = 10

# Email configuration
[notifications.email]
smtp_host = smtp.gmail.com
smtp_port = 587
from_address = dashboard@example.com
recipients = team@example.com, lead@example.com
use_tls = true

[alerts]
# Enable alert checking
enabled = true

# Check interval (seconds)
check_interval = 300

# Alert retention (days)
retention = 30

[export]
# Default export format
default_format = html

# Include sections in exports
include_sections = summary, coverage, features, trends, alerts

# Custom styling
style = default  # or: minimal, detailed
```

### Configuration Commands

```bash
# Initialize with defaults
simple dashboard config-init

# Validate configuration
simple dashboard config-validate

# Display current configuration
simple dashboard config-show

# Update single value
simple dashboard config-set coverage.threshold 85.0
simple dashboard config-set notifications.enabled true
```

---

## Phase 6 Features

### Phase C1: Notification Testing

**Purpose:** Verify notification channels work correctly before sending real alerts.

**Usage:**
```bash
# Test Slack (dry-run - no actual message sent)
simple dashboard notify-test --channel=slack --dry-run

# Actually send test notification to Slack
simple dashboard notify-test --channel=slack

# Test all configured channels
simple dashboard notify-test --all
```

**Supported Channels:**
- Slack webhooks
- Generic webhooks (HTTP POST)
- Email (SMTP)

**Dry-Run Mode:**
Validates configuration without sending actual notifications.

### Phase C2: Custom Alert Rules

**Purpose:** Define custom rules to trigger alerts based on dashboard metrics.

**Create Rule:**
```bash
simple dashboard alert-add 'coverage < 75.0' --level=critical
```

**Rule Syntax:**
```
<metric> <operator> <threshold>
```

**Operators:**
- `<`: Less than
- `>`: Greater than
- `<=`: Less than or equal
- `>=`: Greater than or equal
- `==`: Equal
- `!=`: Not equal

**Metrics:**
- `coverage`: Overall code coverage percentage
- `features`: Feature completion percentage
- `todos`: Total TODO count
- `todos.p0`: P0 TODO count
- `tests`: Test count

**Severity Levels:**
- `--level=info`: Informational
- `--level=warning`: Warning (default)
- `--level=critical`: Critical

**Management:**
```bash
# List all rules
simple dashboard alert-list

# Remove rule by ID
simple dashboard alert-remove 1

# Check which rules would trigger
simple dashboard check-alerts
```

### Phase C3: Comparative Analysis

**Purpose:** Compare metrics across different time periods to track progress.

**Compare Dates:**
```bash
# Compare Jan 1 to today
simple dashboard compare --baseline=2026-01-01

# Compare two specific dates
simple dashboard compare --baseline=2026-01-01 --current=2026-01-21
```

**Metrics Compared:**
- Coverage percentage
- Features completion
- P0 TODOs count
- Test count
- Duplication percentage
- Verification pass rate

**Trend Detection:**
- **Improving:** Metric better than baseline
- **Degrading:** Metric worse than baseline
- **Stable:** No significant change

**Output Formats:**
```bash
# Table format (default)
simple dashboard compare --baseline=2026-01-01 --format=table

# JSON format (for scripting)
simple dashboard compare --baseline=2026-01-01 --format=json
```

### Phase C4: Query/Filter Engine

**Purpose:** Query dashboard data using SQL-like syntax.

**Basic Queries:**
```bash
# Find P0 TODOs
simple dashboard query "todos where priority=P0"

# Find incomplete features
simple dashboard query "features where status=incomplete"

# Find low coverage files
simple dashboard query "coverage where percent < 80"
```

**Advanced Queries:**
```bash
# Multiple conditions with AND
simple dashboard query "todos where priority=P0 and status=open"

# Multiple conditions with OR
simple dashboard query "features where status=incomplete or status=blocked"

# Sorting and limits
simple dashboard query "tests where status=failed order by name limit 10"
```

**Query Components:**
- **Entity:** todos, features, coverage, tests, plans
- **WHERE:** Filter conditions
- **ORDER BY:** Sort results (asc/desc)
- **LIMIT:** Maximum results to return

**Output Formats:**
```bash
# Table format (default)
simple dashboard query "todos where priority=P0" --format=table

# JSON format
simple dashboard query "todos where priority=P0" --format=json
```

---

## Use Cases

### Use Case 1: Daily Status Check

```bash
# Quick overview
simple dashboard status

# Check if any alerts triggered
simple dashboard check-alerts

# View weekly trend
simple dashboard trends --weekly
```

### Use Case 2: Pre-Release Checklist

```bash
# Export comprehensive report
simple dashboard export \
  --format=html \
  --include=coverage,features,trends,alerts \
  release-report.html

# Verify all P0 issues are resolved
simple dashboard query "todos where priority=P0"

# Check coverage trend
simple dashboard compare --baseline=2026-01-01
```

### Use Case 3: Team Notifications

```bash
# Configure notifications in config.sdn
simple dashboard config-set notifications.channels slack,email

# Test before enabling
simple dashboard notify-test --all

# Alerts will automatically send when rules trigger
simple dashboard check-alerts
```

### Use Case 4: CI/CD Integration

```bash
# Collect metrics
simple dashboard collect --mode=full

# Take snapshot
simple dashboard snapshot

# Run alerts
simple dashboard check-alerts

# Export results
simple dashboard export --format=json metrics.json
```

### Use Case 5: Regression Detection

```bash
# Compare with previous known-good baseline
simple dashboard compare \
  --baseline=2026-01-01 \
  --current=2026-01-21 \
  --metric=coverage

# Query failed tests
simple dashboard query "tests where status=failed"

# Query new TODOs
simple dashboard query "todos where status=open order by created limit 20"
```

---

## Troubleshooting

### Dashboard Won't Run

**Error:** `Simple compiler not found`

**Solution:**
```bash
# Build the compiler first
cargo build

# Then run dashboard
./target/debug/simple src/app/dashboard/main.spl
```

### No Metrics Collected

**Error:** `No metrics available`

**Solution:**
```bash
# Run collection explicitly
simple dashboard collect --mode=full

# Verify sources exist
ls doc/dashboard/tables/
```

### Notifications Not Working

**Error:** `Failed to send notification`

**Solution:**
```bash
# Test configuration
simple dashboard notify-test --channel=slack --dry-run

# Check configuration
simple dashboard config-validate

# Verify credentials
simple dashboard config-show
```

### Alerts Not Triggering

**Error:** `No alerts triggered`

**Solution:**
```bash
# Check active rules
simple dashboard alert-list

# Manually evaluate
simple dashboard check-alerts

# View current metrics
simple dashboard status
```

### Query Returns No Results

**Error:** `No results found`

**Solution:**
```bash
# Verify data exists
simple dashboard status

# Check entity name (todos, features, etc.)
# Check condition syntax

# Try simpler query first
simple dashboard query "todos"
```

---

## Advanced Topics

### Automated Dashboards with Scripts

Create a daily update script:

```bash
#!/bin/bash
# daily-dashboard.sh

DATE=$(date +%Y-%m-%d)
REPORT="reports/dashboard-${DATE}.html"

echo "Updating dashboard..."
simple dashboard collect --mode=full

echo "Taking snapshot..."
simple dashboard snapshot

echo "Checking alerts..."
simple dashboard check-alerts

echo "Exporting report..."
simple dashboard export \
  --format=html \
  --include=coverage,trends,alerts \
  "$REPORT"

echo "Dashboard updated: $REPORT"
```

### Integration with CI/CD

GitHub Actions example:
```yaml
- name: Update Dashboard
  run: |
    ./target/debug/simple dashboard collect --mode=full
    ./target/debug/simple dashboard check-alerts
    ./target/debug/simple dashboard export --format=json metrics.json

- name: Archive Metrics
  uses: actions/upload-artifact@v4
  with:
    name: dashboard-metrics
    path: metrics.json
```

### Custom Alert Workflows

Create a workflow that responds to alerts:

```bash
#!/bin/bash
# alert-handler.sh

ALERTS=$(simple dashboard check-alerts)

if echo "$ALERTS" | grep -q "critical"; then
    echo "Critical alert detected!"
    # Notify on-call engineer
    # Trigger incident response
    # Update status page
fi
```

### Historical Analysis

Compare long-term trends:

```bash
for date in 2026-01-01 2026-01-08 2026-01-15 2026-01-21; do
    echo "Baseline: 2026-01-01 vs Current: $date"
    simple dashboard compare \
      --baseline=2026-01-01 \
      --current=$date \
      --format=json >> trends.json
done
```

### Data Export for Analytics

Export metrics for external analysis:

```bash
# Export to various formats
simple dashboard export --format=json metrics.json
simple dashboard export --format=csv metrics.csv

# Use with analysis tools
python analyze_metrics.py metrics.json
```

---

## Best Practices

1. **Regular Snapshots**: Take snapshots daily for historical tracking
2. **Alert Configuration**: Start with critical alerts, add more as needed
3. **Notification Testing**: Always test notifications before critical alerts
4. **Baseline Comparisons**: Establish known-good baselines for regression detection
5. **Regular Exports**: Export monthly reports for archival
6. **Configuration Backup**: Keep dashboard config in version control
7. **Documentation**: Document custom alert rules for team knowledge

---

## Related Documentation

- [Dashboard CI/CD Setup](dashboard_cicd.md) - GitHub Actions and Jenkins integration
- [CLI Reference](../reference/cli.md) - Complete command reference
- [Configuration Reference](../reference/config.md) - Configuration options

---

## Getting Help

For issues or questions:

1. Check the [Troubleshooting](#troubleshooting) section
2. Review the [Use Cases](#use-cases) for similar scenarios
3. Check dashboard logs: `simple dashboard --verbose`
4. See CI/CD documentation: `doc/guide/dashboard_cicd.md`
