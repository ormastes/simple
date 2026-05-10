# Dashboard CLI Guide

The Simple Dashboard CLI provides project monitoring and analytics: metrics collection, trend analysis, alerts, data export, and CI/CD integration.

For the `llm_dashboard` web login and Peer Base Pack bootstrap flow, including `SIMPLE_LLM_DASHBOARD_ADMIN_USER`, `SIMPLE_LLM_DASHBOARD_ADMIN_PASSWORD`, and `.build/llm_dashboard/auth` session storage, see [llm_dashboard_web_login.md](llm_dashboard_web_login.md).

---

## Quick Start

```bash
# View current metrics
simple dashboard status

# Collect data
simple dashboard collect --mode=full

# View trends
simple dashboard trends --weekly

# Check alert rules
simple dashboard check-alerts
```

---

## Commands

### Status

Display current project metrics (coverage, features, TODOs, tests, P0 issues).

```bash
simple dashboard status
```

### Collect

Gather metrics from project sources.

```bash
simple dashboard collect --mode=full          # All sources
simple dashboard collect --mode=fast          # Use cache
simple dashboard collect --mode=incremental   # Only new data
```

Options: `--include=coverage,todos,features`, `--exclude=tests`

### Snapshot

Create a historical snapshot of current metrics.

```bash
simple dashboard snapshot
# Creates: doc/dashboard/history/YYYY-MM/YYYY-MM-DD.sdn
```

### Trends

Analyze metric trends over time.

```bash
simple dashboard trends --weekly              # Last 7 days
simple dashboard trends --monthly --chart     # Last 30 days with ASCII chart
simple dashboard trends --metric=coverage     # Specific metric
```

### Export

Export dashboard data to various formats.

```bash
simple dashboard export --format=html report.html
simple dashboard export --format=json metrics.json
simple dashboard export --format=markdown report.md
simple dashboard export --format=csv metrics.csv
```

Options: `--include=coverage,trends,alerts`, `--exclude=tests`, `--date-range=2026-01-01:2026-01-21`

### Alert Rules

Define custom rules to trigger alerts based on metrics.

```bash
# Add rules
simple dashboard alert-add 'coverage < 75.0' --level=critical
simple dashboard alert-add 'todos.p0 > 10' --level=warning
simple dashboard alert-add 'features < 80%' --level=info

# List rules
simple dashboard alert-list

# Check which rules trigger
simple dashboard check-alerts

# Remove a rule
simple dashboard alert-remove 1
```

Severity levels: `info`, `warning`, `critical`

Available metrics: `coverage`, `features`, `todos`, `todos.p0`, `tests`

### Compare

Compare metrics between two dates.

```bash
simple dashboard compare --baseline=2026-01-01
simple dashboard compare --baseline=2026-01-01 --current=2026-01-21
simple dashboard compare --baseline=2026-01-01 --format=json
simple dashboard compare --baseline=2026-01-01 --metric=coverage
```

### Query

Query dashboard data with SQL-like syntax.

```bash
simple dashboard query "todos where priority=P0"
simple dashboard query "features where status=incomplete"
simple dashboard query "coverage where percent < 80"
simple dashboard query "todos where priority=P0 and status=open"
simple dashboard query "tests where status=failed order by name limit 10"
```

Entities: `todos`, `features`, `coverage`, `tests`, `plans`

Conditions: `=`, `!=`, `<`, `>`, `contains`, `starts_with`

### Notify Test

Test notification channels without sending real alerts.

```bash
simple dashboard notify-test --channel=slack --dry-run
simple dashboard notify-test --channel=email
simple dashboard notify-test --all
```

Channels: `slack`, `webhook`, `email`

### Config

Manage dashboard configuration.

```bash
simple dashboard config-init          # Initialize defaults
simple dashboard config-validate      # Validate config
simple dashboard config-show          # Display config
simple dashboard config-set key value # Update value
```

---

## Configuration

Config file: `doc/dashboard/config.sdn`

```ini
[dashboard]
update_interval = 3600
snapshot_retention = 90

[coverage]
threshold = 80.0
include_branches = true

[notifications]
enabled = true
channels = slack, email

[notifications.slack]
webhook_url = https://hooks.slack.com/services/YOUR/WEBHOOK/URL

[notifications.email]
smtp_host = smtp.gmail.com
smtp_port = 587
from_address = dashboard@example.com
recipients = team@example.com

[alerts]
enabled = true
check_interval = 300

[export]
default_format = html
include_sections = summary, coverage, features, trends, alerts
```

---

## CI/CD Integration

### GitHub Actions

```yaml
name: Dashboard Update
on:
  schedule:
    - cron: '0 9 * * *'
jobs:
  update-dashboard:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Collect and Export
        run: |
          simple dashboard collect --mode=full
          simple dashboard snapshot
          simple dashboard check-alerts
          simple dashboard export --format=json metrics.json
      - uses: actions/upload-artifact@v4
        with:
          name: dashboard-metrics
          path: metrics.json
```

### Jenkins

```groovy
pipeline {
    agent any
    triggers { cron('0 9 * * *') }
    stages {
        stage('Collect') {
            steps { sh 'simple dashboard collect --mode=full' }
        }
        stage('Snapshot') {
            steps { sh 'simple dashboard snapshot' }
        }
        stage('Alerts') {
            steps { sh 'simple dashboard check-alerts' }
        }
        stage('Export') {
            steps { sh 'simple dashboard export --format=html report.html' }
        }
    }
    post {
        success { archiveArtifacts artifacts: 'report.html' }
        failure {
            emailext(
                subject: "Dashboard Build Failed: #${BUILD_NUMBER}",
                body: "Check console output at ${BUILD_URL}",
                to: "dev-team@example.com"
            )
        }
    }
}
```

### Pre-Commit Hook

```bash
#!/bin/bash
simple dashboard collect --mode=fast
ALERTS=$(simple dashboard check-alerts)
if echo "$ALERTS" | grep -q "TRIGGERED"; then
    echo "Warning: Dashboard alerts triggered"
    echo "$ALERTS"
fi
exit 0
```

---

## Use Cases

**Daily status check:**
```bash
simple dashboard status && simple dashboard check-alerts && simple dashboard trends --weekly
```

**Pre-release checklist:**
```bash
simple dashboard export --format=html --include=coverage,features,trends release-report.html
simple dashboard query "todos where priority=P0"
simple dashboard compare --baseline=2026-01-01
```

**Regression detection:**
```bash
simple dashboard compare --baseline=2026-01-01 --metric=coverage
simple dashboard query "tests where status=failed"
```

---

## Troubleshooting

**No metrics collected**: Run `simple dashboard collect --mode=full` explicitly and check `doc/dashboard/tables/`.

**Notifications not working**: Test with `simple dashboard notify-test --channel=slack --dry-run` and validate config with `simple dashboard config-validate`.

**Query returns no results**: Verify data exists with `simple dashboard status`, then try a simpler query first (e.g., `simple dashboard query "todos"`).

**Alerts not triggering**: Check active rules with `simple dashboard alert-list` and manually evaluate with `simple dashboard check-alerts`.

---

## Source Code

- **Dashboard CLI**: `src/app/dashboard/`
- **Dashboard modules**: `src/lib/std/src/tooling/dashboard/`
- **Config**: `doc/dashboard/config.sdn`
- **History**: `doc/dashboard/history/`
