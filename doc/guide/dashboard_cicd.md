# Dashboard CI/CD Setup Guide

This comprehensive guide explains how to set up continuous integration and deployment for the Simple Dashboard CLI using GitHub Actions and Jenkins/Hudson. It covers all Phase 6 features and provides step-by-step setup instructions.

## Quick Links

- [Dashboard User Guide](dashboard.md) - How to use the dashboard
- [Dashboard SSpec Tests](../../simple/std_lib/test/unit/testing/dashboard_spec.spl) - Test specifications
- [CI/CD Summary](../../CI_CD_SETUP_SUMMARY.md) - Quick reference

## Table of Contents

1. [GitHub Actions Setup](#github-actions-setup)
2. [Jenkins/Hudson Setup](#jenkinshudon-setup)
3. [Pipeline Stages](#pipeline-stages)
4. [Monitoring and Notifications](#monitoring-and-notifications)
5. [Troubleshooting](#troubleshooting)

---

## GitHub Actions Setup

### Overview

The GitHub Actions workflow (`.github/workflows/dashboard-ci.yml`) automatically:
- Builds dashboard CLI on multiple platforms (Linux, macOS, Windows)
- Runs automated tests
- Verifies all Phase 6 features
- Generates artifacts and releases
- Performs code quality checks

### Prerequisites

- GitHub repository with Actions enabled
- Repository secrets configured (if needed)

### Automatic Triggers

The workflow triggers on:
- Push to `main`, `master`, or `develop` branches
- Pull requests to `main`, `master`, or `develop` branches
- Changes to dashboard-related files:
  - `src/app/dashboard/**`
  - `src/lib/std/src/tooling/dashboard/**`
  - `.github/workflows/dashboard-ci.yml`

### Workflow Jobs

#### 1. **Build** (Matrix: Ubuntu, macOS, Windows)
```yaml
- Compiles dashboard CLI on multiple platforms
- Verifies compilation artifacts are created
- Caches cargo dependencies for faster builds
```

#### 2. **Dashboard Tests** (Ubuntu)
```yaml
- Runs dashboard CLI
- Verifies all 4 Phase 6 features are available:
  - C1: Notification Testing
  - C2: Custom Alert Rules
  - C3: Comparative Analysis
  - C4: Query/Filter Engine
```

#### 3. **Module Tests** (Ubuntu)
```yaml
- Compiles each dashboard module individually
- Verifies notify.spl
- Verifies alert_rules.spl
- Verifies compare.spl
- Verifies query.spl
```

#### 4. **Code Quality** (Ubuntu)
```yaml
- Checks code style and conventions
- Validates TODO format
- Checks for unused variables
```

#### 5. **Artifact** (Ubuntu)
```yaml
- Creates downloadable artifacts
- Generates release notes
- Creates GitHub releases on tags
```

#### 6. **Lint** (Ubuntu)
```yaml
- Checks for common code issues
- Validates language conventions
```

### View Workflow Results

1. Go to your GitHub repository
2. Click **Actions** tab
3. Select **Dashboard CI/CD** workflow
4. Click on a run to see detailed results
5. Check **Artifacts** section for built binaries

### Manual Workflow Trigger

You can manually trigger the workflow:

```bash
# Via GitHub CLI
gh workflow run dashboard-ci.yml

# Or commit and push changes that match the trigger conditions
git add .
git commit -m "Update dashboard"
git push
```

### Release Creation

Create a release automatically by tagging:

```bash
git tag v1.0.0
git push origin v1.0.0
```

This triggers the workflow and creates a GitHub Release with artifacts.

---

## Jenkins/Hudson Setup

### Prerequisites

- Jenkins or Hudson server installed
- Rust toolchain installed on build agents
- Git plugin installed
- Email notification plugin (optional)

### Installation Steps

#### Step 1: Create a New Pipeline Job

1. Go to Jenkins home page
2. Click **New Item**
3. Enter job name: `Dashboard-CI-CD`
4. Select **Pipeline**
5. Click **OK**

#### Step 2: Configure Pipeline

1. In **Pipeline** section, select **Pipeline script from SCM**
2. **SCM**: Select **Git**
3. **Repository URL**: Enter your git repository URL
   ```
   https://github.com/your-org/simple.git
   ```
4. **Credentials**: Add credentials if private repository
5. **Branch**: Set to `*/main` or `*/develop`
6. **Script Path**: Enter `Jenkinsfile-dashboard`

#### Step 3: Configure Triggers

In **Build Triggers** section:

1. **GitHub hook trigger for GITScm polling**
   - Requires GitHub plugin
   - Automatically triggers on push/PR

2. **Poll SCM**
   - Schedule: `H/15 * * * *` (every 15 minutes)
   - Alternative if webhook not available

#### Step 4: Configure Build Agents

Add labels to agents with Rust installed:

```groovy
// The Jenkinsfile uses 'agent any'
// To restrict to specific agents, modify:
agent {
    label 'rust && linux'
}
```

#### Step 5: Set Build Parameters (Optional)

Add parameters for custom builds:

```groovy
parameters {
    string(name: 'BRANCH', defaultValue: 'main', description: 'Git branch')
    booleanParam(name: 'SKIP_TESTS', defaultValue: false, description: 'Skip tests')
    choice(name: 'LOG_LEVEL', choices: ['INFO', 'DEBUG', 'TRACE'], description: 'Log level')
}
```

### Jenkins Configuration as Code (JCasC)

For automated Jenkins setup, use this YAML configuration:

```yaml
# jenkins.yaml
jenkins:
  jobs:
    - name: "Dashboard-CI-CD"
      type: "org.jenkinsci.plugins.workflow.job.WorkflowJob"
      script: |
        pipeline {
          agent any
          options { buildDiscarder(logRotator(numToKeepStr: '30')) }
          stages {
            stage('Build') {
              steps { sh './target/debug/simple compile src/app/dashboard/main.spl' }
            }
            stage('Test') {
              steps { sh './target/debug/simple src/app/dashboard/main.spl' }
            }
          }
        }
```

### View Build Results

1. Go to Jenkins Dashboard
2. Click on **Dashboard-CI-CD** job
3. View build history
4. Click on build number to see console output
5. Check **Artifacts** for downloaded files

### Manual Build Trigger

```bash
# Using curl
curl -X POST http://jenkins:8080/job/Dashboard-CI-CD/build \
  -H "Authorization: Bearer YOUR_TOKEN"

# Or use Jenkins CLI
java -jar jenkins-cli.jar -s http://jenkins:8080 \
  build Dashboard-CI-CD
```

### Blue Ocean (Modern Jenkins UI)

View builds in Blue Ocean:

1. Go to Jenkins home
2. Click **Blue Ocean** in sidebar
3. Select **Dashboard-CI-CD** pipeline
4. Visualize build stages with real-time logs

---

## Pipeline Stages

Both GitHub Actions and Jenkins/Hudson follow similar stages:

### 1. **Checkout**
- Clone repository
- Get commit hash and branch name

### 2. **Setup**
- Verify Rust/Cargo versions
- Create build directories
- Log environment info

### 3. **Build Dashboard CLI**
- Compile `src/app/dashboard/main.spl`
- Verify output artifact
- Copy to build directory

### 4. **Compile Modules** (Parallel)
- Build `notify.spl`
- Build `alert_rules.spl`
- Build `compare.spl`
- Build `query.spl`

### 5. **Test Dashboard**
- Run dashboard CLI
- Verify all 4 Phase 6 features:
  - ✓ C1: Notification Testing
  - ✓ C2: Custom Alert Rules
  - ✓ C3: Comparative Analysis
  - ✓ C4: Query/Filter Engine

### 6. **Unit Tests**
- Run Rust tests: `cargo test --lib dashboard`

### 7. **Code Quality**
- Check for common issues
- Verify TODO format
- Check for unused code patterns

### 8. **Lint**
- Check code style
- Verify naming conventions

### 9. **Archive Artifacts** (main branch only)
- Create release package
- Include compiled binaries
- Include source files
- Generate build metadata

### 10. **Generate Report**
- Create build report with:
  - Build number
  - Git commit and branch
  - All stages status
  - Feature verification results
  - Build duration and timestamp

---

## Monitoring and Notifications

### GitHub Actions Notifications

**Email Notifications:**
- Set up in GitHub account Settings > Notifications
- Receive emails on workflow failures

**Slack Integration:**

```yaml
# Add to .github/workflows/dashboard-ci.yml
      - name: Notify Slack
        if: failure()
        uses: slackapi/slack-github-action@v1.24.0
        with:
          webhook-url: ${{ secrets.SLACK_WEBHOOK }}
          payload: |
            {
              "text": "Dashboard CI/CD Pipeline Failed",
              "blocks": [
                {
                  "type": "section",
                  "text": {
                    "type": "mrkdwn",
                    "text": "Build: ${{ github.run_id }}\nCommit: ${{ github.sha }}\nBranch: ${{ github.ref }}"
                  }
                }
              ]
            }
```

### Jenkins Notifications

**Email Notifications:**

```groovy
// In post section
post {
    failure {
        emailext(
            subject: "Dashboard Build Failed: #${BUILD_NUMBER}",
            body: "Check console output at ${BUILD_URL}",
            to: "dev-team@example.com",
            recipientProviders: [developers(), requestor()]
        )
    }
}
```

**Slack Integration:**

```groovy
post {
    failure {
        slackSend(
            channel: '#ci-cd',
            color: 'danger',
            message: "Dashboard Build Failed: #${BUILD_NUMBER}\n${BUILD_URL}"
        )
    }
}
```

### Dashboard Metrics

Track over time:
- Build success rate
- Build duration trends
- Number of tests passed/failed
- Code quality metrics

---

## Troubleshooting

### GitHub Actions Issues

#### Build fails on Windows
```
Error: spirv-val not found
```
**Solution:** SPIR-V Tools download may timeout. Check Windows step in workflow.

#### Artifacts not uploading
```
No files found matching path
```
**Solution:** Verify the compiled binary exists. Check the build log for compilation errors.

#### Workflow not triggering
**Solution:**
- Verify branch name matches trigger conditions
- Check file paths in `paths:` filter
- Ensure Actions are enabled in repository settings

### Jenkins Issues

#### Build fails with "rustc not found"
**Solution:**
```bash
# SSH to agent and verify Rust installation
ssh agent@host
rustc --version
cargo --version

# If missing, install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env
```

#### Pipeline script not loading
```
ERROR: Failed to load script from SCM
```
**Solution:**
- Verify `Jenkinsfile-dashboard` exists in repository root
- Check Git credentials are correct
- Verify branch name in Jenkins matches actual branches

#### Artifacts not persisting
**Solution:**
```groovy
// Ensure archiveArtifacts is in correct stage
archiveArtifacts artifacts: 'dashboard-release/**/*',
                  allowEmptyArchive: false,
                  onlyIfSuccessful: true
```

### Common Issues for Both Platforms

#### "All modules compiled successfully" but tests fail
**Solution:**
- Check runtime errors in test output
- Verify dashboard data files exist
- Check file permissions

#### Out of memory during build
**Solution:**
```bash
# Increase memory for cargo
export CARGO_BUILD_JOBS=1
export RUST_BACKTRACE=full
```

#### Git clone timeout
**Solution:** Increase timeout or use SSH instead of HTTPS
```groovy
// Jenkins: Use SSH key authentication
// GitHub Actions: Use GitHub token
```

---

## Advanced Configuration

### Custom Build Environment

```groovy
// Jenkins - Set environment variables
environment {
    RUST_BACKTRACE = 'full'
    CARGO_TERM_COLOR = 'always'
    DASHBOARD_VERSION = '1.0.0-beta'
}
```

### Conditional Stages

```groovy
// Run only on main branch
when {
    branch 'main'
}

// Run only on tag
when {
    tag pattern: "v\\d+\\.\\d+\\.\\d+", comparator: "REGEXP"
}
```

### Parallel Execution

```groovy
parallel {
    stage('Build') { ... }
    stage('Test') { ... }
    stage('Lint') { ... }
}
```

### Post-Build Actions

```groovy
post {
    always {
        cleanWs()  // Clean workspace
    }
    success {
        echo "Build successful!"
    }
    failure {
        echo "Build failed!"
    }
}
```

---

## References

- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [Jenkins Documentation](https://www.jenkins.io/doc/)
- [Hudson Documentation](https://www.eclipse.org/hudson/)
- [Simple Language Documentation](../guide/overview.md)
- [Dashboard CLI Guide](../guide/dashboard.md)
