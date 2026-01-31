#!/bin/bash

# Dashboard CI/CD Setup Script
# Helps configure GitHub Actions and Jenkins/Hudson for Dashboard CLI
# Usage: ./scripts/setup-dashboard-ci.sh [github|jenkins|both]

set -e

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Functions
print_header() {
    echo -e "${BLUE}===================================${NC}"
    echo -e "${BLUE}$1${NC}"
    echo -e "${BLUE}===================================${NC}"
}

print_success() {
    echo -e "${GREEN}✓ $1${NC}"
}

print_error() {
    echo -e "${RED}✗ $1${NC}"
}

print_warning() {
    echo -e "${YELLOW}⚠ $1${NC}"
}

check_file() {
    if [ -f "$1" ]; then
        print_success "Found: $1"
        return 0
    else
        print_error "Missing: $1"
        return 1
    fi
}

# Main function
setup_github_actions() {
    print_header "Setting up GitHub Actions"

    # Check GitHub Actions workflow exists
    WORKFLOW_FILE=".github/workflows/dashboard-ci.yml"

    if ! check_file "$WORKFLOW_FILE"; then
        print_error "Workflow file not found!"
        return 1
    fi

    echo -e "\n${BLUE}GitHub Actions Configuration:${NC}"
    echo "- Workflow file: $WORKFLOW_FILE"
    echo "- Triggers: Push to main/develop, PRs"
    echo "- Platforms: Ubuntu, macOS, Windows"
    echo ""
    echo "Steps to activate:"
    echo "1. Push changes to GitHub"
    echo "2. Go to repository → Actions tab"
    echo "3. Click 'Dashboard CI/CD' workflow"
    echo ""

    # Check if git remote exists
    if git remote get-url origin > /dev/null 2>&1; then
        REMOTE=$(git remote get-url origin)
        print_success "Git remote: $REMOTE"
    else
        print_warning "No git remote configured"
    fi

    echo "Optional: Enable branch protection"
    echo "1. Go to Settings → Branches"
    echo "2. Add rule for 'main' branch"
    echo "3. Check 'Require status checks to pass'"
    echo "4. Select 'Dashboard CI/CD' checks"
    echo ""

    print_success "GitHub Actions setup complete!"
}

setup_jenkins() {
    print_header "Setting up Jenkins/Hudson"

    # Check Jenkinsfile exists
    JENKINSFILE="Jenkinsfile-dashboard"

    if ! check_file "$JENKINSFILE"; then
        print_error "Jenkinsfile not found!"
        return 1
    fi

    print_success "Found: $JENKINSFILE"
    echo ""
    echo -e "${BLUE}Jenkins Configuration Steps:${NC}"
    echo ""
    echo "1. Create New Pipeline Job:"
    echo "   - Go to Jenkins home"
    echo "   - Click 'New Item'"
    echo "   - Name: 'Dashboard-CI-CD'"
    echo "   - Select 'Pipeline'"
    echo "   - Click 'OK'"
    echo ""
    echo "2. Configure Pipeline:"
    echo "   - Pipeline section → 'Pipeline script from SCM'"
    echo "   - SCM: 'Git'"
    echo "   - Repository URL: $(git remote get-url origin 2>/dev/null || echo 'https://github.com/org/repo')"
    echo "   - Credentials: (configure if private repo)"
    echo "   - Branch: */main"
    echo "   - Script Path: Jenkinsfile-dashboard"
    echo ""
    echo "3. Build Triggers:"
    echo "   - GitHub hook trigger (recommended)"
    echo "   - OR Poll SCM: H/15 * * * *"
    echo ""
    echo "4. Verify Rust on agents:"

    # Check local Rust installation
    if command -v rustc &> /dev/null; then
        RUST_VERSION=$(rustc --version)
        print_success "$RUST_VERSION"
    else
        print_warning "Rust not found on this system"
        echo "   Install on Jenkins agents with:"
        echo "   curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh"
    fi

    echo ""
    echo "5. Optional: Configure Notifications"
    echo "   - Email: Manage Jenkins → Configure System"
    echo "   - Slack: Install Slack plugin and configure webhook"
    echo ""

    print_success "Jenkins setup instructions complete!"
}

setup_environment() {
    print_header "Verifying Build Environment"

    echo ""
    echo -e "${BLUE}Checking prerequisites:${NC}"
    echo ""

    # Check Rust
    if command -v rustc &> /dev/null; then
        RUST_VERSION=$(rustc --version)
        print_success "$RUST_VERSION"
    else
        print_error "Rust not installed"
        echo "  Install: https://rustup.rs/"
        return 1
    fi

    # Check Cargo
    if command -v cargo &> /dev/null; then
        CARGO_VERSION=$(cargo --version)
        print_success "$CARGO_VERSION"
    else
        print_error "Cargo not installed"
        return 1
    fi

    # Check Git
    if command -v git &> /dev/null; then
        GIT_VERSION=$(git --version)
        print_success "$GIT_VERSION"
    else
        print_error "Git not installed"
        return 1
    fi

    # Check dashboard files
    echo ""
    echo -e "${BLUE}Checking dashboard files:${NC}"
    check_file "src/app/dashboard/main.spl"
    check_file "src/lib/std/src/tooling/dashboard/notify.spl"
    check_file "src/lib/std/src/tooling/dashboard/alert_rules.spl"
    check_file "src/lib/std/src/tooling/dashboard/compare.spl"
    check_file "src/lib/std/src/tooling/dashboard/query.spl"

    echo ""
    print_success "Environment verification complete!"
}

test_build() {
    print_header "Testing Dashboard Build"

    echo ""
    echo -e "${BLUE}Building dashboard...${NC}"

    if [ ! -f "target/debug/simple" ]; then
        print_warning "Simple compiler not found, building..."
        cargo build 2>&1 | tail -5
    fi

    if ./target/debug/simple compile src/app/dashboard/main.spl; then
        print_success "Dashboard compiled successfully"

        if [ -f "src/app/dashboard/main.smf" ]; then
            SIZE=$(du -h src/app/dashboard/main.smf | cut -f1)
            print_success "Binary created ($SIZE)"
        fi

        echo ""
        echo -e "${BLUE}Running dashboard...${NC}"
        if ./target/debug/simple src/app/dashboard/main.spl | head -20; then
            print_success "Dashboard executed successfully"
        else
            print_error "Dashboard execution failed"
            return 1
        fi
    else
        print_error "Dashboard compilation failed"
        return 1
    fi

    echo ""
    print_success "Build test complete!"
}

show_usage() {
    echo "Usage: $0 [command]"
    echo ""
    echo "Commands:"
    echo "  github   - Setup GitHub Actions"
    echo "  jenkins  - Setup Jenkins/Hudson"
    echo "  both     - Setup both GitHub Actions and Jenkins"
    echo "  env      - Verify build environment"
    echo "  test     - Test dashboard build locally"
    echo "  help     - Show this help message"
    echo ""
}

# Main script
cd "$ROOT_DIR"

COMMAND=${1:-both}

case "$COMMAND" in
    github)
        setup_github_actions
        ;;
    jenkins)
        setup_jenkins
        ;;
    both)
        setup_github_actions
        echo ""
        setup_jenkins
        ;;
    env)
        setup_environment
        ;;
    test)
        setup_environment
        echo ""
        test_build
        ;;
    help|--help|-h)
        show_usage
        ;;
    *)
        print_error "Unknown command: $COMMAND"
        show_usage
        exit 1
        ;;
esac

echo ""
echo -e "${GREEN}Setup completed!${NC}"
echo ""
echo "Next steps:"
echo "1. Review configuration: doc/guide/dashboard_cicd.md"
echo "2. Push changes to repository"
echo "3. Monitor builds in GitHub Actions or Jenkins"
echo ""
