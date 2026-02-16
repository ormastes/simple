#!/usr/bin/env bash
# cleanup_doc_folder.sh - Reorganize doc/ directory
# Based on: doc/plan/doc_folder_cleanup_2026-02-16.md

set -euo pipefail

echo "=== Documentation Folder Cleanup ==="
echo ""
echo "This will move 39 files from doc/ root to subdirectories"
echo "and delete 2 obsolete files."
echo ""
read -p "Continue? (y/N) " -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "Aborted."
    exit 1
fi

cd "$(dirname "$0")/../.."

echo ""
echo "Step 1: Delete temporary/obsolete files..."

if [ -f doc/.needed_feature.md.swp ]; then
    rm -f doc/.needed_feature.md.swp
    echo "  ✓ Deleted vim swap file"
fi

if [ -f doc/needed_feature_OLD.md ]; then
    rm -f doc/needed_feature_OLD.md
    echo "  ✓ Deleted obsolete needed_feature_OLD.md"
fi

echo ""
echo "Step 2: Move session files to doc/session/..."
[ -f doc/MULTI_AGENT_SESSION_SUMMARY.md ] && mv doc/MULTI_AGENT_SESSION_SUMMARY.md doc/session/ || true
[ -f doc/SESSION_COMPLETE.md ] && mv doc/SESSION_COMPLETE.md doc/session/ || true
[ -f doc/SESSION_FINAL_SUMMARY.md ] && mv doc/SESSION_FINAL_SUMMARY.md doc/session/ || true
echo "  ✓ Moved 3 session files"

echo ""
echo "Step 3: Move coverage reports to doc/coverage/..."
[ -f doc/COMPLETE_100_PERCENT_COVERAGE.md ] && mv doc/COMPLETE_100_PERCENT_COVERAGE.md doc/coverage/ || true
[ -f doc/COMPLETION_CERTIFICATE_2026-02-16.md ] && mv doc/COMPLETION_CERTIFICATE_2026-02-16.md doc/coverage/ || true
[ -f doc/CORE_SIMPLE_100_PERCENT.md ] && mv doc/CORE_SIMPLE_100_PERCENT.md doc/coverage/ || true
[ -f doc/COVERAGE_100_PERCENT_ACHIEVEMENT.md ] && mv doc/COVERAGE_100_PERCENT_ACHIEVEMENT.md doc/coverage/ || true
[ -f doc/FINAL_COVERAGE_REPORT.md ] && mv doc/FINAL_COVERAGE_REPORT.md doc/coverage/ || true
[ -f doc/FULL_SIMPLE_100_PERCENT.md ] && mv doc/FULL_SIMPLE_100_PERCENT.md doc/coverage/ || true
[ -f doc/STDLIB_COVERAGE_IMPROVEMENT.md ] && mv doc/STDLIB_COVERAGE_IMPROVEMENT.md doc/coverage/ || true
[ -f doc/TEST_COVERAGE_ACHIEVEMENT.md ] && mv doc/TEST_COVERAGE_ACHIEVEMENT.md doc/coverage/ || true
echo "  ✓ Moved 8 coverage files"

echo ""
echo "Step 4: Move design docs to doc/design/..."
[ -f doc/COVERAGE_CHECK_API_DESIGN.md ] && mv doc/COVERAGE_CHECK_API_DESIGN.md doc/design/ || true
[ -f doc/MCDC_COVERAGE_DESIGN.md ] && mv doc/MCDC_COVERAGE_DESIGN.md doc/design/ || true
[ -f doc/TEST_RUNNER_TAG_DESIGN.md ] && mv doc/TEST_RUNNER_TAG_DESIGN.md doc/design/ || true
echo "  ✓ Moved 3 design files"

echo ""
echo "Step 5: Move release docs to doc/release/..."
[ -f doc/PRODUCTION_READINESS.md ] && mv doc/PRODUCTION_READINESS.md doc/release/ || true
[ -f doc/PRODUCTION_READY_SUMMARY.md ] && mv doc/PRODUCTION_READY_SUMMARY.md doc/release/ || true
[ -f doc/RELEASE_2026-02-14.md ] && mv doc/RELEASE_2026-02-14.md doc/release/ || true
[ -f doc/RELEASE_CHECKLIST_DL_2026-02-16.md ] && mv doc/RELEASE_CHECKLIST_DL_2026-02-16.md doc/release/ || true
echo "  ✓ Moved 4 release files"

echo ""
echo "Step 6: Move TODO files to doc/todo/..."
[ -f doc/TODO_ACTIONABLE.md ] && mv doc/TODO_ACTIONABLE.md doc/todo/ || true
[ -f doc/TODO_INVESTIGATION.md ] && mv doc/TODO_INVESTIGATION.md doc/todo/ || true
[ -f doc/TODO_NEXT_SESSION.md ] && mv doc/TODO_NEXT_SESSION.md doc/todo/ || true
[ -f doc/COMPILER_TODOS_SUMMARY.md ] && mv doc/COMPILER_TODOS_SUMMARY.md doc/todo/ || true
[ -f doc/REMAINING_WORK.md ] && mv doc/REMAINING_WORK.md doc/todo/ || true
echo "  ✓ Moved 5 TODO files"

echo ""
echo "Step 7: Move test docs to doc/test/..."
[ -f doc/TEST_STATUS_AUDIT.md ] && mv doc/TEST_STATUS_AUDIT.md doc/test/ || true
[ -f doc/TEST_STATUS_PARTIAL.md ] && mv doc/TEST_STATUS_PARTIAL.md doc/test/ || true
echo "  ✓ Moved 2 test files"

echo ""
echo "Step 8: Move bug reports to doc/bug/..."
[ -f doc/bug_report.md ] && mv doc/bug_report.md doc/bug/ || true
[ -f doc/bug_report_const_pointer_parsing.md ] && mv doc/bug_report_const_pointer_parsing.md doc/bug/ || true
echo "  ✓ Moved 2 bug files"

echo ""
echo "Step 9: Move implementation docs to doc/implementation/..."
[ -f doc/IMPLEMENTATION_FIXES.md ] && mv doc/IMPLEMENTATION_FIXES.md doc/implementation/ || true
[ -f doc/IMPLEMENTATION_PLAN_5_PHASE.md ] && mv doc/IMPLEMENTATION_PLAN_5_PHASE.md doc/implementation/ || true
echo "  ✓ Moved 2 implementation files"

echo ""
echo "Step 10: Move feature docs to doc/feature/..."
[ -f doc/needed_feature.md ] && mv doc/needed_feature.md doc/feature/ || true
[ -f doc/improve_request.md ] && mv doc/improve_request.md doc/feature/ || true
[ -f doc/FEATURES_THAT_WORK.md ] && mv doc/FEATURES_THAT_WORK.md doc/feature/ || true
echo "  ✓ Moved 3 feature files"

echo ""
echo "Step 11: Move reports to doc/report/..."
[ -f doc/import_errors_summary.md ] && mv doc/import_errors_summary.md doc/report/ || true
[ -f doc/FFI_NEEDS_ANALYSIS.md ] && mv doc/FFI_NEEDS_ANALYSIS.md doc/report/ || true
[ -f doc/EXECUTIVE_SUMMARY.md ] && mv doc/EXECUTIVE_SUMMARY.md doc/report/ || true
echo "  ✓ Moved 3 report files"

echo ""
echo "Step 12: Move integration docs to doc/integration/..."
[ -f doc/torch_ffi_integration.md ] && mv doc/torch_ffi_integration.md doc/integration/ || true
echo "  ✓ Moved 1 integration file"

echo ""
echo "Step 13: Move spec files to doc/spec/..."
[ -f doc/instructions.irdsl ] && mv doc/instructions.irdsl doc/spec/ || true
echo "  ✓ Moved 1 spec file"

echo ""
echo "Step 14: Move guide files to doc/guide/..."
[ -f doc/BUILD.md ] && mv doc/BUILD.md doc/guide/ || true
echo "  ✓ Moved 1 guide file"

echo ""
echo "=== Cleanup Complete ==="
echo ""

# Count remaining files in doc/ root
FILE_COUNT=$(find doc/ -maxdepth 1 -type f -name "*.md" -o -name "*.irdsl" | wc -l)
echo "Files remaining in doc/ root: $FILE_COUNT"
echo ""
echo "Expected: ~7 files (indexes + auto-generated)"
echo "  - README.md"
echo "  - INDEX.md"
echo "  - JIT_INFRASTRUCTURE_INDEX.md"
echo "  - MCP_LSP_DAP_INDEX.md"
echo "  - NOTE_SDN_INDEX.md"
echo "  - TODO.md (auto-generated)"
echo "  - code_statistics.md (auto-generated)"
echo ""
echo "Listing actual files:"
find doc/ -maxdepth 1 -type f | sort
echo ""
echo "Done! Run 'jj status' to review changes."
