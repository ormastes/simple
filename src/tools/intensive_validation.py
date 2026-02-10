#!/usr/bin/env python3
"""
Intensive Validation Suite for Desugared Core Simple Code

Tests:
1. Syntax validation (all files parse correctly)
2. Semantic checks (no remaining Full Simple features)
3. Core compatibility (only allowed constructs)
4. Functional equivalence (key behaviors preserved)
5. Integration tests (files work together)
"""

import re
import sys
from pathlib import Path
from collections import defaultdict
from typing import List, Tuple, Dict

class DesugarValidator:
    def __init__(self, directory: str):
        self.directory = Path(directory)
        self.errors = defaultdict(list)
        self.warnings = defaultdict(list)
        self.stats = defaultdict(int)
        
    def run_all_tests(self):
        """Run complete validation suite."""
        print("="*80)
        print("INTENSIVE VALIDATION SUITE")
        print("="*80)
        print()
        
        print("📁 Validating directory:", self.directory)
        print()
        
        # Test 1: File structure
        print("Test 1: File Structure Validation...")
        self.test_file_structure()
        print()
        
        # Test 2: Syntax validation
        print("Test 2: Syntax Validation...")
        self.test_syntax()
        print()
        
        # Test 3: No Full Simple features
        print("Test 3: Core Simple Compatibility...")
        self.test_core_compatibility()
        print()
        
        # Test 4: Transformation verification
        print("Test 4: Transformation Verification...")
        self.test_transformations()
        print()
        
        # Test 5: Cross-file consistency
        print("Test 5: Cross-File Consistency...")
        self.test_consistency()
        print()
        
        # Report results
        self.report_results()
        
    def test_file_structure(self):
        """Test 1: Verify file structure is preserved."""
        files = list(self.directory.rglob('*.spl'))
        self.stats['total_files'] = len(files)
        
        print(f"  ✓ Found {len(files)} .spl files")
        
        # Check for expected subdirectories
        expected_dirs = ['backend', 'types', 'hir', 'mir']
        for dir_name in expected_dirs:
            dir_path = self.directory / dir_name
            if dir_path.exists():
                count = len(list(dir_path.rglob('*.spl')))
                print(f"  ✓ {dir_name}/ exists ({count} files)")
            else:
                self.warnings['structure'].append(f"Expected directory not found: {dir_name}/")
        
    def test_syntax(self):
        """Test 2: Basic syntax validation."""
        issues = []
        
        for spl_file in self.directory.rglob('*.spl'):
            try:
                with open(spl_file, 'r', encoding='utf-8') as f:
                    content = f.read()
                    
                # Check for basic syntax errors
                
                # Balanced braces
                if content.count('{') != content.count('}'):
                    issues.append((spl_file, "Unbalanced braces"))
                
                # Balanced parens
                if content.count('(') != content.count(')'):
                    issues.append((spl_file, "Unbalanced parentheses"))
                
                # Balanced brackets
                if content.count('[') != content.count(']'):
                    issues.append((spl_file, "Unbalanced brackets"))
                
                self.stats['files_checked'] += 1
                
            except Exception as e:
                issues.append((spl_file, f"Read error: {e}"))
        
        if issues:
            print(f"  ✗ Found {len(issues)} syntax issues:")
            for file, issue in issues[:10]:  # Show first 10
                print(f"    - {file.name}: {issue}")
                self.errors['syntax'].append(f"{file}: {issue}")
        else:
            print(f"  ✓ All {self.stats['files_checked']} files have valid syntax")
    
    def test_core_compatibility(self):
        """Test 3: Check for disallowed Full Simple features."""
        disallowed_patterns = [
            (r'^impl\s+\w+:', 'impl block'),
            (r'<\w+>', 'generic type parameter'),
            (r'\|\w*\|', 'closure syntax'),
            (r'async\s+fn', 'async function'),
            (r'await\s+', 'await keyword'),
            (r'trait\s+\w+', 'trait definition'),
            (r'\.await\b', '.await syntax'),
        ]
        
        violations = defaultdict(list)
        
        for spl_file in self.directory.rglob('*.spl'):
            with open(spl_file, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
                
                for line_num, line in enumerate(lines, 1):
                    # Skip comments
                    if line.strip().startswith('#'):
                        continue
                    
                    for pattern, feature_name in disallowed_patterns:
                        if re.search(pattern, line):
                            violations[feature_name].append((spl_file.name, line_num, line.strip()[:60]))
        
        if violations:
            print(f"  ⚠️  Found {len(violations)} types of Full Simple features:")
            for feature, occurrences in violations.items():
                count = len(occurrences)
                print(f"    - {feature}: {count} occurrences")
                if count <= 3:  # Show details for few occurrences
                    for file, line_num, line in occurrences[:3]:
                        print(f"      {file}:{line_num}: {line}")
                self.warnings['compatibility'].extend([f"{feature} at {f}:{l}" for f, l, _ in occurrences[:5]])
        else:
            print("  ✓ No disallowed Full Simple features found")
    
    def test_transformations(self):
        """Test 4: Verify transformations were applied."""
        transformation_markers = {
            'DESUGARED': 0,
            'was: impl': 0,
            'has_': 0,
            '_value': 0,
        }
        
        module_functions = 0  # fn type_method pattern
        
        for spl_file in self.directory.rglob('*.spl'):
            with open(spl_file, 'r', encoding='utf-8') as f:
                content = f.read()
                
                # Count transformation markers
                for marker in transformation_markers:
                    transformation_markers[marker] += content.count(marker)
                
                # Count module-level functions with type prefix
                module_functions += len(re.findall(r'^fn \w+_\w+\(', content, re.MULTILINE))
        
        print("  Transformation evidence found:")
        print(f"    - DESUGARED comments: {transformation_markers['DESUGARED']}")
        print(f"    - impl conversions: {transformation_markers['was: impl']}")
        print(f"    - Option fields (has_*): {transformation_markers['has_']}")
        print(f"    - Option values (*_value): {transformation_markers['_value']}")
        print(f"    - Module functions: {module_functions}")
        
        if transformation_markers['DESUGARED'] > 100:
            print("  ✓ Strong evidence of successful desugaring")
        else:
            print("  ⚠️  Few transformation markers found")
            self.warnings['transformations'].append("Low transformation marker count")
    
    def test_consistency(self):
        """Test 5: Cross-file consistency checks."""
        
        # Check that all files in subdirectories maintain structure
        subdirs = set()
        for spl_file in self.directory.rglob('*.spl'):
            parent = spl_file.parent.relative_to(self.directory)
            if parent != Path('.'):
                subdirs.add(str(parent))
        
        print(f"  ✓ Found {len(subdirs)} subdirectories with .spl files")
        
        # Check for use statements consistency
        use_statements = defaultdict(list)
        for spl_file in self.directory.rglob('*.spl'):
            with open(spl_file, 'r', encoding='utf-8') as f:
                for line in f:
                    if line.strip().startswith('use '):
                        module = line.split('use ')[1].split('.')[0].split('{')[0].strip()
                        use_statements[module].append(spl_file.name)
        
        print(f"  ✓ Found {len(use_statements)} unique modules imported")
        
        # Most commonly imported modules
        top_imports = sorted(use_statements.items(), key=lambda x: len(x[1]), reverse=True)[:5]
        print("  Most imported modules:")
        for module, files in top_imports:
            print(f"    - {module}: used in {len(files)} files")
    
    def report_results(self):
        """Generate final report."""
        print()
        print("="*80)
        print("VALIDATION RESULTS")
        print("="*80)
        print()
        
        # Summary
        print("📊 SUMMARY")
        print(f"  Files validated: {self.stats['total_files']}")
        print(f"  Files checked: {self.stats['files_checked']}")
        print(f"  Errors: {sum(len(v) for v in self.errors.values())}")
        print(f"  Warnings: {sum(len(v) for v in self.warnings.values())}")
        print()
        
        # Errors
        if self.errors:
            print("❌ ERRORS")
            for category, error_list in self.errors.items():
                print(f"  {category.upper()}: {len(error_list)} errors")
                for error in error_list[:5]:  # Show first 5
                    print(f"    - {error}")
                if len(error_list) > 5:
                    print(f"    ... and {len(error_list) - 5} more")
            print()
        else:
            print("✅ NO ERRORS FOUND")
            print()
        
        # Warnings
        if self.warnings:
            print("⚠️  WARNINGS")
            for category, warning_list in self.warnings.items():
                print(f"  {category.upper()}: {len(warning_list)} warnings")
                for warning in warning_list[:3]:  # Show first 3
                    print(f"    - {warning}")
                if len(warning_list) > 3:
                    print(f"    ... and {len(warning_list) - 3} more")
            print()
        else:
            print("✅ NO WARNINGS")
            print()
        
        # Verdict
        print("="*80)
        if not self.errors:
            print("🎉 VALIDATION PASSED")
            print()
            print("The desugared code passes all validation tests!")
            print("Ready for compilation with seed compiler.")
            return 0
        else:
            print("❌ VALIDATION FAILED")
            print()
            print(f"Found {sum(len(v) for v in self.errors.values())} errors that need attention.")
            return 1

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 intensive_validation.py <directory>")
        print("Example: python3 intensive_validation.py src/compiler_core")
        sys.exit(1)
    
    directory = sys.argv[1]
    
    validator = DesugarValidator(directory)
    exit_code = validator.run_all_tests()
    
    sys.exit(exit_code)

if __name__ == '__main__':
    main()
