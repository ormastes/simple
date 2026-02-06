#!/usr/bin/env python3
"""
Simple Language Syntax Migration Tool

Migrates from explicit self syntax to Scala-style val/var syntax:
- let -> val
- let mut -> var
- fn method(self, ...) -> fn method(...)
- fn method(mut self, ...) -> var fn method(...)
- fn constructor() in impl -> static fn constructor() (heuristic)
"""

import re
import os
import shutil
from pathlib import Path
from datetime import datetime

class SyntaxMigration:
    def __init__(self):
        self.files_processed = 0
        self.files_modified = 0
        self.backup_dir = Path(f".migration_backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}")
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        print(f"Created backup directory: {self.backup_dir}")

    def migrate_content(self, content: str) -> str:
        """Apply all syntax transformations"""
        result = content

        # 1. let mut -> var (MUST come before let -> val)
        result = re.sub(r'\blet\s+mut\b', 'var', result)

        # 2. let -> val
        result = re.sub(r'\blet\b', 'val', result)

        # 3. fn method(mut self) -> var fn method()
        #    Remove mut self parameter and add var prefix
        result = re.sub(
            r'^(\s*)fn\s+(\w+)\s*\(\s*mut\s+self\s*\)(\s*(?:->)?)',
            r'\1var fn \2()\3',
            result,
            flags=re.MULTILINE
        )

        result = re.sub(
            r'^(\s*)fn\s+(\w+)\s*\(\s*mut\s+self\s*,\s*',
            r'\1var fn \2(',
            result,
            flags=re.MULTILINE
        )

        # 4. fn method(self) -> fn method()
        #    Remove self parameter
        result = re.sub(
            r'^(\s*)fn\s+(\w+)\s*\(\s*self\s*\)(\s*(?:->)?)',
            r'\1fn \2()\3',
            result,
            flags=re.MULTILINE
        )

        result = re.sub(
            r'^(\s*)fn\s+(\w+)\s*\(\s*self\s*,\s*',
            r'\1fn \2(',
            result,
            flags=re.MULTILINE
        )

        # 5. Add static to constructors (heuristic for common patterns)
        #    Matches: new, default, from_*, create_*, etc. with no params
        constructor_patterns = [
            'new', 'default',
            r'from_\w+', r'create_\w+', r'make_\w+', r'build_\w+',
            r'with_\w+'
        ]

        for pattern in constructor_patterns:
            result = re.sub(
                rf'^(\s*)fn\s+({pattern})\s*\(\s*\)\s*->',
                r'\1static fn \2() ->',
                result,
                flags=re.MULTILINE
            )

        return result

    def migrate_file(self, filepath: Path) -> bool:
        """Migrate a single file, return True if modified"""
        try:
            content = filepath.read_text()
            migrated = self.migrate_content(content)

            if content != migrated:
                # Backup original
                relative_path = filepath.relative_to('.') if filepath.is_absolute() else filepath
                backup_path = self.backup_dir / relative_path
                backup_path.parent.mkdir(parents=True, exist_ok=True)
                backup_path.write_text(content)

                # Write migrated content
                filepath.write_text(migrated)

                # Count changed lines
                original_lines = content.splitlines()
                migrated_lines = migrated.splitlines()
                changes = sum(1 for a, b in zip(original_lines, migrated_lines) if a != b)

                print(f"  ✓ Modified: {filepath} ({changes} lines changed)")
                return True
            else:
                print(f"  - No changes: {filepath}")
                return False

        except Exception as e:
            print(f"  ✗ Error processing {filepath}: {e}")
            return False

    def run(self, root_dir: str = '.'):
        """Run migration on all .spl files"""
        print("=== Simple Language Syntax Migration ===")
        print("Migrating to Scala-style (val/var) syntax\n")

        # Find all .spl files
        root = Path(root_dir)
        spl_files = []

        for pattern in ['**/*.spl']:
            for filepath in root.glob(pattern):
                # Skip target, git, backup directories
                if any(part in filepath.parts for part in ['target', '.git', '.migration_backup']):
                    continue
                spl_files.append(filepath)

        print(f"Found {len(spl_files)} .spl files\n")

        # Process each file
        for filepath in sorted(spl_files):
            self.files_processed += 1
            if self.migrate_file(filepath):
                self.files_modified += 1

        # Summary
        print("\n" + "="*50)
        print("=== Migration Complete ===")
        print(f"Files processed: {self.files_processed}")
        print(f"Files modified: {self.files_modified}")
        print(f"Backups saved to: {self.backup_dir}")
        print("\n⚠️  Next steps:")
        print("1. Review changes: jj diff")
        print("2. Run tests: cargo test && make check")
        print("3. Update documentation")
        print("4. Commit: jj commit -m 'Migrate to Scala-style val/var syntax'")

if __name__ == '__main__':
    migration = SyntaxMigration()
    migration.run()
