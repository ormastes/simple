#!/usr/bin/env python3
"""
Simple Language Syntax Migration Tool - Option B (fn/me)

Migrates from current syntax to fn/me syntax:
- var fn method() -> me method() (mutable methods, implicit self)
- fn method() -> fn method() (immutable methods, implicit self)
- static fn method() -> static fn method() (static methods, no self)
- val x = ... -> val x = ... (immutable variables, no change)
- var x = ... -> var x = ... (mutable variables, no change)

For backward compatibility with parser:
- Keeps explicit self parameters for now
- Converts: fn method(mut self, ...) -> me method(self, ...)
- Converts: fn method(self, ...) -> fn method(self, ...)
"""

import re
import os
from pathlib import Path
from datetime import datetime

class MeSyntaxMigration:
    def __init__(self):
        self.files_processed = 0
        self.files_modified = 0
        self.backup_dir = Path(f".migration_backup_me_{datetime.now().strftime('%Y%m%d_%H%M%S')}")
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        print(f"Created backup directory: {self.backup_dir}")

    def migrate_content(self, content: str) -> str:
        """Apply all syntax transformations"""
        result = content

        # 1. Convert: var fn method(self, ...) -> me method(self, ...)
        #    Remove var fn prefix, replace with me
        result = re.sub(
            r'^(\s*)var\s+fn\s+(\w+)\s*\(\s*self\s*\)(\s*(?:->)?)',
            r'\1me \2(self)\3',
            result,
            flags=re.MULTILINE
        )

        result = re.sub(
            r'^(\s*)var\s+fn\s+(\w+)\s*\(\s*self\s*,\s*',
            r'\1me \2(self, ',
            result,
            flags=re.MULTILINE
        )

        # 2. Convert: fn method(mut self, ...) -> me method(self, ...)
        #    Remove mut from self parameter
        result = re.sub(
            r'^(\s*)fn\s+(\w+)\s*\(\s*mut\s+self\s*\)(\s*(?:->)?)',
            r'\1me \2(self)\3',
            result,
            flags=re.MULTILINE
        )

        result = re.sub(
            r'^(\s*)fn\s+(\w+)\s*\(\s*mut\s+self\s*,\s*',
            r'\1me \2(self, ',
            result,
            flags=re.MULTILINE
        )

        # 3. Keep: fn method(self, ...) as is (immutable methods)
        # 4. Keep: static fn method() as is (static methods)
        # 5. Keep: val/var as is (already migrated)

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
        print("=== Simple Language Syntax Migration (fn/me) ===")
        print("Migrating to LL(1)-friendly fn/me syntax\n")

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
        print("2. Update parser to handle 'me' keyword")
        print("3. Run tests: cargo test && make check")
        print("4. Commit: jj commit -m 'Migrate to fn/me syntax (Option B)'")

if __name__ == '__main__':
    migration = MeSyntaxMigration()
    migration.run()
