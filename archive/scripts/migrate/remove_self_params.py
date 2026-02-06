#!/usr/bin/env python3
"""
Remove explicit self parameters from method signatures

Transforms:
- me method(self) -> me method()
- me method(self, x, y) -> me method(x, y)
- fn method(self) -> fn method()
- fn method(self, x, y) -> fn method(x, y)
"""

import re
from pathlib import Path
from datetime import datetime

class RemoveSelfParams:
    def __init__(self):
        self.files_processed = 0
        self.files_modified = 0
        self.backup_dir = Path(f".migration_backup_remove_self_{datetime.now().strftime('%Y%m%d_%H%M%S')}")
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        print(f"Created backup directory: {self.backup_dir}")

    def migrate_content(self, content: str) -> str:
        """Remove self parameters from method signatures"""
        result = content

        # Pattern 1: method(self) -> method()
        result = re.sub(
            r'^(\s*(?:me|fn)\s+\w+)\s*\(\s*self\s*\)(\s*(?:->)?)',
            r'\1()\2',
            result,
            flags=re.MULTILINE
        )

        # Pattern 2: method(self, params) -> method(params)
        result = re.sub(
            r'^(\s*(?:me|fn)\s+\w+)\s*\(\s*self\s*,\s*',
            r'\1(',
            result,
            flags=re.MULTILINE
        )

        return result

    def migrate_file(self, filepath: Path) -> bool:
        """Migrate a single file"""
        try:
            content = filepath.read_text()
            migrated = self.migrate_content(content)

            if content != migrated:
                # Backup
                relative_path = filepath.relative_to('.') if filepath.is_absolute() else filepath
                backup_path = self.backup_dir / relative_path
                backup_path.parent.mkdir(parents=True, exist_ok=True)
                backup_path.write_text(content)

                # Write
                filepath.write_text(migrated)

                changes = sum(1 for a, b in zip(content.splitlines(), migrated.splitlines()) if a != b)
                print(f"  ✓ {filepath} ({changes} lines)")
                return True
            return False
        except Exception as e:
            print(f"  ✗ Error: {filepath}: {e}")
            return False

    def run(self):
        print("=== Removing self parameters from methods ===\n")

        # Find all .spl files
        spl_files = []
        for filepath in Path('.').glob('**/*.spl'):
            if any(part in filepath.parts for part in ['target', '.git', '.migration_backup']):
                continue
            spl_files.append(filepath)

        print(f"Found {len(spl_files)} .spl files\n")

        for filepath in sorted(spl_files):
            self.files_processed += 1
            if self.migrate_file(filepath):
                self.files_modified += 1

        print(f"\n{'='*50}")
        print(f"Files processed: {self.files_processed}")
        print(f"Files modified: {self.files_modified}")
        print(f"Backups: {self.backup_dir}")

if __name__ == '__main__':
    RemoveSelfParams().run()
