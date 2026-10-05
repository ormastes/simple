"""Resolve an immutable materialization root once; still resolve every child.

Only for an exclusively owned root. Call verify_root before publishing its
receipt. This does not authenticate file contents or authorize alias creation.
"""
from pathlib import Path


class MaterializationBoundary:
    def __init__(self, root):
        self.root = Path(root)
        self.resolved_root = self.root.resolve(strict=True)
        if not self.resolved_root.is_dir():
            raise ValueError('materialization root is not a directory')
        self.identity = self.resolved_root.stat()

    def contains(self, path):
        # Preserve per-child canonical resolution: lexical prefix comparisons
        # would accept junction/symlink escapes and are deliberately not used.
        return Path(path).resolve().is_relative_to(self.resolved_root)

    def verify_root(self):
        current = self.root.resolve(strict=True)
        identity = current.stat()
        if (current != self.resolved_root or identity.st_dev != self.identity.st_dev
                or identity.st_ino != self.identity.st_ino):
            raise ValueError('materialization root changed before publication')
