#!/usr/bin/env python3
"""
Populate a pre-formatted FAT32 image with a deterministic 8.3-only tree.
"""

from __future__ import annotations

import math
import struct
import sys
from pathlib import Path


ATTR_DIRECTORY = 0x10
ATTR_ARCHIVE = 0x20
FAT32_FREE = 0x00000000
FAT32_EOC = 0x0FFFFFFF


def to_short_name(name: str) -> bytes:
    upper = name.upper()
    if "." in upper:
        base, ext = upper.rsplit(".", 1)
    else:
        base, ext = upper, ""
    if not base or len(base) > 8 or len(ext) > 3:
        raise ValueError(f"name is not FAT32 8.3 compatible: {name}")

    allowed = set("ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_$%'-@~`!(){}^#&")
    if any(ch not in allowed for ch in base + ext):
        raise ValueError(f"name contains unsupported FAT32 8.3 characters: {name}")

    return base.ljust(8, " ").encode("ascii") + ext.ljust(3, " ").encode("ascii")


class Fat32Seeder:
    def __init__(self, image_path: Path):
        self.image_path = image_path
        self.fp = image_path.open("r+b")
        self._read_bpb()

    def close(self) -> None:
        self.fp.flush()
        self.fp.close()

    def _read_bpb(self) -> None:
        self.fp.seek(0)
        bpb = self.fp.read(512)
        if len(bpb) != 512 or bpb[510:512] != b"\x55\xaa":
            raise RuntimeError("invalid FAT32 boot sector signature")

        self.bytes_per_sector = struct.unpack_from("<H", bpb, 11)[0]
        self.sectors_per_cluster = bpb[13]
        self.reserved_sectors = struct.unpack_from("<H", bpb, 14)[0]
        self.num_fats = bpb[16]
        self.fat_size = struct.unpack_from("<I", bpb, 36)[0]
        self.root_cluster = struct.unpack_from("<I", bpb, 44)[0]
        self.fs_info_sector = struct.unpack_from("<H", bpb, 48)[0]
        self.data_start_sector = self.reserved_sectors + (self.num_fats * self.fat_size)
        self.cluster_size = self.bytes_per_sector * self.sectors_per_cluster
        total_sectors = struct.unpack_from("<I", bpb, 32)[0]
        data_sectors = total_sectors - self.data_start_sector
        self.total_clusters = data_sectors // self.sectors_per_cluster

    def cluster_to_offset(self, cluster: int) -> int:
        sector = self.data_start_sector + (cluster - 2) * self.sectors_per_cluster
        return sector * self.bytes_per_sector

    def _fat_offset(self, cluster: int, fat_index: int) -> int:
        fat_sector = self.reserved_sectors + fat_index * self.fat_size
        return fat_sector * self.bytes_per_sector + cluster * 4

    def read_fat_entry(self, cluster: int) -> int:
        self.fp.seek(self._fat_offset(cluster, 0))
        return struct.unpack("<I", self.fp.read(4))[0] & FAT32_EOC

    def write_fat_entry(self, cluster: int, value: int) -> None:
        packed = struct.pack("<I", value & FAT32_EOC)
        for fat_index in range(self.num_fats):
            self.fp.seek(self._fat_offset(cluster, fat_index))
            self.fp.write(packed)

    def zero_cluster(self, cluster: int) -> None:
        self.fp.seek(self.cluster_to_offset(cluster))
        self.fp.write(b"\x00" * self.cluster_size)

    def read_cluster(self, cluster: int) -> bytearray:
        self.fp.seek(self.cluster_to_offset(cluster))
        return bytearray(self.fp.read(self.cluster_size))

    def write_cluster(self, cluster: int, data: bytes) -> None:
        if len(data) != self.cluster_size:
            raise ValueError("cluster write size mismatch")
        self.fp.seek(self.cluster_to_offset(cluster))
        self.fp.write(data)

    def follow_chain(self, start_cluster: int) -> list[int]:
        chain = []
        cluster = start_cluster
        seen = set()
        while cluster >= 2 and cluster not in seen:
            chain.append(cluster)
            seen.add(cluster)
            nxt = self.read_fat_entry(cluster)
            if nxt >= 0x0FFFFFF8 or nxt < 2:
                break
            cluster = nxt
        return chain

    def alloc_clusters(self, count: int) -> list[int]:
        clusters = []
        for cluster in range(2, self.total_clusters + 2):
            if self.read_fat_entry(cluster) == FAT32_FREE:
                clusters.append(cluster)
                if len(clusters) == count:
                    break
        if len(clusters) != count:
            raise RuntimeError("not enough free FAT32 clusters")

        for index, cluster in enumerate(clusters):
            nxt = clusters[index + 1] if index + 1 < len(clusters) else FAT32_EOC
            self.write_fat_entry(cluster, nxt)
            self.zero_cluster(cluster)
        return clusters

    def _update_fsinfo(self) -> None:
        if self.fs_info_sector == 0:
            return
        free_count = 0
        next_free = 0xFFFFFFFF
        for cluster in range(2, self.total_clusters + 2):
            if self.read_fat_entry(cluster) == FAT32_FREE:
                free_count += 1
                if next_free == 0xFFFFFFFF:
                    next_free = cluster
        off = self.fs_info_sector * self.bytes_per_sector
        self.fp.seek(off)
        fsinfo = bytearray(self.fp.read(512))
        if len(fsinfo) == 512:
            struct.pack_into("<I", fsinfo, 488, free_count)
            struct.pack_into("<I", fsinfo, 492, next_free)
            self.fp.seek(off)
            self.fp.write(fsinfo)

    def _find_free_dir_slot(self, dir_cluster: int):
        chain = self.follow_chain(dir_cluster)
        for cluster in chain:
            data = self.read_cluster(cluster)
            for off in range(0, self.cluster_size, 32):
                if data[off] in (0x00, 0xE5):
                    return cluster, off, data

        new_cluster = self.alloc_clusters(1)[0]
        self.write_fat_entry(chain[-1], new_cluster)
        self.write_fat_entry(new_cluster, FAT32_EOC)
        data = bytearray(b"\x00" * self.cluster_size)
        return new_cluster, 0, data

    def _write_dir_entry(self, dir_cluster: int, name: str, attr: int, start_cluster: int, size: int) -> None:
        cluster, off, data = self._find_free_dir_slot(dir_cluster)
        entry = bytearray(32)
        entry[0:11] = to_short_name(name)
        entry[11] = attr
        struct.pack_into("<H", entry, 20, (start_cluster >> 16) & 0xFFFF)
        struct.pack_into("<H", entry, 26, start_cluster & 0xFFFF)
        struct.pack_into("<I", entry, 28, size)
        data[off:off + 32] = entry
        self.write_cluster(cluster, data)

    def _initialize_directory_cluster(self, cluster: int, parent_cluster: int) -> None:
        data = bytearray(b"\x00" * self.cluster_size)

        dot = bytearray(32)
        dot[0:11] = b".          "
        dot[11] = ATTR_DIRECTORY
        struct.pack_into("<H", dot, 20, (cluster >> 16) & 0xFFFF)
        struct.pack_into("<H", dot, 26, cluster & 0xFFFF)

        dotdot = bytearray(32)
        dotdot[0:11] = b"..         "
        dotdot[11] = ATTR_DIRECTORY
        struct.pack_into("<H", dotdot, 20, (parent_cluster >> 16) & 0xFFFF)
        struct.pack_into("<H", dotdot, 26, parent_cluster & 0xFFFF)

        data[0:32] = dot
        data[32:64] = dotdot
        self.write_cluster(cluster, data)

    def create_directory(self, parent_cluster: int, name: str) -> int:
        cluster = self.alloc_clusters(1)[0]
        self._initialize_directory_cluster(cluster, parent_cluster)
        self._write_dir_entry(parent_cluster, name, ATTR_DIRECTORY, cluster, 0)
        return cluster

    def write_file(self, parent_cluster: int, name: str, content: bytes) -> None:
        if len(content) == 0:
            self._write_dir_entry(parent_cluster, name, ATTR_ARCHIVE, 0, 0)
            return

        cluster_count = math.ceil(len(content) / self.cluster_size)
        clusters = self.alloc_clusters(cluster_count)
        for index, cluster in enumerate(clusters):
            start = index * self.cluster_size
            chunk = content[start:start + self.cluster_size]
            if len(chunk) < self.cluster_size:
                chunk = chunk + b"\x00" * (self.cluster_size - len(chunk))
            self.write_cluster(cluster, chunk)
        self._write_dir_entry(parent_cluster, name, ATTR_ARCHIVE, clusters[0], len(content))

    def seed_tree(self, src_dir: Path, dir_cluster: int | None = None) -> None:
        if dir_cluster is None:
            dir_cluster = self.root_cluster
        for entry in sorted(src_dir.iterdir(), key=lambda path: path.name.upper()):
            try:
                to_short_name(entry.name)
            except ValueError as exc:
                print(f"[fat32_seed] skipping incompatible path: {entry.relative_to(src_dir.parent)} ({exc})", file=sys.stderr)
                continue

            if entry.is_dir():
                child_cluster = self.create_directory(dir_cluster, entry.name)
                self.seed_tree(entry, child_cluster)
            else:
                self.write_file(dir_cluster, entry.name, entry.read_bytes())
        self._update_fsinfo()


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        print("usage: fat32_seed.py <image> <source_dir>", file=sys.stderr)
        return 2
    image_path = Path(argv[1])
    source_dir = Path(argv[2])
    if not image_path.exists():
        print(f"image not found: {image_path}", file=sys.stderr)
        return 1
    if not source_dir.is_dir():
        print(f"source dir not found: {source_dir}", file=sys.stderr)
        return 1

    seeder = Fat32Seeder(image_path)
    try:
        seeder.seed_tree(source_dir)
    finally:
        seeder.close()
    print(f"[fat32_seed] seeded {image_path} from {source_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
