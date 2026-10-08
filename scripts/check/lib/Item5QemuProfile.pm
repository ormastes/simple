package Item5QemuProfile;
use strict;
use warnings;

# Mirrors the nine PureDatabase boundary sizes plus the 1025-row no-match
# case in pure_database_bitmap_query.spl. Bitmap words are ceil(rows / 32).
# NEON counts only full 4-word vector groups; SVE/RVV count each tail vector.
my @DB_ROW_COUNTS = (31, 32, 33, 511, 512, 513, 1023, 1024, 1025, 1025);
my %PROFILE = (
    'aarch64-neon' => {
        triple => 'aarch64-linux-gnu', qemu => 'qemu-aarch64',
        sysroot => '/usr/aarch64-linux-gnu', cpu => 'max',
        db_lanes => 4, loop_policy => 'full-vectors-only',
        loop_model => 'neon-full-u32x4-plus-scalar-tail',
    },
    'aarch64-sve-vq1' => {
        triple => 'aarch64-linux-gnu', qemu => 'qemu-aarch64',
        sysroot => '/usr/aarch64-linux-gnu', cpu => 'max,sve-max-vq=1',
        db_lanes => 4, loop_policy => 'tail-vector', loop_model => 'sve-ceil-u32x4',
    },
    'aarch64-sve-vq2' => {
        triple => 'aarch64-linux-gnu', qemu => 'qemu-aarch64',
        sysroot => '/usr/aarch64-linux-gnu', cpu => 'max,sve-max-vq=2',
        db_lanes => 8, loop_policy => 'tail-vector', loop_model => 'sve-ceil-u32x8',
    },
    'aarch64-sve-vq4' => {
        triple => 'aarch64-linux-gnu', qemu => 'qemu-aarch64',
        sysroot => '/usr/aarch64-linux-gnu', cpu => 'max,sve-max-vq=4',
        db_lanes => 16, loop_policy => 'tail-vector', loop_model => 'sve-ceil-u32x16',
    },
    'aarch64-sve2-vq1' => {
        triple => 'aarch64-linux-gnu', qemu => 'qemu-aarch64',
        sysroot => '/usr/aarch64-linux-gnu', cpu => 'max,sve-max-vq=1',
        db_lanes => 4, loop_policy => 'tail-vector', loop_model => 'sve2-artifact-sve-ceil-u32x4',
    },
    'aarch64-sve2-vq2' => {
        triple => 'aarch64-linux-gnu', qemu => 'qemu-aarch64',
        sysroot => '/usr/aarch64-linux-gnu', cpu => 'max,sve-max-vq=2',
        db_lanes => 8, loop_policy => 'tail-vector', loop_model => 'sve2-artifact-sve-ceil-u32x8',
    },
    'aarch64-sve2-vq4' => {
        triple => 'aarch64-linux-gnu', qemu => 'qemu-aarch64',
        sysroot => '/usr/aarch64-linux-gnu', cpu => 'max,sve-max-vq=4',
        db_lanes => 16, loop_policy => 'tail-vector', loop_model => 'sve2-artifact-sve-ceil-u32x16',
    },
    'riscv64-rvv128' => {
        triple => 'riscv64-linux-gnu', qemu => 'qemu-riscv64',
        sysroot => '/usr/riscv64-linux-gnu', cpu => 'rva23u64,vlen=128,elen=64',
        db_lanes => 4, loop_policy => 'tail-vector', loop_model => 'rvv-ceil-u32x4',
    },
    'riscv64-rvv256' => {
        triple => 'riscv64-linux-gnu', qemu => 'qemu-riscv64',
        sysroot => '/usr/riscv64-linux-gnu', cpu => 'rva23u64,vlen=256,elen=64',
        db_lanes => 8, loop_policy => 'tail-vector', loop_model => 'rvv-ceil-u32x8',
    },
);

sub profile {
    my ($name) = @_;
    return unless defined($name) && exists $PROFILE{$name};
    my $profile = { %{$PROFILE{$name}}, name => $name };
    my $iterations = 0;
    for my $rows (@DB_ROW_COUNTS) {
        my $words = int(($rows + 31) / 32);
        if ($profile->{loop_policy} eq 'full-vectors-only') {
            $iterations += int($words / $profile->{db_lanes});
        } else {
            $iterations += int(($words + $profile->{db_lanes} - 1) / $profile->{db_lanes});
        }
    }
    $profile->{db_loops} = $iterations;
    $profile->{db_queries} = scalar @DB_ROW_COUNTS;
    return $profile;
}

1;
