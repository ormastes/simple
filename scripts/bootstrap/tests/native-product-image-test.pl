#!/usr/bin/env perl
use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/../lib";
use BootstrapNativeImage qw(verify_native_image);
use File::Temp qw(tempdir);
use Test::More;

my $root = tempdir(CLEANUP => 1);
sub image {
    my $bytes = "\0" x 1024;
    substr($bytes, 0, 2) = 'MZ';
    substr($bytes, 60, 4) = pack('V', 128);
    substr($bytes, 128, 4) = "PE\0\0";
    substr($bytes, 132, 4) = pack('vv', 0x8664, 1);
    substr($bytes, 148, 4) = pack('vv', 240, 0x22);
    substr($bytes, 152, 2) = pack('v', 0x20b);
    substr($bytes, 168, 4) = pack('V', 4096);
    substr($bytes, 208, 8) = pack('VV', 8192, 512);
    substr($bytes, 392, 8) = ".text\0\0\0";
    substr($bytes, 400, 16) = pack('VVVV', 512, 4096, 512, 512);
    substr($bytes, 428, 4) = pack('V', 0x60000020);
    return $bytes;
}
sub accepts {
    my ($bytes, $system, $machine) = @_;
    my $path = "$root/product.exe";
    open my $f, '>:raw', $path or die $!;
    print {$f} $bytes;
    close $f or die $!;
    chmod 0700, $path;
    return eval { verify_native_image($path, $system // 'MINGW64_NT-10.0', $machine // 'x86_64'); 1 } // 0;
}
ok(accepts(image()), 'valid bounded PE32+ executable');
my $arm = image(); substr($arm, 132, 2) = pack('v', 0xaa64);
ok(accepts($arm, 'MSWin32', 'arm64'), 'ARM64 host matches ARM64 image');
ok(!accepts($arm), 'wrong architecture rejected');
for my $case (
    ['DOS absent', 0, 'NO'],
    ['PE offset before DOS end', 60, pack('V', 32)],
    ['PE offset outside file', 60, pack('V', 0xffffffff)],
    ['PE signature wrong', 128, "XX\0\0"],
    ['COFF object lacks executable flag', 150, pack('v', 0)],
    ['DLL rejected', 150, pack('v', 0x2022)],
    ['32-bit characteristics rejected', 150, pack('v', 0x122)],
    ['PE32 optional header rejected', 152, pack('v', 0x10b)],
    ['zero sections rejected', 134, pack('v', 0)],
    ['unbounded section count rejected', 134, pack('v', 97)],
    ['unbounded optional header rejected', 148, pack('v', 65535)],
    ['zero entry rejected', 168, pack('V', 0)],
    ['entry outside section rejected', 168, pack('V', 7000)],
    ['non-executable entry rejected', 428, pack('V', 0x40000040)],
    ['raw section truncated rejected', 412, pack('V', 900)],
    ['raw section overlaps headers rejected', 412, pack('V', 1)],
    ['section virtual extent rejected', 404, pack('V', 8192)],
) {
    my ($name, $offset, $replacement) = @$case;
    my $bytes = image(); substr($bytes, $offset, length $replacement) = $replacement;
    ok(!accepts($bytes), $name);
}
for my $length (0, 20, 63, 140, 180, 420, 1023) {
    ok(!accepts(substr(image(), 0, $length)), "truncated image $length rejected");
}
my $elf = "\x7fELF\x02\x01" . ("\0" x 10) . pack('vv', 2, 62) . ("\0" x 44);
ok(accepts($elf, 'Linux', 'x86_64'), 'existing ELF64 host support retained');
ok(!accepts($elf), 'ELF is not accepted on Windows');
ok(!accepts(image(), 'Darwin', 'x86_64'), 'unsupported host remains fail closed');
if (@ARGV) {
    require POSIX;
    my @host = POSIX::uname();
    ok(eval { verify_native_image($ARGV[0], $host[0], $host[4]); 1 }, 'actual host executable container validates');
}
done_testing();
