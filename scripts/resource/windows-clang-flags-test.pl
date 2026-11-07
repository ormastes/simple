use strict;
use warnings;
use Test::More;
use FindBin;
use File::Spec;
my $path = shift @ARGV // File::Spec->catfile($FindBin::Bin, 'process-tree-rss-watchdog.pl');
die 'usage: windows-clang-flags-test.pl [watchdog-source]' if @ARGV;
open my $fh, '<', $path or die $!;
my $text = do { local $/; <$fh> };
my ($functions) = $text =~ /(sub windows_compile_flags \{.*?)(?=\n# Publish a queried compiler identity)/s;
die 'production functions not located' unless defined $functions;
sub win_path { return 'C:/Git/usr/bin/sh.exe' }
eval $functions; die $@ if $@;
for my $cc ('clang','clang-19.exe','clang-cl.exe','x86_64-w64-mingw32-clang.exe','aarch64-w64-mingw32-clang','/clang/bin/x86_64-w64-mingw32-clang.exe','C:\LLVM\x86_64-w64-mingw32-clang.exe') {
    local $ENV{CC} = $cc;
    my @flags = eval { windows_compile_flags() };
    ok(!$@ && @flags, "accept $cc");
    ok(grep($_ eq '-fuse-ld=lld', @flags), "LLD mandatory for $cc");
}
for my $cc ('gcc','gcc.exe','cl','cl.exe','x86_64-w64-mingw32-gcc.exe','x86_64-w64-mingw32-cl.exe','x86_64-w64-mingw32-clang.exe.bat','not-clang.exe') {
    local $ENV{CC} = $cc;
    eval { windows_compile_flags() };
    like($@, qr/cl\/gcc are not permitted/, "reject $cc");
}
is_deeply([windows_target_compile_flags('gnu', "clang version 19\nTarget: x86_64-w64-mingw32\n")], ['-municode'], 'MinGW requires unicode startup');
is_deeply([windows_target_compile_flags('gnu', "clang version 19\nTarget: x86_64-pc-windows-msvc\n")], [], 'MSVC target does not require MinGW flag');
eval { windows_target_compile_flags('gnu', "clang version 19\nTarget: x86_64-unknown-linux-gnu\n") };
like($@, qr/unsupported Windows/, 'reject Linux target');
eval { windows_target_compile_flags('gnu', 'clang version 19') };
like($@, qr/has no target/, 'reject absent target');
like($text, qr/\$identity =~ \/clang\/i or die "compiler identity is not clang/, 'independent identity validation retained');
done_testing();
