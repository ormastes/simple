use strict;
use warnings;
use Test::More;
open my $f, '<', 'scripts/resource/process-tree-rss-watchdog.pl' or die $!;
my $source = do { local $/; <$f> };
my ($fn) = $source =~ /(sub windows_target_compile_flags \{.*?\n\})/s;
die 'missing target selection' unless $fn;
eval $fn; die $@ if $@;
for my $target ('x86_64-w64-windows-gnu', 'aarch64-w64-windows-gnu', 'x86_64-w64-mingw32') {
    is_deeply([windows_target_compile_flags('gnu', "clang\nTarget: $target\n")], ['-municode'], "$target Unicode startup");
}
for my $target ('x86_64-pc-windows-msvc', 'x86_64-pc-windows-msvc19.42.0') {
    is_deeply([windows_target_compile_flags('gnu', "clang\nTarget: $target\n")], [], "$target preserves MSVC startup");
}
is_deeply([windows_target_compile_flags('cl', "clang\nTarget: x86_64-pc-windows-msvc\n")], [], 'clang-cl unchanged');
for my $identity ("clang\n", "clang\nTarget: x86_64-unknown-linux-gnu\n") {
    eval { windows_target_compile_flags('gnu', $identity) };
    ok($@, 'unknown or missing target fails closed');
}
done_testing();
