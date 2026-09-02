#!/usr/bin/env perl
use strict;
use warnings;
use Cwd qw(realpath);
use Errno qw(EEXIST ENOENT);
use Fcntl qw(O_RDONLY O_DIRECTORY O_NOFOLLOW F_GETFD F_SETFD FD_CLOEXEC);
use File::Basename qw(dirname basename);

@ARGV == 2 or die "usage: $0 STAGING FINAL\n";
my ($staging, $final) = @ARGV;
dirname($staging) eq dirname($final) or die "generation publication parents differ\n";
my $parent_path = dirname($final);
my $canonical_parent = realpath($parent_path);
defined($canonical_parent) && $canonical_parent eq $parent_path
    or die "generation publication parent is not canonical\n";
for my $leaf (basename($staging), basename($final)) {
    $leaf =~ /\A[A-Za-z0-9._-]+\z/ && $leaf ne q{.} && $leaf ne q{..}
        or die "unsafe generation publication leaf\n";
}
sysopen(my $parent, $parent_path, O_RDONLY | O_DIRECTORY | O_NOFOLLOW)
    or die "open generation publication parent: $!\n";
my $fd_flags = fcntl($parent, F_GETFD, 0);
defined($fd_flags) && defined(fcntl($parent, F_SETFD, $fd_flags | FD_CLOEXEC))
    or die "seal generation publication parent descriptor: $!\n";
my @parent_identity = stat($parent);
@parent_identity or die "stat generation publication parent: $!\n";
my $staging_leaf = basename($staging);
my $final_leaf = basename($final);
my @staging_identity = lstat($staging);
@staging_identity && -d _ && !-l _ or die "staging generation is not physical\n";
!lstat($final) && $! == ENOENT or die "generation publication final exists\n";
chdir($parent) or die "bind generation publication parent: $!\n";
my @bound_parent = stat(q{.});
@bound_parent && $bound_parent[0] == $parent_identity[0] &&
    $bound_parent[1] == $parent_identity[1]
    or die "generation publication parent identity changed\n";
my @bound_staging = lstat($staging_leaf);
@bound_staging && $bound_staging[0] == $staging_identity[0] &&
    $bound_staging[1] == $staging_identity[1] && -d _ && !-l _
    or die "staging generation identity changed\n";
if (($ENV{SIMPLE_BOOTSTRAP_TEST_AUTHORITY_PUBLISH_SWAP_PARENT} // q{}) eq 1) {
    my $swapped = "$parent_path.swapped.$$";
    rename($parent_path, $swapped) or die "inject parent swap: $!\n";
    mkdir($parent_path, 0700) or die "inject replacement parent: $!\n";
}
rename($staging_leaf, $final_leaf) or die "atomic generation rename: $!\n";
my @final_identity = lstat($final_leaf);
@final_identity && $final_identity[0] == $staging_identity[0] &&
    $final_identity[1] == $staging_identity[1] && -d _ && !-l _
    or die "published generation identity changed\n";
my $failure;
if (($ENV{SIMPLE_BOOTSTRAP_TEST_AUTHORITY_PUBLISH_FAIL_FREEZE} // q{}) eq 1) {
    $failure = "injected generation freeze failure\n";
} elsif (!chmod(0500, $final_leaf)) {
    $failure = "freeze published generation: $!\n";
}
my $visible_parent = realpath($parent_path);
my @visible_identity = defined($visible_parent) ? stat($parent_path) : ();
if (!defined($visible_parent) || $visible_parent ne $parent_path ||
        !@visible_identity || $visible_identity[0] != $parent_identity[0] ||
        $visible_identity[1] != $parent_identity[1]) {
    $failure ||= "generation publication parent changed during commit\n";
}
if (defined($failure)) {
    my $quarantine;
    for my $attempt (0 .. 1023) {
        my $candidate = ".rejected.$final_leaf.$$.$attempt";
        next if lstat($candidate);
        if (rename($final_leaf, $candidate)) {
            $quarantine = $candidate;
            chmod(0500, $quarantine);
            last;
        }
        next if $! == EEXIST;
        die $failure . "quarantine published generation: $!\n";
    }
    defined($quarantine) or die $failure . "quarantine namespace exhausted\n";
    die $failure;
}
my @sealed = lstat($final_leaf);
@sealed && $sealed[0] == $staging_identity[0] &&
    $sealed[1] == $staging_identity[1] && (($sealed[2] & 0222) == 0)
    or die "published generation was not sealed\n";
exit 0;
