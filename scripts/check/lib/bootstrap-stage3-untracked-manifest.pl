#!/usr/bin/env perl
use strict;
use warnings;
use Digest::SHA qw(sha256_hex);
use File::Find ();
use File::Spec ();

@ARGV == 3 or die "usage: $0 <git-root> <nul-path-list> <records-output>\n";
my ($root, $list_path, $records_path) = @ARGV;

sub bytes_digest {
    my ($bytes) = @_;
    return sha256_hex($bytes);
}

sub file_digest {
    my ($path) = @_;
    open my $fh, '<:raw', $path or die "open $path: $!\n";
    my $sha = Digest::SHA->new(256);
    $sha->addfile($fh);
    close $fh or die "close $path: $!\n";
    return $sha->hexdigest;
}

sub nested_head {
    my ($path) = @_;
    return undef unless -e File::Spec->catfile($path, '.git');
    open my $fh, '-|', 'git', '-C', $path, 'rev-parse', '--verify', 'HEAD'
        or return undef;
    local $/;
    my $output = <$fh> // '';
    return undef unless close $fh;
    return $output;
}

sub directory_digest {
    my ($relative, $absolute) = @_;
    my $head = nested_head($absolute);
    return bytes_digest($head) if defined $head;

    my @files;
    File::Find::find(
        {
            no_chdir => 1,
            wanted => sub {
                return unless -f $File::Find::name;
                push @files, $File::Find::name;
            },
        },
        $absolute,
    );
    my $manifest = '';
    for my $file (sort { $a cmp $b } @files) {
        my $file_relative = substr($file, length($root) + 1);
        $manifest .= $file_relative . ':' . file_digest($file) . "\n";
    }
    return bytes_digest($manifest);
}

open my $list, '<:raw', $list_path or die "open $list_path: $!\n";
local $/;
my $raw = <$list> // '';
close $list or die "close $list_path: $!\n";
my @paths = sort { $a cmp $b } grep { length $_ } split /\0/, $raw, -1;

open my $records, '>>:raw', $records_path
    or die "open $records_path: $!\n";
for my $path (@paths) {
    my $absolute = File::Spec->catfile($root, split m{/}, $path);
    if (-l $absolute) {
        my $target = readlink($absolute);
        defined $target or die "readlink $absolute: $!\n";
        print {$records} 'untracked-link:', length($path), ':', $path, ':',
            length($target), ':', bytes_digest($target), "\n";
    } elsif (-f $absolute) {
        print {$records} 'untracked-file:', length($path), ':', $path, ':',
            (-x $absolute ? 1 : 0), ':', file_digest($absolute), "\n";
    } elsif (-d $absolute) {
        print {$records} 'untracked-dir:', length($path), ':', $path, ':',
            directory_digest($path, $absolute), "\n";
    } else {
        die "unsupported untracked path: $path\n";
    }
}
close $records or die "close $records_path: $!\n";
