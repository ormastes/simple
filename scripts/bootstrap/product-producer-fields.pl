#!/usr/bin/env perl
use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/lib";
use BootstrapProductProducer qw(read_product_producer);
@ARGV == 5 or die "expected receipt mode compiler SHA source-root\n";
my %proof = read_product_producer(@ARGV);
for my $key (qw(source_snapshot_path source_snapshot_sha256 runtime_authority_path runtime_capsule_path runtime_capsule_sha256)) {
    my $value = $proof{$key} // '';
    $value !~ /[\t\r\n\0]/ or die "invalid producer field encoding\n";
    print "$key\t$value\n";
}
