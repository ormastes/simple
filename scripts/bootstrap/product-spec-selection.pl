#!/usr/bin/env perl
use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/lib";
use BootstrapProductSelection qw(product_selection selection_fields);
my ($mode, $canonical, $list, $subsystem, $selected) = @ARGV;
defined($mode) && (($mode eq 'render' && @ARGV == 4) || ($mode eq 'verify' && @ARGV == 5))
    or die "usage: $0 render|verify CANONICAL SPEC_LIST SUBSYSTEM [SELECTED]\n";
my $selection = product_selection($canonical, $list, $subsystem);
if ($mode eq 'render') {
    print $selection->{inventory_bytes};
} else {
    BootstrapProductSelection::read_regular($selected) eq $selection->{inventory_bytes}
        or die "selected inventory differs from ordered spec list\n";
    print selection_fields($selection);
}
