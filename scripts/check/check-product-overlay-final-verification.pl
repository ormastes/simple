use strict;
use warnings;
use File::Basename qw(dirname);
my ($canonical, $source, $fixture) = @ARGV;
defined($fixture) or die "requires canonical materializer, fixture source and output parent\n";
require lib;
lib->import(dirname($canonical) . '/lib');
require BootstrapProductOverlay;

sub bytes {
    open my $f, '<:raw', $_[0] or die $!;
    local $/; my $data = <$f>; close $f or die $!;
    return $data;
}
sub write_bytes {
    open my $f, '>:raw', $_[0] or die $!;
    print {$f} $_[1] or die $!; close $f or die $!;
}
my $source_file = "$source/src/lib/value.spl";
my $original = bytes($source_file);
my $digest = \&BootstrapProductOverlay::digest;
my $verify = \&BootstrapProductOverlay::verify_product_overlay;
for my $mode (qw(normal output source manifest)) {
    my $overlay = "$fixture/final-$mode";
    mkdir $overlay or die $!;
    my $manifest = "$fixture/final-$mode.tsv";
    my (%calls, $verified);
    my ($ok, $error);
    {
        no warnings 'redefine';
        local *BootstrapProductOverlay::digest = sub {
            ++$calls{$_[0]}; return $digest->(@_);
        };
        local *BootstrapProductOverlay::verify_product_overlay = sub {
            ++$verified;
            if ($mode ne 'normal') {
                my $path = $mode eq 'source' ? $source_file :
                    $mode eq 'output' ? "$overlay/src/lib/value.spl" : $manifest;
                write_bytes($path, bytes($path) . "tampered\n");
            }
            return $verify->(@_);
        };
        $ok = eval { BootstrapProductOverlay::materialize_product_overlay($source, $overlay, $manifest); 1 };
        $error = $@;
    }
    # Restore the private fixture even when the source fault is rejected.
    write_bytes($source_file, $original) if $mode eq 'source';
    ($verified // 0) == 1 or die "mandatory final verifier was skipped or repeated\n";
    if ($mode eq 'normal') {
        $ok or die $error;
        for my $path ("$overlay/src/lib/value.spl", "$overlay/src/app/alias/value.spl") {
            ($calls{$path} // 0) == 1 or die "output digest must run exactly once in final verification\n";
            bytes($path) eq $original or die "physical alias output differs\n";
        }
        ($calls{$source_file} // 0) == 2 or die "independent source revalidation was removed\n";
        keys(%calls) == 3 or die "unexpected digest membership\n";
        print "PASS final-verification-output-digest-budget-and-source-revalidation\n";
    } else {
        !$ok or die "final $mode mutation accepted\n";
        my $expected = $mode eq 'output' ? 'overlay member differs' : 'overlay catalog/source binding differs';
        index($error, $expected) >= 0 or die "unexpected $mode rejection: $error";
        print "PASS final-verification-rejects-$mode-mutation\n";
    }
}
