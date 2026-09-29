#!/usr/bin/env perl
use strict;
use warnings;
use Test::More;

my $package = $ENV{STAGE2_RUNNER_PACKAGE}
    or die "STAGE2_RUNNER_PACKAGE is required\n";
my $path = "$package/scripts/check/lib/bootstrap-stage3-unit-supervisor.pl";
open(my $fh, '<', $path) or die $!;
my $source = do { local $/; <$fh> };
close($fh);

like($source, qr/open\(STDOUT, '\+<&', \$lock_fh\)/,
    'Stage2 systemd client stdout is the supervisor-held lock OFD');
like($source, qr/--pipe'[\s\S]*?'--quiet'/,
    'systemd pipe capability channel suppresses client stdout chatter');
like($source, qr/WorkingDirectory=\$root_exec/,
    'systemd resolves the working directory through the held root descriptor');
like($source, qr/--heavy-lock=\$o\{heavy_lock\}/,
    'gate receives the exact supervisor-validated lock identity');
like($source,
    qr/SIMPLE_STAGE3_OUTER_LOCK_HELD[\s\S]*?SIMPLE_BOOTSTRAP_OUTER_LOCK_PROOF/,
    'caller-controlled service environment denies private lock proof markers');
unlike($source, qr/flock\(\$lock_fh,\s*LOCK_UN\)[\s\S]*?wait_bounded/,
    'heavy lock is not released before the bounded systemd service wait');
like($source,
    qr/missing or non-canonical Stage 2 transaction root[\s\S]*?Stage 2 transaction root collision/,
    'supervisor admits exactly one initially absent transaction root');
like($source,
    qr/legacy Stage 2 sibling authority is forbidden/,
    'supervisor rejects legacy output evidence home tmp and cache aliases');
like($source,
    qr/simple-bootstrap-stage2-transaction-v1[\s\S]*?Stage 2 helper receipt mismatch[\s\S]*?Stage 2 child receipt mismatch/,
    'supervisor independently consumes source and child transaction identities');
like($source, qr/hash_stage2_directory/,
    'supervisor recomputes the runner directory-content framing');

my $gate_path = "$package/scripts/check/lib/bootstrap-stage3-unit-gate.shs";
open(my $gate_fh, '<', $gate_path) or die $!;
my $gate = do { local $/; <$gate_fh> };
close($gate_fh);
like($gate,
    qr/duplicate transaction root[\s\S]*?legacy Stage 2 sibling authority[\s\S]*?simple-bootstrap-stage2-transaction-v1/,
    'gate enforces one transaction authority and consumes its receipt');

done_testing();
