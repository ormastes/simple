package BootstrapProductSelection;
use strict;
use warnings;
use Exporter 'import';
use Digest::SHA qw(sha256_hex);
our @EXPORT_OK = qw(product_selection selection_fields);

sub read_regular {
    my ($path) = @_;
    $path =~ m{\A(?:/|[A-Za-z]:/)} && -f $path && !-l $path
        or die "selection requires an absolute regular file: $path\n";
    open my $file, '<:raw', $path or die "cannot read selection input\n";
    local $/;
    my $bytes = <$file>;
    close $file or die "cannot close selection input\n";
    return $bytes;
}

sub product_selection {
    my ($canonical, $spec_list, $subsystem) = @_;
    $subsystem =~ /\A(?:compiler|interpreter|loader)\z/ or die "invalid selection subsystem\n";
    my $canonical_bytes = read_regular($canonical);
    my @rows = split /\n/, $canonical_bytes;
    shift(@rows) eq "subsystem\tlevel\tpath\tsha256" or die "invalid canonical inventory header\n";
    my (%row, $total);
    $total = 0;
    for my $line (@rows) {
        my @f = split /\t/, $line, -1;
        @f == 4 && $f[0] =~ /\A(?:compiler|interpreter|loader)\z/ &&
            $f[1] =~ /\A(?:01_unit|02_integration|03_system)\z/ &&
            $f[2] =~ m{\Atest/\Q$f[1]\E/[^\t\r\n\\]+_(?:spec|test)\.spl\z} &&
            $f[3] =~ /\A[0-9a-f]{64}\z/ && $f[2] !~ m{(?:\A|/)\.\.?(?:/|\z)}
            or die "invalid canonical inventory row\n";
        !exists($row{$f[2]}) or die "duplicate canonical owner\n";
        $row{$f[2]} = [$line, @f];
        $total++ if $f[0] eq $subsystem;
    }
    my $list_bytes = read_regular($spec_list);
    length($list_bytes) && $list_bytes =~ /\n\z/ && $list_bytes !~ /[\r\t\0\\]/
        or die "spec list must contain newline-terminated repository paths\n";
    my @paths = split /\n/, $list_bytes, -1;
    pop @paths;
    my (%seen, @selected);
    for my $path (@paths) {
        length($path) && !$seen{$path}++ or die "empty or duplicate selected owner\n";
        exists($row{$path}) or die "selected owner is not in canonical inventory: $path\n";
        $row{$path}[1] eq $subsystem or die "selected owner belongs to another subsystem: $path\n";
        push @selected, $row{$path}[0];
    }
    @selected or die "empty spec list\n";
    return {
        selection_scope => 'ordered-subset',
        canonical_inventory_path => $canonical,
        canonical_inventory_sha256 => sha256_hex($canonical_bytes),
        spec_list_path => $spec_list,
        spec_list_sha256 => sha256_hex($list_bytes),
        canonical_subsystem_owner_count => $total,
        selected_owner_count => scalar(@selected),
        inventory_bytes => "subsystem\tlevel\tpath\tsha256\n" . join('', map { "$_\n" } @selected),
        rows => \@selected,
    };
}

sub selection_fields {
    my ($selection) = @_;
    return join('', map { "$_=$selection->{$_}\n" }
        qw(selection_scope canonical_inventory_path canonical_inventory_sha256 spec_list_path
           spec_list_sha256 canonical_subsystem_owner_count selected_owner_count));
}
1;
