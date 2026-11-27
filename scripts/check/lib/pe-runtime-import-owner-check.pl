#!/usr/bin/env perl
use strict;
use warnings;

# Static Windows x64 evidence only: full COFF symbols plus named runtime
# imports and their candidate application-directory DLL owners. Never union
# unrelated DLL exports or infer a complete table from PE exports.
my ($binary, $nm, $readobj, $prefix_re, $work) = @ARGV;
my $checked = 0;
my @missing;
my $serial = 0;
sub refuse { die "$_[0]\n"; }
sub tool_output {
    my (@args) = @_;
    my $stem = "$work/tool-" . ++$serial;
    my $status;
    open my $saved_out, '>&', \*STDOUT or refuse('cannot preserve stdout');
    open my $saved_err, '>&', \*STDERR or refuse('cannot preserve stderr');
    open STDOUT, '>', "$stem.out" or refuse('cannot retain tool stdout');
    open STDERR, '>', "$stem.err" or refuse('cannot retain tool stderr');
    $status = system { $args[0] } @args;
    open STDOUT, '>&', $saved_out or refuse('cannot restore stdout');
    open STDERR, '>&', $saved_err or refuse('cannot restore stderr');
    refuse("symbol reader failed (status $status; $stem.err)") if $status != 0;
    refuse('symbol reader output exceeds 16 MiB evidence bound') if -s "$stem.out" > 16 * 1024 * 1024;
    open my $fh, '<', "$stem.out" or refuse('cannot read retained tool output');
    local $/;
    my $text = <$fh> // '';
    $text =~ s/\r\n/\n/g;
    return $text;
}
sub number {
    my ($text, $field) = @_;
    my @values = $text =~ /^\s*\Q$field\E: (0x[0-9a-fA-F]+|[0-9]+)\s*$/mg;
    refuse("missing or ambiguous PE header $field") if @values != 1;
    return $values[0] =~ /^0x/ ? hex($values[0]) : 0 + $values[0];
}
sub headers {
    my ($text, $dll, $full) = @_;
    my @formats = $text =~ /^Format: (\S+)$/mg;
    refuse('unsupported PE format; only Windows x64 is admitted') if @formats != 1 || $formats[0] ne 'COFF-x86-64';
    refuse('unsupported PE machine; only AMD64 is admitted') unless $text =~ /^\s*Machine: IMAGE_FILE_MACHINE_AMD64 \(0x8664\)\s*$/m;
    refuse('PE executable-image evidence missing') unless $text =~ /^\s*IMAGE_FILE_EXECUTABLE_IMAGE \(0x2\)\s*$/m;
    my $is_dll = $text =~ /^\s*IMAGE_FILE_DLL \(0x2000\)\s*$/m ? 1 : 0;
    refuse('expected candidate PE DLL owner') if $dll && !$is_dll;
    refuse('expected candidate executable, not DLL') if !$dll && $is_dll;
    if ($full) {
        refuse('no full COFF symbol table; stripped exports are insufficient')
            unless number($text, 'PointerToSymbolTable') > 0 && number($text, 'SymbolCount') > 0;
    }
}
sub run_check {
    refuse('bad PE checker invocation') unless defined($work) && @ARGV == 5;
    mkdir $work or refuse('cannot create private PE evidence directory');
    my $image = tool_output($readobj, '--file-headers', '--coff-imports', $binary);
    headers($image, 0, 1);
    refuse('delay imports are unsupported coverage')
        if number($image, 'DelayImportDescriptorRVA') != 0 || number($image, 'DelayImportDescriptorSize') != 0 || $image =~ /^DelayImport \{/m;
    my $all = tool_output($nm, '-a', $binary);
    refuse('no readable full COFF symbols') unless $all =~ /\S/;
    my $undef = tool_output($nm, '-u', $binary);
    my @imports = $image =~ /^Import \{\n(.*?)^\}/msg;
    my $import_openers = () = $image =~ /^Import\s*\{/mg;
    refuse('incomplete PE import block evidence') if $import_openers != @imports;
    refuse('PE import descriptor bound exceeded') if @imports > 256;
    my $import_rva = number($image, 'ImportTableRVA');
    my $import_size = number($image, 'ImportTableSize');
    refuse('incomplete PE import-table evidence')
        if (($import_rva == 0 || $import_size == 0) && @imports) || ($import_rva != 0 && $import_size != 0 && !@imports) || (($import_rva == 0) != ($import_size == 0));
    my %by_owner;
    my %imported;
    my $import_count = 0;
    my $parsed_symbol_rows = 0;
    for my $block (@imports) {
        my @owners = $block =~ /^  Name: (.+)$/mg;
        refuse('invalid or ambiguous PE import DLL owner') if @owners != 1 || $owners[0] !~ /\A[A-Za-z0-9_.-]+\.dll\z/i;
        my $owner = $owners[0];
        my @symbols = $block =~ /^  Symbol: (.*?) \(([0-9]+)\)$/mg;
        my $rows = () = $block =~ /^  Symbol:/mg;
        $parsed_symbol_rows += $rows;
        refuse('unsupported PE import symbol rendering') if @symbols != $rows * 2;
        while (@symbols) {
            my $name = shift @symbols;
            my $hint = shift @symbols;
            refuse('ordinal-only imports are unsupported coverage') if $name eq '';
            refuse('PE import count bound exceeded') if ++$import_count > 16384;
            next unless $name =~ /\A(?:$prefix_re)/;
            refuse('unsupported decorated runtime import name') unless $name =~ /\A[A-Za-z_][A-Za-z0-9_]*\z/;
            $by_owner{$owner}{$name} = 1;
            $imported{$name} = 1;
        }
    }
    my $all_symbol_rows = () = $image =~ /^\s*Symbol:/mg;
    refuse('unmatched PE import symbol evidence') if $parsed_symbol_rows != $all_symbol_rows;
    my $directory = $binary;
    $directory =~ s{\\}{/}g;
    $directory =~ s{/[^/]+\z}{} or $directory = '.';
    refuse('runtime provider count bound exceeded') if keys(%by_owner) > 64;
    for my $owner (sort keys %by_owner) {
        my $provider = "$directory/$owner";
        refuse("runtime import owner unavailable in candidate application directory: $owner") unless -f $provider && -r $provider;
        my $exports = tool_output($readobj, '--file-headers', '--coff-exports', $provider);
        headers($exports, 1, 0);
        my $start = number($exports, 'ExportTableRVA');
        my $size = number($exports, 'ExportTableSize');
        refuse('invalid PE export directory bounds') if $start > 0xffffffff || $size > 0xffffffff || $start + $size > 4294967296;
        my @entries = $exports =~ /^Export \{\n(.*?)^\}/msg;
        my $export_openers = () = $exports =~ /^Export\s*\{/mg;
        refuse('incomplete PE export block evidence') if $export_openers != @entries;
        refuse('PE export count bound exceeded') if @entries > 65536;
        refuse('incomplete PE export directory evidence') if (($start == 0 || $size == 0) && @entries) || (($start == 0) != ($size == 0));
        my %names;
        my %forwarded;
        my $parsed_export_values = 0;
        for my $entry (@entries) {
            my @name = $entry =~ /^  Name: (.*)$/mg;
            refuse('ambiguous PE export-name evidence') if @name != 1;
            my $values = () = $entry =~ /^  (?:RVA|ForwardedTo):/mg;
            refuse('ambiguous PE export-value evidence') if $values != 1;
            $parsed_export_values += $values;
            next if $name[0] eq '';
            refuse('duplicate PE export-name evidence') if exists $names{$name[0]};
            if ($entry =~ /^  ForwardedTo: .+$/m) {
                $forwarded{$name[0]} = 1;
                $names{$name[0]} = 0;
                next;
            }
            $names{$name[0]} = number($entry, 'RVA');
        }
        my $all_export_names = () = $exports =~ /^\s*Name:/mg;
        my $all_export_values = () = $exports =~ /^\s*(?:RVA|ForwardedTo):/mg;
        refuse('unmatched PE export records') if $all_export_names != @entries || $all_export_values != $parsed_export_values;
        for my $name (sort keys %{$by_owner{$owner}}) {
            ++$checked;
            refuse("forwarded runtime export is unsupported coverage: $owner:$name") if $forwarded{$name};
            if (!exists($names{$name}) || $names{$name} == 0) { push @missing, "$owner:$name"; next; }
            refuse("forwarded runtime export is unsupported coverage: $owner:$name") if $names{$name} >= $start && $names{$name} < $start + $size;
        }
    }
    for my $line (split /\n/, $undef) {
        next unless $line =~ /\S/;
        refuse('unsupported undefined COFF symbol rendering') unless $line =~ /^\s*U\s+(\S+)\s*$/;
        my $name = $1;
        if ($name =~ /\A__imp_((?:$prefix_re).*)\z/) {
            ++$checked;
            push @missing, "COFF:$name" unless $imported{$1};
        } elsif ($name =~ /\A(?:$prefix_re)/) {
            ++$checked;
            # A same-name PE import does not define a missing direct thunk.
            # Only the explicit __imp_ address form may use the IAT owner fact.
            push @missing, "COFF:$name";
        }
    }
}
my $ok = eval { run_check(); 1 };
if (!$ok) { my $why = $@ || 'unknown PE evidence failure'; $why =~ s/\s+\z//; print "ERROR — Windows x64 import-owner evidence unavailable ($why)\n"; exit 2; }
print "checked\t$checked\n";
print "missing\t$_\n" for @missing;
exit(@missing ? 1 : 0);
