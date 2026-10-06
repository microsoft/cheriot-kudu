#!/usr/bin/perl
%instr_all  = (); 
%instr_nobr = ();

#---------------------------------------------------------------
# Start of the main code body

$infile_name  = $ARGV[0];
$outfile_name = $infile_name;
$outfile_name =~ s/\.log$/\.clog/g;
open(INFILE, "<$infile_name") or die "ERROR: Cant open file $infile_name for read\n";
open(OUTFILE, ">$outfile_name") or die "ERROR: Cant open file $outfile_name for write\n";


while ($line = <INFILE>) {
  if ($line =~ s/^\s*\d+\s+\d+\s+// ) {
    print OUTFILE $line;
  }
}

close INFILE;
close OUTFILE;


