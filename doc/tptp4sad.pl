#!/usr/bin/perl -w

# $tptpath should point to your copy of the TPTP library if you
# have one, or to some nonexistent path if you have no local copy
local $tptpath = "/home/andrei/prj/TPTP-v3.1.1";
local $tptpurl = "tptp.org";        # URL of the TPTP website
local $wget    = "/usr/bin/wget";   # your wget executable

# Usage:
# 1.  % ./tptp4sad                  # reads a TPTP problem from stdin
# 2.  % ./tptp4sad ./myproblem.p    # reads a problem from the file
# 3.  % ./tptp4sad ALG001-3.p       # looks for the problem in $tptpath
#                                   # or tries to take it from $tptpurl
#
# Any "include"d axiom set will be looked for in $tptpath or at $tptpurl
# This script requires the include instructions to be given one in a row,
# and any such a line should not contain any more non-whitespace symbols.
# All the problem files in TPTP v.2.6.0 satisfy this requirement.

###################### Here the script starts ##############################

local $url = "$wget -q -O - http://$tptpurl/cgi-bin/DVTPTP2WWW/view_file.pl";
local $link = shift; local $rempr = 0; local $remax = 0; local $gotit = 0;
local *IH;

if (not $link) { *IH = *STDIN; }
elsif (not open(IH, "<$link"))
{
    $link =~ /^([A-Z]{3})[0-9]{3}[-+][0-9]{1,2}(\.[0-9]{3})?\.p$/
        or die "Fail: malformed TPTP Problem name: $link\n";

    $rempr = 0, open(IH, "<$tptpath/Problems/$1/$link")
        or $rempr = 1, open(IH, "$url?Category=Problems\\\&Domain=$1\\\&File=$link|")
            or die "Fail: cannot run wget\n";
}

if ($rempr) { while (<IH>) { last if (/\<pre\>(%-*)?$/); } }

while (<IH>)
{
    last if ($rempr and /^\<\/pre\>/);
    s/\<[^=][^>]+\>//g if ($rempr);
    $gotit = 1;

    s/%/#/, print, next unless
        (/^\s*include\s*\(\s*'Axioms\/([A-Z]{3}[0-9]{3}[-+][0-9]{1,2}\.(ax|eq))'\s*\)\s*\.\s*$/);

    $link = $1; next if ($link =~ /^EQU001|eq$/);

    $remax = 0, open(IH2, "<$tptpath/Axioms/$link")
        or $remax = 1, open(IH2, "$url?Category=Axioms\\\&File=$link|")
            or die "Fail: cannot run wget\n";

    if ($remax) { while (<IH2>) { last if (/\<pre\>(%-*)?$/); } }

    while (<IH2>)
    {
        last if ($remax and /^\<\/pre\>/);
        s/\<[^=][^>]+\>//g if ($remax);
        s/%/#/; print; $gotit = 1
    }

    if ($remax) { while (<IH2>) {}; }
    close IH2;

    die "Fail: axiom set $link not found\n" unless ($gotit);
}

if ($rempr) { while (<IH>) {}; }
close IH;

die "Fail: problem $link not found\n" unless ($gotit);
