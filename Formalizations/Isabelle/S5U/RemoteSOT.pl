#! /usr/bin/perl -w

use strict "vars";
use Getopt::Std;
use HTTP::Request::Common;
use LWP;
use File::Temp qw/ mkstemp /;
#------------------------------------------------------------------------------
my $SystemOnTPTPFormReplyURL = "http://www.cs.miami.edu/~tptp/cgi-bin/SystemOnTPTPFormReply";

# my $ProxyAndPort = "http://proxy.math.uni-bonn.de:3128";
my $ProxyAndPort = "";

my $TemporaryFile = "/tmp/RemoteSOT_XXXXXX";

my %URLParameters = (
    "NoHTML" => 1,
    "QuietFlag" => "-q2",
    "SubmitButton" => "RunParallel",
    "ProblemSource" => "UPLOAD",
    "AutoModeTimeLimit" => 300,
    "AutoMode" => "-cE",
    "AutoModeSystemsLimit" => 3,
    "X2TPTP" => "",
    );
#------------------------------------------------------------------------------
    my $URL;
    my %Options;
    my @Content;
    my $Key;
    my $ReportInfo;
    my $ReportLevel;
    my $MyAgent;
    my $Request;
    my $Response;
    my $TempHandle;
    my $Line;

#----Get format and transform options if specified
    getopts("hfw:r:q:t:c:l:s:SPp:a:y:",\%Options);

#----Help
    if (exists($Options{'h'})) {
        print("Usage: RemoteSOT <options> [<File name>]\n");
        print("    <options> are ...\n");
        print("    -h              - print this help\n");
        print("    -w[<status>]    - list available ATP systems\n");
        print("    -rr             - recommend ATP systems at level\n");
        print("    -r<type><level> - report type (i,c,s,t) at level (0,2)\n");
        print("    -q<quietness>   - control amount of output\n");
        print("    -t<timelimit>   - CPU time limit for system\n");
        print("    -c<automode>    - one of N, E, S\n");
        print("    -l<syslimit>    - maximal systems for automode\n");
        print("    -s<system>      - specified system to use\n");
        print("    -f              - force use of inappropriate system\n");
        print("    -S              - TSTP format output\n");
        print("    -p<filename>    - TPTP problem name\n");
        print("    -y<proxy:port>  - use this proxy:port\n");
        print("    <File name>     - if not TPTP problem (-- for stdin)\n");
        exit(0);
    }

#----What systems flag
    if (exists($Options{'w'})) {
        $URLParameters{"SubmitButton"} = "ListSystems";
        if (!defined($Options{'w'}) || $Options{'w'} eq "") {
            $URLParameters{"ListStatus"} = "READY";
        } else {
            $URLParameters{"ListStatus"} = $Options{'w'};
        }
        delete($URLParameters{"AutoMode"});
        delete($URLParameters{"AutoModeTimeLimit"});
        delete($URLParameters{"AutoModeSystemsLimit"});
        $URLParameters{"ProblemSource"} = "TPTP";
    }
#----Quiet flag
    if (exists($Options{'q'})) {
        $URLParameters{"QuietFlag"} = "-q$Options{'q'}";
    }
#----Force flag
    if (exists($Options{'f'})) {
        $URLParameters{"ForceSystem"} = "-force";
    }
#----Proxy
    if (exists($Options{'y'})) {
        $ProxyAndPort = $Options{'y'};
    }
#----Time limit
    if (exists($Options{'t'})) {
        $URLParameters{"AutoModeTimeLimit"} = $Options{'t'};
    }
#----Automode
    if (exists($Options{'c'})) {
        $URLParameters{"AutoMode"} = "-c$Options{'c'}";
    }
#----Systems limit
    if (exists($Options{'l'})) {
        $URLParameters{"AutoModeSystemsLimit"} = $Options{'l'};
    }
#----Selected system. Do after time limit as it gets moved across
    if (exists($Options{'s'})) {
        $URLParameters{"SubmitButton"} = "RunSelectedSystems";
        $URLParameters{"System___$Options{'s'}"} = $Options{'s'};
        $URLParameters{"TimeLimit___$Options{'s'}"} = 
$URLParameters{"AutoModeTimeLimit"};
        delete($URLParameters{"AutoMode"});
        delete($URLParameters{"AutoModeTimeLimit"});
        delete($URLParameters{"AutoModeSystemsLimit"});
    }
#----Recommend systems flag. Do after system because that must get reset
    if (exists($Options{'r'})) {
        if ($Options{'r'} eq "r") {
            $URLParameters{"SubmitButton"} = "RecommendSystems";
            $URLParameters{"ReportFlag"} = "-q0";
        } else {
            $URLParameters{"SubmitButton"} = "ReportSelectedSystems";
            ($ReportInfo,$ReportLevel) = ($Options{'r'} =~ /(.)(.)/);
            if (!defined($ReportInfo) || !defined($ReportLevel)) {
                print("ERROR: Invalid report type or level\n");
                die("\n");
            }
            if ($ReportInfo eq "i") {
                $URLParameters{"SystemInfo"} = "1";
            } elsif ($ReportInfo eq "c") {
                $URLParameters{"Completeness"} = "1";
            } elsif ($ReportInfo eq "s") {
                $URLParameters{"Soundness"} = "1";
            } elsif ($ReportInfo eq "t") {
                $URLParameters{"TSTPData"} = "";
            } else {
                print("ERROR: Invalid report type\n");
                die("\n");
            }
            $URLParameters{"ReportFlag"} = "-q$ReportLevel";
        }
        delete($URLParameters{"AutoMode"});
        delete($URLParameters{"AutoModeTimeLimit"});
        delete($URLParameters{"AutoModeSystemsLimit"});
    }
#----TSTP format output request
    if (exists($Options{'S'})) {
        $URLParameters{"X2TPTP"} = "-S";
    }
#----Request a postprocessing tool (not in help) 
    if (exists($Options{'P'})) {
        $URLParameters{"SubmitButton"} = "ProcessSolution";
        $URLParameters{"QuietFlag"} = "-q01";
    }
#----TPTP file name
    if (exists($Options{'p'})) {
        if ($URLParameters{"SubmitButton"} eq "ProcessSolution") {
            print("ERROR: Not compatible with -P (processing a solution)\n");
            die("\n");
        }
        $URLParameters{"ProblemSource"} = "TPTP";
        $URLParameters{"TPTPProblem"} = $Options{'p'};
    }
#----Password
    if (exists($Options{'a'})) {
        $URLParameters{"CPUPassword"} = $Options{'a'};
    }

#----Get single file name
    if ($URLParameters{"ProblemSource"} eq "UPLOAD") {
        if (scalar(@ARGV) == 0 || (scalar(@ARGV) >= 1 &&
$ARGV[0] eq "--")) {
            ($TempHandle,$TemporaryFile) = mkstemp($TemporaryFile);
            while (defined($Line = <STDIN>)) {
                print($TempHandle $Line);
            }
            close($TempHandle);
            $URLParameters{"UPLOADProblem"} = [$TemporaryFile];
        } else {
            $URLParameters{"UPLOADProblem"} = [shift(@ARGV)];
        }
    }

#DEBUG foreach $Key (keys(%URLParameters)) { print("$Key = $URLParameters{$Key}\n"); }
    $MyAgent = LWP::UserAgent->new;
    if (defined($ProxyAndPort) && $ProxyAndPort ne "") {
        $MyAgent->proxy(['http'],$ProxyAndPort);
    }
    $Request = POST($SystemOnTPTPFormReplyURL,
Content_Type => 'form-data',Content => \%URLParameters);
#DEBUG printf("%s\n",$Request->as_string());
    $Response = $MyAgent->request($Request);

#----Close (and hence delete) the temporary file if it exists
    if (defined($TempHandle)) {
        unlink($TemporaryFile);
    }

    printf("%s\n",$Response->content);

#------------------------------------------------------------------------------
