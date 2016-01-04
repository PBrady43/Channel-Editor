#!/usr/bin/perl -w
use strict;
use Tk;
use Tk::Pane;
use Tk::Dialog;
use Tk::DialogBox;
require Tk::LabEntry;

use scan_database;    #See https://www.mythtv.org/wiki/Perl_API_examples
use Getopt::Long;
use warnings FATAL => qw(uninitialized);

my $version='Release 0.03 201601004';

#changes 
# 4 Dec 2014   Beta 2
#  Abolished separate 'select' and 'acton' menus - single 'edit' instead.
#  Undo function added
#  New sort rules for channel nos like 99_99 or _99_990.
#  icon not changed with hide/unhide POST operations
#  put 'unknown' for multiplex frequency/standard if no multiplexes found
#  Toggle channel names <-> callsigns. They are same in UK but not in US. 
#  diagnostics section added; ability to read diagnostic file
#  Duplicates now identify duplicate numbers, callsigns and channel names.
#  Demo mode flagged in header.

# 6 Dec 2015   Beta 3
#  Bug in MYTHCONFDIR and config.xml fixed 
#  View menu now has 'sort by' 
#  fixed mis-alignment of US channel numbers with - eg 7-1 and 7_1.
#         Should accept ANY not digit separator now.
#  Added xmltidlist to diagnostics - for possible future development. 
# 8 Dec 2015
#  further fix to CONFIGDIR
#  button now 'Update database!!'
#  Added command line option 'nodemo'
#  Changed 'reinstate all' to 'undo all'
#  Reverse sort added
#  Custom sorting - turn multi-sort rules into simple (mplex and duplcates).
#  Correct 'channels.export' in help text.
#
#10 Dec 2015  Beta 5
# Corrected two ValidatePost lines - need 'post' not 'raw' .  Oops!  but see later!
# Remove 'die' twice in favour of 'print .. exit'.  May be needed later if trapping included 
# Allowed --demo
# Icon in post - only default it if not returned in get (needs defaulting on 0.27 & 0.28)
# if MYTHCONFDIR do not search further folders. 

#15 Dec 2015.
#  6 digit channel nunbers misaligned.  Now allow 9 digits.
#  Added postmortem (via eval).  More routines to be trapped.
#  better sorting of multiplexes, channel count added.
#  added track mechanism - put in log at postmortem
#  Added postmortem checks and track calls.
#  3 import rules introduced and updated help.
#  reinstated 'raw' not 'post' for ValidatePost operations  (2 author's channels need it).
#  Released as beta6.
# 
#16~19 Dec 2015
# change name - spoof not diagnostics for input - less confusing
# allow spoofing even if own backend turned off
# Allow channel numbers like _23
# Fix for GetMultiplexinfo with no multiplexes but channels show mpx 32767
# Simplebox tracking confusing - track first line only
# don't re-sort after an edit, revise 'reverse' mechanism.
# Sort by query now does query then name
# multiplex frequency now in MHz.
# --spoof now in help
# warn of escapes in callsign.channel name to log
# Beta 7.
#
#23 Dec 2015
#Introduced rule4 in import.
#Two spare fields added to export for future use.
#Don't re-sort after edits
#Null undo supported - revealing previous
#add os to log.
#add third 'spare' field in export data
#version 'Release 0.01 20151223'
#
#4 Jan 2016
# Error-wrap initial code
# Fix uninitialised $sub in sub track
# Show right heading after toggling name
# Changed export file for future additions
# a) added title line
# b) separator now []:[]  not just :
# version 0.03 20160104

my $backend; my $spoof; my %ChanData; my %MplexInfo;my %sources;my $nodemo=0; my $demo=1;
my $mythversion='0'; 
my @sorted;
my $UserInput;
my $SelectChoice='S';
my @log; my @undo=(' :-1'); my @previousundo =(' :-1'); my @track;

GetOptions("backend:s"      => \$backend,
           "spoof:s"        => \$spoof,
           "demo!"          => \$demo);

my @CustomSortRules=(\&RuleChanId);
my $CustomState=0;
my @CustomDescription=();
my $NameChoice='CallSign';    #or ChannelName
my $text='Fully functional mode.';
   $text="Running in demo mode." if $demo;

my $main; my $font; my $menubar; my $FileMenu; my $ListMenu; my $EditMenu; my $HelpMenu;
my $headings; my $pane; my $pane2;

eval{
    #create main window
    &mylog(0,'creating main');
    $main=MainWindow->new();
    $main->geometry($main->screenwidth . 'x' . $main->screenheight . '+0+0');
    $main->Label(-text => "MythTV Channel Editor.  Version $version    $text")->pack;

    $font = $main->fontCreate('body',
       -family=>'courier',
       -weight=>'normal',
       -size=> 14);

    my $headerfont = $main->fontCreate('header',
       -family=>'courier',
       -weight=>'bold',
       -size=>14);


    #menu bar and pull down menus
    &mylog(0,'creating menubar'); 
    $menubar=$main->Frame(-relief =>"raised",
                   -borderwidth   =>2)  
                   ->pack (-anchor => "nw",
                           -fill   => "x");

    &mylog(0,'creating file menu');
    $FileMenu= $menubar-> Menubutton(-text =>"File", -menuitems  => [
          [ Button => "Import",               -command   => \&Import],
          [ Button => "Export",               -command   => \&Export],
          [ Button => "Update Database!!",    -command     => \&Save],
          [ Button => "Exit",                 -command     => sub {exit}],
          ]) ->pack(-side => "left");

    &mylog(0,'creating list menu');
    $ListMenu= $menubar-> Menubutton(-text =>"View", -menuitems  => [
          [ Button => "Sort by ChanId",       -command   => sub{&ListBy(\&RuleChanId,'Channel Id')}],
          [ Button => "Sort by Channel no.",  -command   => sub{&ListBy(\&RuleChanNum,'Channel number')}],
          [ Button => "Sort by Source",       -command   => sub{&ListBy(\&RuleSource,'Source')}],
          [ Button => "Sort by Source:Multiplex",
                                              -command   => sub{&ListBy(\&RuleMpx,'Source:Multiplex', \&RuleSimpleMpx)}],
          [ Button => "Sort by Name",         -command   => sub{&ListBy(\&RuleCallSign,'Channel name')}],
          [ Button => "Sort by Hidden ",      -command   => sub{&ListBy(\&RuleHid,'Hidden')}],
          [ Button => "Sort by Duplicates",
                                              -command   => sub{&ListBy(\&RuleDuplicates, 'Duplicates',\&RuleSimpleDups)}],
          [ Button => "Sort by Query",        -command   => sub{&ListBy(\&RuleQuery,'Query', \&RuleSimpleQuery)}],
          [ Button => "Sort by Final",        -command   => sub{&ListBy(\&RuleNew,'Final')}],
          [ Button => "Reverse sort",         -command   => sub {&ReverseSort}],
          [ Separator =>''],
          [ Button => "Custom sort",          -command   => \&Custom],
          [ Separator =>''],
          [ Button => "Multiplexes",          -command   => \&ListMultiplexes],                
          [ Button => "Log",                  -command   => \&ShowLog],
          [ Separator =>''],
          [ Button => "Toggle name",          -command   => \&ToggleName],
          [ Button => "Create Custom Sort",   -command   => sub{&CreateCustom('new')}],

          ]) ->pack(-side => "left");

    &mylog(0,'creating edit menu');
    $EditMenu   = $menubar -> Menubutton(-text =>"Edit", -menuitems  => [
          [ Button => "Key range",    -command   => \&EditbyKey],
          [ Button => "Source:mpx",   -command   => \&EditbyMpx],
          [ Button => "Channel name", -command   => \&EditbyName],
          [ Separator =>''],
          [ Button => "Undo",         -command   => \&EditUndo],
          [ Button => "Undo All",     -command   => \&EditReinstate],
          ]) ->pack(-side => "left");

    &mylog(0,'creating help menu');
    $HelpMenu  = $menubar -> Menubutton(-text => "Help", -menuitems  => [
          [ Button => "Version",       -command   => \&Version],       
          [ Button => "Help",          -command   => \&help],
          [ Button => "Diagnostics",   -command   => \&Diagnostics],
          ]) ->pack(-side => "left");

    #column headings
    &mylog(0,'creating headings');
    $headings=$main ->Label(-text => '', -font => $headerfont)->pack(-anchor => "nw");

    #create the scrolled pane 
    &mylog(0,'creating scrolled pane');
    $pane = $main->Scrolled("Pane", Name => 'fred',
            -scrollbars => 'e',
            -sticky     => 'we',
            -gridded    => 'y',
            );
       $pane->Frame;
       $pane->pack(-expand => 1,
                    -fill => 'both');

    #create label for content
    &mylog(0,'creating content label');
    $pane2= $pane -> Label(-text => '', -justify => 'left', -font => $font)-> pack(-side=>"left");

    #Off we go!
    &preamble;
    &ListBy(\&RuleChanId,'Channel Id');
    $text .="\n\nRestart with --nodemo if you really intend changing the database." if $demo;
    &SimpleBox("Note \n$text");
    MainLoop;
};
&postmortem($@) if ($@);
exit 0;



sub preamble{
    eval{
        my $text="unset";
        &track();
        if (defined $spoof){$demo=1; $text=$spoof};
        &mylog(0, "$0  Version=$version, demo=$demo, spoof=$text, os=$^O");
        &InterrogateBackend;
    };
    &postmortem($@) if ($@);
}

#-- Edit menu routines --------

sub EditbyKey{
    return if $CustomState;
    eval{
        my $first; my $last;
        
        my $userchoice = &ChooseAction('Give key (eg 9) or key range (eg 7:11)');
        &track("$userchoice  $UserInput");
        return if $userchoice eq 'Cancel';
        
        if ($UserInput =~ /^\s?(\d+)\s?$/){
           ($first,$last)=($1,$1);
        }elsif ($UserInput =~ /^\s?(\d*):(\d*)\s?$/ ){
            ($first, $last)=($1,$2);
        }else{
            &SimpleBox("Input:  $UserInput not recognised");
            return;
        }
        if (($last<$first) or ($last>=scalar @sorted)){
            &SimpleBox("Sorry:  Limits of $first to $last not valid.");
            return;
        }
        @previousundo=@undo; @undo=();
        for ($first .. $last){
            push @undo, "$ChanData{$sorted[$_]}{NewState}:$sorted[$_]";
            $userchoice=$ChanData{$sorted[$_]}{Visible} if ($userchoice eq 'R');
            $ChanData{$sorted[$_]}{NewState}=$userchoice;
            substr($ChanData{$sorted[$_]}{State},1,1)=' ';  #resets Q
        }
        &MarkDuplicates;
        &refresh;
    };
    &postmortem($@) if ($@);
}

sub EditbyMpx{
    eval{
        return if $CustomState;
        my $userchoice = &ChooseAction('Give source or source:multiplex');
        &track("$userchoice  $UserInput");
        return if $userchoice eq 'Cancel';
       
        my $src; my $mpx;
        if ($UserInput =~ /^\s?(\d+):(\d+)$/){
            ($src, $mpx)=($1, $2);
        }elsif ($UserInput =~ /^\s?(\d+)\s?$/){
            ($src, $mpx)=($1, '*');
        }else {
            &SimpleBox(" $UserInput not recognised");
            return;
        }
        @previousundo=@undo; @undo=();
        for (keys %ChanData){
            if ($ChanData{$_}{Source} == $src){
                if (($mpx eq '*') || ($mpx == $ChanData{$_}{MplexId})){
                    push @undo, "$ChanData{$_}{NewState}:$_";
                    $userchoice=$ChanData{$sorted[$_]}{Visible} if ($userchoice eq 'R');
                    $ChanData{$_}{NewState}=$userchoice;
                    substr($ChanData{$_}{State},1,1)=' ';  #reset Q
                }
            }
        }

        &MarkDuplicates;
        &refresh;
    };
    &postmortem($@) if ($@);
}

sub EditbyName{
    return if $CustomState;
    eval{
        my $userchoice = &ChooseAction('Give text to match in channel name');
        &track("$userchoice  $UserInput");
        return if $userchoice eq 'Cancel';
        @previousundo=@undo; @undo=();
        for (keys %ChanData){
            if ($ChanData{$_}{$NameChoice} =~ /$UserInput/i){
                push @undo, "$ChanData{$_}{NewState}:$_";
                $userchoice=$ChanData{$sorted[$_]}{Visible} if ($userchoice eq 'R');
                $ChanData{$_}{NewState}=$userchoice;
                substr($ChanData{$_}{State},1,1)=' ';  #reset Q
            }
        }
        &MarkDuplicates;
        &refresh;
    };
    &postmortem($@) if ($@);
}

sub EditReinstate{
   return if $CustomState; 
   eval{
        #reinstate all channels to original state
        track();
        @previousundo=@undo; @undo=();
        for (keys %ChanData){
            push @undo, "$ChanData{$_}{NewState}:$_";
            $ChanData{$_}{NewState}=$ChanData{$_}{Visible};
            substr($ChanData{$_}{State},1,1)=' ';  #resets Q
        }
        &MarkDuplicates;
        &refresh;
    };
    &postmortem($@) if ($@);
}

sub EditUndo{
    return if $CustomState;
    eval{
        &track();
        #unless (scalar @undo){ &SimpleBox('Sorry - cannot undo'); return};
        for (@undo){
            (my $action, my $id)= split ':', $_;
            if ($id<0){&SimpleBox('Sorry - cannot undo'); return};
            $ChanData{$id}{NewState}=$action;
            substr($ChanData{$id}{State},1,1)=' ';  #resets Q
        }
        @undo=@previousundo; @previousundo=(':-1');
        &MarkDuplicates;
        &refresh;
    };
    &postmortem($@) if ($@);   
}

#------------------Diagnostics, logging and and error handling ----------------

sub mylog{
    #log and (optionally) print message
    (my $print, my $message)=@_;
    if ($print){print "$message\n"};
    push @log, $message;
}

sub ShowLog{
    &track;
    &ShowHeading(0);
    my $text=join "\n", @log;
#   $text .= "\nTracking\n";
#   $text .=join "\n", @track;
    $pane2 -> configure(-text => $text, -anchor =>"nw", -justify=>'left');   
}


sub getdiagnostics{
     # author's debugging aid
    return '' unless (defined $spoof);
    (my $section)=@_;
    my $out='';  my $interesting=0; my $count=0;
    unless (open FN, "<$spoof"){print "Cannot open $spoof\n";exit 0};
    while (<FN>){
        $interesting=0 if (/^##/);
        if ($interesting){
            $out .= $_;
            $count++;
        }
        $interesting=1 if (/##$section/);
     }
    close FH;
#    &mylog(0, "$section: read $count lines.");
    return $out;
}

sub postmortem{
    #unexpected error
    (my $myerror, my @params)=@_;
    &track();
    chomp $myerror;
    #postmortem exceptions:
    exit 0 if ($myerror =~ /^_TK_EXIT_/);   #deliberate exit
   
    &mylog(1,"Failure:  $myerror");
    &mylog(0,"Call stack:");
    my $i=0;    
    while (my @stack=caller($i)){
        &mylog(0,sprintf "line %4d called $stack[3]", $stack[2]);
        if (($i==1) and (scalar @params >0)){
             &mylog(0,"Calling params:");
             for (@params){
                &mylog(0, "  $_");
            }
        }
        $i++;
    }
    $myerror= "There has been a fatal error\n$myerror\n";
    $myerror .= "We cannot continue.\nDo you want diagnostics?";
    my $reply=&CheckOk($myerror);
    &Diagnostics if ($reply eq 'ok');
    exit 0;
}

sub Diagnostics{

    #add tracking to log
    &mylog(0,"\nTracking");
    &mylog(0, join "\n", @track);
    
    #show log
    unless (open DI, ">channels.diags") {&SimpleBox("Cannot open channels.diags $!"); return};
    print DI "##log\n";
    print DI join("\n", @log), "\n";

    #enough if spoof input
    if (defined $spoof){
        close DI;
        &SimpleBox("Short diagnostics written to 'channels.diags'.");
        exit 0;
    }

    #now sources
    OutputDiags ('sources', 'VideoSourceList');
    for (sort keys %sources){
        #multiplexes
        OutputDiags ("multiplex$_", "GetVideoMultiplexList?SourceID=$_");
        #Channels
        OutputDiags ("channels$_", "GetChannelInfoList?SourceID=$_&OnlyVisible=false&Details=true");
        #XMLT
        OutputDiags ("XMLTV$_", "GetXMLTVIdList?SourceID=$_");
    }
    if ($mythversion gt '0.28.2015'){OutputDiags('##wsdl', 'wsdl')};
    print DI "##end\n";
    close DI;
    &SimpleBox('Diagnostic info written to channels.diags');
}
  
sub OutputDiags{
    (my $tag, my $urltail)=@_;
    my $temp;
    print DI "\n##$tag\n";
    ReadBackend($backend. '/Channel/' . $urltail, $temp);
    $temp =~ s/></>\n</g;
    print DI "$temp\n";           
}

sub track{

    #put entry in track log
    (my $param)=@_;
    $param ||='';
    my $line=(caller(0))[2];
    my $i=1;
    my $sub;
    while ($sub= (caller($i++))[3]){
       last if ($sub ne '(eval)'); 
    }
    $sub||='';
    push @track, sprintf "%7d   $sub $param", $line;
    shift @track if (scalar @track >25);   #only keep 25
}

 
#-------------Misc support routines ---------

sub SimpleBox{
    (my $message)=@_;
    my ($line1)=split "\n", $message;
    &track($line1);
    my $box=$main->Dialog(
        -title => "Channel Editor",
        -text => $message,
        -buttons => ['ok'],
        -default_button => "ok")->Show();
}
sub ChooseAction{
    (my $question)=@_;
    &track(); 
    $UserInput='';
    my $box=$main->DialogBox(
        -title => "Channel Editor",
        -buttons => ['Hide', 'Unhide', 'Delete', 'Revert','Cancel'],
        -default_button => "Cancel");
    $box-> add('LabEntry',-textvariable=>\$UserInput, -width =>30,
                -label=> "$question   ",
                -labelPack => [-side => 'left'])->pack;
    my $answer = $box -> Show();
    if ($answer eq 'Hide'){return 'H'};
    if ($answer eq 'Unhide'){return ' '};
    if ($answer eq 'Delete'){return 'D'};
    if ($answer eq 'Revert'){return 'R'};
    return 'Cancel';
}

sub CheckOk{
    (my $question)=@_;
    my $box=$main->DialogBox(
        -title => 'Channel Editor',
        -buttons => ['ok','cancel'],
        -default_button => "ok");
    $box-> add("Label",
                -text      => "$question   ")->pack;
    $box -> Show();
#    $box||='cancel';  
}

sub MarkDuplicates{
    #identify duplicates
    eval{
        &track();
        my %dupcallsign; my %dupnumber; my %dupchanname; my $item; my $new;
        foreach (keys %ChanData){
            if ($ChanData{$_}{NewState} eq ' '){
                #count callsigns
                $dupcallsign{$ChanData{$_}{CallSign}}++;
                #count channel names
                $dupchanname{$ChanData{$_}{ChannelName}}++;
                #count channel nos.
                $dupnumber{$ChanData{$_}{ChanNum}}++;
            }
        }

        #now mark them
        foreach (keys %ChanData){
           $new=' ';
           if ($ChanData{$_}{NewState} eq ' '){
               if ($dupcallsign{$ChanData{$_}{CallSign}} >1)    {$new='d'};
               if ($dupnumber{$ChanData{$_}{ChanNum}} >1)       {$new='d'};
               if ($dupchanname{$ChanData{$_}{ChannelName}} >1) {$new='d'};
           } 
           substr($ChanData{$_}{State},0,1)=$new;
        }
    };
    &postmortem($@) if ($@);
}

sub state{
    #eg call if (&state($_,'d')) returns non zero if state found,
    return 1+index($ChanData{$_[0]}{State}, $_[1]);
}

#----File menu items--------

sub Import{
    return if $CustomState;
    eval{
        &track();
        &mylog(0,"\nImporting channel.export");

        # scan import file
        my $rule; my $index; my %Chans;
        unless (open  FH, "<channels.export") {&SimpleBox("Cannot open channel.export"); return};
        <FH>;       #ignore first descriptive line (future enhancement) 
        while (<FH>){
            chomp;
            for $rule (1,2,3){     #leave out rule 4 for now - same as 1
                    (my $action)= split /\[\]:\[\]/, $_;
                    if (index('HVD',$action)<0){
                        &SimpleBox("You have an invalid file:\n $_");
                        return;
                    }
                $index=&fingerprint($rule, $_);
                $Chans{$index}{count}++;
                if (($Chans{$index}{count}==1) or ($action ne 'H')){
                    $Chans{$index}{action}=$action;
                }
            }
        }
        close FH;

        my $details;
        #now scan database

        for (sort keys %ChanData){
            $details=&ExportLine($_);
            for $rule (1,2,3){
                $index=&fingerprint($rule, $details);
                if (defined $Chans{$index}{count}) {
                    $Chans{$index}{count} +=1000;
                }
           }
           #mark all initially as queried
           substr($ChanData{$_}{State},1,1)='Q';
        }

        #now try to match them 
        
        my @rulestats = (0,0,0,0,0); my $match;
        @previousundo=@undo; @undo=(); 

        for (sort keys %ChanData){
            $details=&ExportLine($_);
            for $rule (1,2,3,4){
                $match=0;
                $index=&fingerprint($rule, $details);
                my $count=$Chans{$index}{count};
                next unless (defined $count);
                if ($count == 1001){
                    $match=1;
                }elsif (($rule==4) and (($count % 1001)==0)){
                      $match=1 if ($Chans{$index}{action} eq 'H');
                }

                if ($match){
                    my $action=$Chans{$index}{action};
                    #rule matched!
                    if ($ChanData{$_}{NewState} ne $action){  #change it
                        $action =~ s/V/ /;
                        #keep undo info
                        push @undo, "$ChanData{$_}{NewState}:$_";
                        #update it
                        $ChanData{$_}{NewState}= $action;
                    }
                    #update 'Q' flag
                    substr($ChanData{$_}{State},1,1)=' ';
                    #stats
                    $rulestats[$rule]++;
                    last;
                }
            }
        }

        #log the rule stats
        &mylog(0,'Rule stats');
        for (1 .. 4){
            &mylog(0,"   Rule $_  $rulestats[$_]");
        }

        #count queries
        &mylog(0, "\nThe following channels in the database could not be matched");
        my $queries=0; $match=0;
        for (keys %ChanData){
            if (&state($_,'Q')){
                $queries++ ;
                &mylog(0,ExportLine($_));
            }else{  $match++;
            }
        }
        &mylog(0,'(none)') if ($queries==0);

       &MarkDuplicates;
        my $out='Import complete';
        $out .= "\n\n$match channels matched, $queries not.";
        if  ($queries){
            $out .= "\n\nSee channels marked 'Q'";
            $out .= "\nor log for details";
            &ListBy(\&RuleQuery,'Query');
        }else{
            #leave page as it was!
            &refresh;
        }        
        &SimpleBox($out);
    };
    &postmortem($@) if ($@);
}

sub fingerprint{
    (my $rule, my $line)=@_;
    (my $state, my $chno, my $src, my $mpx, my $freq, my $name)=split /\[\]:\[\]/, $line;

    if ($rule ==1){
        return "1:$name";
    }elsif ($rule==2){
        return "2:$chno:$name";
    }elsif ($rule==3){
        return "3:$src:$freq:$name";
    }elsif ($rule ==4){
        return "1:$name";   #as rule 1
    }else{
        postmortem ("Import rule $rule missing");
    }
}

sub Export{
    eval{
        #export state of play
        &track();
        &mylog(0,"\nExporting to channel.export"); 
        unless (open  FH, ">channels.export"){
            &SimpleBox("Cannot open channels.export"); return};

        print FH &ExportLine(-1)."\n";
        my $count=0;
        for (sort keys %ChanData){
            my $L=&ExportLine($_);
            print FH "$L\n";
            $count++;
        }
        close FH;
        &track("$count channels exported");
        &mylog(0, "$count channels exported");
        &SimpleBox("$count channels exported to 'channels.export'");
    };
    &postmortem($@) if ($@);
}

sub ExportLine{
    (my $id)=@_; 
    if ($id<0){         #give heading = format of returns
        return 'NewState[]:[]ChanNum[]:[]Source[]:[]MplexId[]:[]Frequency[]:[]CallSign';
    }
    my $ch=$ChanData{$id}{ChanNum};
    $ch =~ s/\s//g;
    my $state=$ChanData{$id}{NewState};
    $state='V' if ($state eq ' ');
    my $freq=$MplexInfo{$ChanData{$id}{Source} .':'. $ChanData{$_}{MplexId}}{Frequency};
    return  join '[]:[]', ($state, $ch, $ChanData{$id}{Source},$ChanData{$_}{MplexId}, $freq, $ChanData{$id}{CallSign});    
}

sub Save{
    eval{
        return if $CustomState;
        #update database and exit
        &track();
        
        my %counts;
        $counts{H}=0; $counts{D}=0; $counts{' '}=0;
        for (keys %ChanData){
            if ($ChanData{$_}{Visible} ne $ChanData{$_}{NewState}){
                $counts{$ChanData{$_}{NewState}}++;
            }
        }
        if ($counts{H} + $counts{' '} + $counts{D} ==0){
            &SimpleBox('There are no changes to save to the database.');
            return;
        }   
        my $text= "\nYou have chosen to hide $counts{H},";
        $text .= "\n unhide $counts{' '} and delete $counts{D} channels.\n";
        $text .= "\nDo you have a good backup?\nAre you sure you wish to update the database?";
        if ($demo==0){
            $text .="\n\nWARNING!!!\n You are NOT in demo mode!\n";
        }else{
            $text .="\n\n .. but you are in demo mode only\n";
        }
        my $reply=CheckOk($text);
        return if ($reply ne 'ok');
        
        &mylog(0,"\nUpdating database:  demo=$demo");
        &mylog(0,"Will hide $counts{H}, unhide $counts{' '}, delete $counts{D}");

        if (!defined $spoof){
            my $action;
            for (sort keys %ChanData){
                $action=$ChanData{$_}{NewState};
                
                if ($ChanData{$_}{Visible} eq $action){   #do nothing
                }elsif ($action eq 'H'){&HideOrUnhide($_, 'false', 'Hid     ');
                }elsif ($action eq ' '){&HideOrUnhide($_, 'true', 'Unhid   ');
                }elsif ($action eq 'D'){&DeleteChannel($_, 'Deleted ');
                }
            } 
        }
        &ShowLog;
    };  #end eval
    &postmortem($@) if ($@);
}

sub HideOrUnhide{
    (my $id,  my $newvisible, my $description)=@_;
    eval{
        my %hash;  my $content;
        ReadBackend($backend . '/Channel/GetChannelInfo?ChanID=' . $id, $content);
        GetAllFields(%hash, $content, '<ChannelInfo', '</ChannelInfo>');
        $hash{Visible}= $newvisible;
        $hash{'#Icon'}='' unless (defined $hash{Icon});    #default it unless now available

        if (ValidatePost(%hash, $backend . '/Channel/UpdateDBChannel', 'quiettest', 12)){
            if ($demo==0){
                ValidatePost(%hash, $backend . '/Channel/UpdateDBChannel', 'raw',12);
            }
            push @log,"ok:    $description $id: $ChanData{$id}{CallSign}";
            $ChanData{$id}{Visible}=$ChanData{$id}{NewState};
        }else{
            push @log,"FAILED $description  $id: $ChanData{$id}{CallSign}";
        }
    };
    &postmortem($@, "id=$id, desc=$description") if ($@);
}

sub DeleteChannel{
    (my $id,  my $description)=@_;
    eval{
        #issue post 
        my %hash;
        &track($id);
        $hash{ChannelID}=$id;
        if (ValidatePost(%hash, "$backend/Channel/RemoveDBChannel", 'quiettest', 1)){
            if ($demo==0){ 
                ValidatePost(%hash, "$backend/Channel/RemoveDBChannel", 'raw', 1);
            }
            push @log,"ok:    $description $id: $ChanData{$id}{CallSign}";
            delete($ChanData{$id});
        }else{
            push @log,"FAILED $description $id: $ChanData{$id}{CallSign}";
        }
    };
    &postmortem($@) if ($@);
}

#----- Sorting and Listing code ---------

sub RuleChanId       {$a <=>$b};
sub RuleCallSign     {lc($ChanData{$a}{$NameChoice}) cmp lc($ChanData{$b}{$NameChoice})};
sub RuleChanNum      {$ChanData{$a}{Sort}            <=> $ChanData{$b}{Sort}};
sub RuleHid          {$ChanData{$b}{Visible}         cmp $ChanData{$a}{Visible}};
sub RuleMpx          {$ChanData{$a}{Source}          <=> $ChanData{$b}{Source} ||
                      $ChanData{$a}{MplexId}         <=> $ChanData{$b}{MplexId}};
sub RuleSimpleMpx    {$ChanData{$a}{Source}          <=> $ChanData{$b}{Source}};    #only used in custom
sub RuleDuplicates   {&state($b,'d')                 <=> &state($a,'d') ||
                     lc($ChanData{$a}{$NameChoice})  cmp lc($ChanData{$b}{$NameChoice})};
sub RuleSimpleDups   {&state($b,'d')                 <=> &state($a,'d')};           #only used in custom
sub RuleSimpleQuery  {&state($b,'Q')                 <=> &state($a,'Q')};           #only used in custom
sub RuleQuery        {&state($b,'Q')                 <=> &state($a,'Q') ||
                     lc($ChanData{$a}{$NameChoice})  cmp lc($ChanData{$b}{$NameChoice})};

sub RuleSource       {$ChanData{$a}{Source}          <=> $ChanData{$b}{Source}};
sub RuleNew          {$ChanData{$b}{NewState}        cmp $ChanData{$a}{NewState}};
sub RuleCustom       {
    &{$CustomSortRules[0]} ||
    &{$CustomSortRules[1]} ||
    &{$CustomSortRules[2]} ||
    &{$CustomSortRules[3]} ||
    &{$CustomSortRules[4]} ||
    &{$CustomSortRules[5]} ||
    $a <=> $b;
}

sub ReverseSort{
    return if $CustomState;
    @sorted=reverse @sorted;
    &refresh;
}

sub ListMultiplexes{
    return if $CustomState;
    eval{
        &track();
        &ShowHeading(0);
        #list sources
        my $out=" Source   Name\n";
        for (sort keys %sources){
            $out .= "    $_     $sources{$_}{SourceName}\n";
        }
        my $total=0;
        #list multiplexes
        $out .= "\n Source  Mplex   Freq (MHz)    Channels  Standard\n";
        for (sort {$MplexInfo{$a}{sort}  <=> $MplexInfo{$b}{sort}} keys %MplexInfo){
            (my $src, my $mpx) =split ":", $_;
            $out .= sprintf "  %3d    %3d     ",$src,$mpx;
            $out .= sprintf " %7.3f  ", $MplexInfo{$_}{Frequency}/1000000;
            $out .= sprintf "  %7d     ", $MplexInfo{$_}{Count};
            $out .= "$MplexInfo{$_}{Standard}\n";
            $total += $MplexInfo{$_}{Count};
        }
        $out .= "\n Total channels:    $total\n";
        $pane2 -> configure(-text => $out, -anchor =>"nw", -justify=>'left');
    };
    &postmortem($@) if ($@);
}
sub ShowHeading{
    (my $show) = @_;
    &track($show);
    my $text='';
    $text="  Key   ChId     ChanNo   Src:Mpx   State Final  Name ($NameChoice)" if $show;
    $headings -> configure(-text => $text, -anchor =>"nw", -justify=>'left');
}

sub ListBy{
    (my $ref, my $desc, my $refcustom)=@_;
    eval{
        &track();
        if ($CustomState==1){
            &CreateCustom('add', $ref, $desc, $refcustom);
            return;
        }
        &MarkDuplicates;
        &ShowHeading(1);
        @sorted=sort {&$ref || $a<=>$b} keys %ChanData;
        &refresh;        
    };
    &postmortem($@) if ($@);
}

sub refresh{
    #rewrite channel data to screen
    eval{
        my $out; my $key=0;
        &track;
        &ShowHeading(1);
        for (@sorted){
            my $state=$ChanData{$_}{Visible}.$ChanData{$_}{State};
            $state =~ s/\s/\./g;
            my $newstate = '  '.$ChanData{$_}{NewState};
            $newstate ='->'.$ChanData{$_}{NewState} 
                        if ($ChanData{$_}{NewState} ne $ChanData{$_}{Visible});
            $newstate='->V' if ($newstate eq '-> ');
            $out .= sprintf "%5d  %5d  %9s %2d:%-5d  %3s   %3s   ", $key++, $_, 
                        $ChanData{$_}{ChanNum}, $ChanData{$_}{Source}, 
                        $ChanData{$_}{MplexId}, $state, $newstate;
            $out .= "$ChanData{$_}{$NameChoice}\n";
        }
        $pane2 -> configure(-text => $out, -anchor =>"nw", -justify=>'left');
    };
    &postmortem($@) if ($@);
}

sub Custom{
    if ($CustomState){
        #fill the array to ensure no holes
        while (scalar @CustomSortRules <6){ push @CustomSortRules , \&RuleChanId};
        $CustomState=0;
    }
    &ListBy(\&RuleCustom);
}
sub CreateCustom{
    #Create custom sort rule
    eval{
        (my $action, my $ref,my $desc, my $refcustom)=@_;
        &track();
        if (defined $refcustom){$ref=$refcustom};    #simplify multi sort rules for custom
        my $items=scalar @CustomDescription;
        if ($action eq 'new'){
            @CustomSortRules=();
            @CustomDescription=();
            $CustomState=1;
        }elsif ($action eq 'add'){
            if ($items < 6){
                push   @CustomSortRules,$ref;
                push   @CustomDescription, $desc;
            }elsif ($items==6){push @CustomDescription, "\n    Limit reached!";
            }
        }
        #put message on screen
        my $out= '    To create a custom sort rule, please select items from
        the View menu in turn, then select Custom Sort.

        Subsequently, just click Custom Sort.
        ';
        if (scalar @CustomDescription){
            $out .= "\n    Items selected so far are:\n\n    ";
            $out .= join "\n    ", @CustomDescription;
        }
        $pane2 -> configure(-text => $out, -anchor =>"nw", -justify=>'left');
    };
    &postmortem($@) if ($@);  
}

sub ToggleName{
    #toggle name between callsign and channelname
    eval{
        if ($NameChoice eq 'CallSign'){
            $NameChoice='ChannelName';
        }else{
            $NameChoice='CallSign';
        }
        &refresh;
    };
    &postmortem($@) if ($@);
}



#-------  Read backend --------

sub InterrogateBackend{

    eval{
        if (!defined $spoof){
            #get backend address
            if ($backend){
                &mylog(1,"Will use backend address $backend");
            }else{
                #look for a config file 
                my @dirs = qw (~/.mythtv/  /home/mythtv/.mythtv/ /etc/mythtv/);
                $_= $ENV{'MYTHCONFDIR'};
                if ($_){
                    unless (m!/$!){$_ .= '/'};
                    @dirs=($_);
                    &mylog(1,"Found environment variable MYTHCONFDIR set to  $_");
                }
                for my $file (@dirs){
                    (my $fn)=glob($file);
                    $fn .='config.xml';
                    if ((defined $fn) && (-e $fn)){
                        unless (open CONFIG, "$fn") {print "Cannot open $fn $!\n"; exit 0};
                        &mylog(1,"Opening $fn");
                        while ($_ = <CONFIG>){
	                        if (m!<Host>(\S+)</Host>!) {
                                $backend=$1; 
                                &mylog(1,"Found host address $backend")};
                        }
                        close CONFIG;
                        last;
                    }else{
                        &mylog(0, "$fn not found");
                    }
                }
            }
            unless ($backend){
                print "Need a backend address - please specify with --backend.\n"; 
                exit 0;
            }
            unless ($backend =~ /:/){$backend .=':6544'};
        }

        #Get video sources
        my $videosource; my %header;my $temp;
        &track('VideoSourceList');
        $temp=&getdiagnostics('sources');
        ReadBackend($backend. '/Channel/VideoSourceList', $temp) unless (defined $spoof);

        if ($temp =~ m!<Version>(.*)</Version>!){$mythversion=$1};
        &mylog(0, "MythTV version $mythversion");
        
        my $reply=FillHashofHash(%sources, $temp, 'VideoSource', 'Id', 'SourceName');
        &mylog(0,"Found $reply video sources");    
         
        for my $source (sort keys %sources){
		    #get source:mpx info
            my %freqs=();
            &track("GetMpxlist $source");

            $temp=&getdiagnostics("multiplex$source");
            unless (defined $spoof){
                ReadBackend($backend . '/Channel/GetVideoMultiplexList?SourceID='.$source, $temp);
            }
            $reply=FillHashofHash(%freqs, $temp, 'VideoMultiplex', 'MplexId',
                                  'Frequency','SIStandard');
            &mylog(0,"Found $reply multiplexes in source $source");
            
            my $multiplexesexist=1;;
            if ($reply == 0){
                #no multiplexes
                $multiplexesexist=0;
                $MplexInfo{"$source:0"}{Frequency}=0;    #'none';
                $MplexInfo{"$source:0"}{Standard}='?';
                $MplexInfo{"$source:0"}{sort}=1000*$source;
                $MplexInfo{"$source:0"}{Count}=0;

            }else{
                for (keys %freqs){
                    $MplexInfo{"$source:$_"}{Frequency}=$freqs{$_}{Frequency};
                    $MplexInfo{"$source:$_"}{Standard}=$freqs{$_}{SIStandard};
                    $MplexInfo{"$source:$_"}{sort}=1000*$source + $_;
                    $MplexInfo{"$source:$_"}{Count}=0;
                 }
            }
            #get channel info
            my %temp;
            &track("ChanInfo $source");
            $temp=&getdiagnostics("channels$source");
            unless (defined $spoof){
                ReadBackend($backend . '/Channel/GetChannelInfoList?SourceID='.$source.
                    '&OnlyVisible=false&Details=true', $temp);
            }
           
            $reply=FillHashofHash(%temp, $temp, 'ChannelInfo', 'ChanId', 'CallSign', 'ChannelName',
                         'ChanNum','Visible', 'MplexId');
            &mylog(0,"Found $reply channels in source $source");
            
            #count channels - put in multiplex hash
            for (keys %temp){
                $temp{$_}{Source}= $source;
                #fix spurious multiplex=32767 in USA satellite data
                $temp{$_}{MplexId}=0 unless $multiplexesexist;
            }
            #add in to main hash
            %ChanData = (%ChanData, %temp);
        }

        #post-process channels:
       
        my $chan;
        foreach (keys %ChanData){
     
            $ChanData{$_}{State}='  ';

            #printable tidy channel number
            $chan=$ChanData{$_}{ChanNum};

            #look for _12_1  (or with - or .) 
            if ($chan =~ /^\s?(\D)(\d+)(\D)(\d+)\s?$/){
                $ChanData{$_}{Sort}=(1024 +$2)*1024 +$4;
                my $L=5-length($2);
                $ChanData{$_}{ChanNum} = ' ' x $L . $1 .  $2 . $3 .sprintf "%-4d ",$4;

            #or 4_1
            }elsif ($chan =~ /^\s?(\d+)(\D)(\d+)\s?$/){
                $ChanData{$_}{Sort}=$1*1024 +$3;
                $ChanData{$_}{ChanNum} = sprintf "  %4d%1s%-4d ",$1,$2, $3;

            #or _23
            }elsif ($chan=~ /^s?(\D)(\d+)\s?$/){
                $ChanData{$_}{Sort}=$2;
                $ChanData{$_}{ChanNum} = sprintf "      %1s%-4d ",$1,$2;

            #or simple numeric
            }elsif ($chan=~ /^\s?(\d+)\s?$/){
                $ChanData{$_}{Sort}=$1;
                $ChanData{$_}{ChanNum} = sprintf "%9d   ",$1;

            }else{
                $ChanData{$_}{Sort}=0;
                $ChanData{$_}{ChanNum}= sprintf "%12s", $chan;
            }
            #final sanity check
            if (length($ChanData{$_}{ChanNum}) != 12){
                &postmortem("Bad formatting of channum $chan");
            } 
                

            #set  'visible' to H or blank
            $ChanData{$_}{Visible}= ($ChanData{$_}{Visible} =~ /true/i)?' ':'H';
            $ChanData{$_}{NewState}= $ChanData{$_}{Visible};

            #count channels for multiplex listing
            my $k = "$ChanData{$_}{Source}:$ChanData{$_}{MplexId}";
            $MplexInfo{$k}{Count}++ if (defined $MplexInfo{$k});
        }
        &track('done');
    };    #end eval
    if ($@ =~ /500 Can't connect to/){
       print "$@\n"; 
       exit 0;
    }
    &postmortem($@) if ($@);
    return;

print "mpx Info at 1088\n";
for (keys %MplexInfo){
   print "id=$_ ";
#   print "freq= $MplexInfo{$_}{Frequency} ";
#   print " std=$MplexInfo{$_}{Standard}";
#   print " sort=$MplexInfo{$_}{sort} 
   print "count=$MplexInfo{$_}{Count}\n";
}
exit 0;


}


#-------help--------

sub Version{
    my $out= "MythTV Channel Editor\nVersion $version";
    $out .= "\n\nGPL license conditons\n\n";
    $out .= "Phil Brady 2015";
    &SimpleBox($out);
}

sub help{
&ShowHeading(0);
my $out = <<"END_HELP";

                MYTHTV CHANNEL EDITOR

DESCRIPTION
    
    This program will allow you to: 

    *  View MythTV channels with various orderings
    *  Edit them to mark them for hiding, unhiding or deletion
    *  Export the settings for use at a later date.
    *  Update the database to implement the changes.

    This will, for example, allow you to 
    *   hide or delete all channels with 'shopping' in the channel name, 
    *   delete those from a distant but interfering transmitter.
    *   Identify and hide or delete channels with duplicated channel.
 
    It uses the Services API interface and requires the perl API module 
    published in the MythTV Wiki 'Perl API examples' page. It has been written,
    tested and validated with MythTV version 0.27.4 in a UK DVB-T environment 
    and with 0.28-pre in USA with over-air ATSC and with cable channels.


PARAMETERS

     The only supported parameters are:
 
    --backend     address or name of backend server and (optionally) port no.

        eg  --backend 192.168.0.2  or --backend 192.168.0.2:6544

        If this is not supplied, then it will search for a backend address
        in a configuration file config.xml.  
   
        If the environment variable MYTHCONFDIR is defined it will search that 
        directory, otherwise it will search  ~/.mythtv/,  ~mythtv/.mythtv/ and
        /etc/mythtv/ in turn.
  
        A port number of 6544 is assumed unless otherwise specified. 

    --nodemo     (or --demo)

        The script normally runs in demonstration mode and will NOT update the 
        database, though all logging, screen shots etc will suggest otherwise.

        If you wish to start in 'live' mode and really update the database then 
        start the script with the --nodemo option. 

    --spoof <filename>

        This was initially developed as a support and development feature, but
        is now also used to for delivering the tutorial.

        It reads a diagnostic file rather than a backend to extract API data. 
        Updating the database is inhibited in this mode.


FILE

    File ->  Export 

             This will write a file 'channels.export' so that settings can be 
             re-imported at a later data after a fresh channel scan.  

             For each channel it will write:
             V, H or D for visible, hidden, or delete
             Channel number
             Source
             Multiplex
             Frequency
             Callsign
        
    File ->  Import

             Will read a previously generated export file 'channels.export' 
             and adopt the visible, hidden or deleted status for each channel
             in the file.

             Since the channel line-up may have changed since the export file
             was created there are four successive rules to match the 
             channels, each rule using a different set of parameters.  

             The rules are:

               1.  Callsign matches and is unique in the file and unique in 
                   the database.

               2.  Channel number and callsign both match and the combination
                   is unique in the file and also unique in the database. 

               3.  Source, frequency and callsign all match and the combination
                   is unique in the file and also unique in the database.

               4.  There is multiple channels with the same callsign in 
                   the file and the same number in the database.  
                   All are marked as hidden in the file.

            Any un-matched channels are reported in the log and require manual 
            intervention.  These are also marked with a status of
            'Q' (query) as a reminder and can be grouped with View > queries.
            The query flag is cleared when channels are subsequently edited.


    File ->  Update Database

             Will update the database with the requested changes.  

             Please ensure that you have a robust backup strategy in 
             place or are prepared to perform a channel re-scan 
             before choosing this option.

             The database will NOT be updated in demo mode. 

    File ->  exit   will quit without saving the changes.


VIEW

    The View menu allows listing of all channels with columns:

        Key            - order for this particular sort rule.
        ChId           - Channel identifier - unique channel reference in the 
                         backend.  May change on re-scan.
        ChNo.          - broadcast channel number visible to viewer
        Src:Mpx        - video source and multiplex
        State          - This will show H for hidden, 
                         d for visible channel with duplicated channel numbers,
                                channel names or callsigns, 
                         Q for an import query and 
        Final          - final state of channel (D=delete, H=hidden, V=visible).   
                         If blank, assume visible and unchanged.
                         An arrow -> indicates a change of state.
        Channel Name   - name of channel   
          OR
        Callsign       - callsign of channel
 
    The channels can be listed in a number of ways.  The pre-defined sort orders are:   
    ChannelId, Channel no, Source, Source:Multiplex, Channel name, hidden, duplicated,
    or query.  These can all be chosen from the 'View' menu.

    If these sorting rules do not meet your requirements then you can 
    define your own custom sort order.  To do this, select:

         View -> Custom Create
         View -> first sort item
         View -> second sort item
            etc.  
         Finally, select View -> custom sort

    Up to six fields can be specified.  ChannelId is used as a final tie-break.

    Once a custom rule is defined, it can be re-used many times.

    View -> multiplexes
        Will list sources, multiplexes, frequencies, channel counts and multiplex type.

    View -> Log
        Will list the internal log file of  major events.

    View -> Toggle name will switch names.

        There are two names stored in the database for each channel; 'CallSign'
        and 'ChannelName'.  In some broadcasting cultures (eg UK DVB-T) these 
        are identical, but in others they differ.

        The MythTV frontend displays Callsign.
            
EDIT

    Channels can be hidden, unhidden, deleted, or reinstated to their original 
    state.

    They can be selected with a range of Key values (as given in the listings), 
    by source:multiplex or by name.  Any channels with a particular text in 
    the channel name (case insensitive) can be chosen.  

    In combination with the sorting rules, the 'key' value range is 
    particularly flexible.  If the order is changed with a subsequent fresh
    listing order, the required action stays with the chosen channels rather
    than being re-ordered.

    The 'undo' option allows you to undo your last two edits.

    The 'undo all' reverts to the state when the backend was read (or the state 
    following a database update).

    Note that the database is not changed at this stage - only when you use
    File >'Update database'.


HELP
    help      gives this text

    version   gives version numbrer

    diagnostics
 
        writes information to a file channels.diags.
        This is a diagnostic file to help the author should you have 
        problems.  It will contain the log and data from your host for 
        sources, multiplexes,channels, xmltv data and (possibly) wsdl.

COPYRIGHT

    This is issued under the GPL license.  You are free to modify and 
    redistribute it freely under the same conditions as MythTV.   The 
    author accepts no liability for any errors or for any damage this
    code may cause.
  

FILES

    Channel editor uses the following files:

    scan_database.pm       perl modules from MythTV wiki API examples.
                           Must be in perl path on your system.
    channels.export        data to enable channel matching following a re-tune
    channels.diags         diagnostic file - will help the author reporoduce 
                           any problems.
 
END_HELP
$pane2 -> configure(-text => $out, -anchor =>"nw", -justify=>'left');
}

