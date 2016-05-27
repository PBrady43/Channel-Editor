#!/usr/bin/perl -w


#for OSX, first line needs to be:
#!/opt/local/bin/perl5.22 -w


=pod
This is a channel editor for MythTV.  It uses the MythTv API inteface.
For full details and a tutorial see https://www.mythtv.org/wiki/Channel_Editor

Phil Brady, 27 May 2016.
=cut


use strict;
use Tk;
use Tk::Pane;
use Tk::Dialog;
use Tk::DialogBox;
require Tk::LabEntry;

use scan_database;    #See https://www.mythtv.org/wiki/Perl_API_examples
use Getopt::Long;
use warnings FATAL => qw(uninitialized);

my $version=' Version 2.00  27 May 2016';

# 27 May 2016    Version 2.00 released.

my $showdata='';
vec($showdata, 2**18-1, 8)=0;
$showdata = '';


my $backend; my $spoof; my %ChanData; my %MplexInfo;my %sources;my $nodemo=0; my $demo=1;
my $Extra;
my %xmlhash;     #for matching xmltv entries 
my @mergelog=();  #manual matches
my $xmltvmatchcount=0;
my $xmltvmultiplex;


my $mythversion='0'; 
my @sorted;
my @log; my @Undo=(); my @UndoPointer =(0); my @track;
my $exportcheck=0;    #check for export reminder

GetOptions("backend:s"      => \$backend,
           "spoof:s"        => \$spoof,
           "demo!"          => \$demo,
           "extra:s"        => \$Extra,
          );

GetBackendfAddress();
my @CustomSortRules=();
my @CustomDescription=();
my $SortChoice = 'ChanId';
my $LastSortChoice=$SortChoice;


#Extra defaults
$Extra||='';



my $CommFreeTrue='true'; my $CommFreeFalse='false';    #but 1 & 0 prior to 0.28

my $text='Fully functional mode.';
   $text="Running in demo mode." if $demo;

my $main; my $font;
my $headings; my $pane; my $pane2;
my @selection=();   #used in edits.
my $postmortemcount=0;



#column controls
my $ViewChoice='Normal';
my $LastChannelView='Normal';
my $ChNoLeft=0; my $ChNoRight=0;     #space allocated for ATSC major/minor  (or non atsc/nothing)

my %columns = (    #column heading, format for view, flags (R=read backend,W=check width, E=edit, X=export, I=import without asking, i=do not import, C=custom column, B=Bulk edit item )
    ChanNum    =>  ['  ChNum','%7s','RXIECB'],
    SourceId   =>  [' Src:',' %3d:','RXi'],
    MplexId    =>  ['Mpx','%-3d','RXi'],
    Flags      =>  ['  DVECdQUM','  %-8s','C'],
    XMLTVID    =>  ["  XMLTVID", "  %-38s",'RWXIECB'],
    CallSign   =>  ["  CallSign", "  %-28s",'RWXIEC'],
    ChanId     =>  ["  ChId","%6d",'Ci'],
    Sort       =>  [" Sort  ", "%7d",''],
    Visible    =>  ['','','RXIE'],
    UseEIT     =>  ['','','RXIE'],
    CommFree   =>  ['','','RXIE'],
    OldCallSign=>  ['  OldCallSign', '%-28s', ''],   #set to RWXIC if callsign changed
   'Src:Mpx'   =>  ['','','C'],
    NewState   =>  ['','',''],           # ) legacy export file parameters
    Source     =>  ['','',''],           # )
    FrequencyId=>  ['FqId', '', 'RWXiC'],
    ChannelName=>  ['  ChannelName', '', 'RWExIC'],
    Frequency  =>  ['','','i'],
);

my @columnswanted = qw/ChanId ChanNum SourceId MplexId FrequencyId Flags CallSign XMLTVID/;
my @customcolumns = ();
 

#control hash for sorting
#[0]=1 if main menu item, =2 if create custom rule
# [1] sort items
# [2] type of sorting:  0=ChanId, 1=numeric, 2=string, 3=state, 99=invalid


my %sortitems =(
   ChanId           => [3,'id', 0],
  'Channel No'      => [3,'Sort', 1],
  'Sort'            => [0, '', 1],
   SourceId         => [3,'SourceId', 1],
  'Src:Mpx'         => [1,'SourceId:MplexId', 99],
   MplexId          => [0,'',1],
   Multiplex        => [2,'MplexId', 1], 
   CallSign         => [3, 'CallSign',2],
   ChannelName      => [3, 'ChannelName', 2],
   FrequencyId      => [3, 'FrequencyId', 1],
   XMLTVID          => [3, 'XMLTVID', 2],
  'Visible/deleted' => [3,'Visible', 99],
   UseEIT           => [3, '-E', 3],
   Commfree         => [3, '-C',3],
  'Duplicate Callsign' => [1,'-d:CallSign',99],
  'Duplicate ChanNum'  => [1,'-d:Sort',99],
   Duplicate        => [2, '-d',3],
   Query            => [3, '-Q',3],
   UnDoable         => [3, '-U',3],
   Modified         => [3,'-M',3],
   custom           => [0, 'id',99],
   id               => [0,'',0],
   Visible          => [0, 'Visible', 2],
);
$sortitems{$Extra}=[3,$Extra, 1] if $Extra;


eval{
    #create main window
    track('creating main');
    $main=MainWindow->new();
    $main->Label(-text => "MythTV Channel Editor.  Version $version    $text")->pack;

    my $w= int($main->screenwidth *0.75); my $h=int($main->screenheight *0.75);
    $main->geometry("${w}x${h}+0+0");   #start at 75% of screen - higher values risk inhibiting resize

    $font = $main->fontCreate('body',
       -family=>'courier',
       -weight=>'normal',
       -size=> 14);

    my $headerfont = $main->fontCreate('header',
       -family=>'courier',
       -weight=>'bold',
       -size=>14);


    #menu bar and pull down menus
    track('creating menubar'); 
    my $menubar=$main->Frame(-relief =>"raised",
                   -borderwidth   =>2)  
                   ->pack (-anchor => "nw",
                           -fill   => "x");

    track('creating file menu');
    my $FileMenu= $menubar-> Menubutton(-text =>"File", -menuitems  => [
          [ Button => "Import",               -command   => \&Import],
          [ Button => "Export",               -command   => \&Export],
          [ Button => "Update Database!!",    -command   => \&Save],
          [ Button => "Exit",                 -command   => \&exitscript],
          ]) ->pack(-side => "left");

    track('creating view menu');
    my $ViewMenu= $menubar-> Menubutton(-text =>"View")
                          -> pack(-side => "left");
       $ViewMenu -> radiobutton(-label => "Show default columns", -variable=>\$ViewChoice, -value=>'Normal',
                                -command=> \&ChooseDisplay);
       $ViewMenu -> radiobutton(-label => "Show Channelname",    -variable=>\$ViewChoice, -value=>'ChannelName',
                                -command=> \&ChooseDisplay);

       if ($Extra){
          $ViewMenu -> radiobutton(-label => "Show $Extra", -variable=>\$ViewChoice, 
                            -value=>'Extra', -command=> \&ChooseDisplay);
       }
       $ViewMenu -> radiobutton(-label => "Show custom columns", -variable=>\$ViewChoice, -value=>'custom',
                                -command=> \&ChooseDisplay);
       $ViewMenu -> separator();
       $ViewMenu -> radiobutton(-label => "Show multiplexes", -variable=>\$ViewChoice, -value=>'Mpxs',
                                              -command      => \&ListMultiplexes);              
       $ViewMenu -> radiobutton(-label => "Show log", -variable=>\$ViewChoice, -value=>'Log',
                                                      -command      => \&ShowLog);
       $ViewMenu ->  separator();
       $ViewMenu ->  radiobutton(-label=>"Define Custom columns", -variable=>\$ViewChoice, -command=> sub{&CreateColumns});

  

  
    track('creating sort menu');
    my $SortMenu= $menubar-> Menubutton(-text =>"Sort") -> pack(-side => "left");
    for (sort keys %sortitems){
         if (($sortitems{$_}[0] % 2) == 1){
            $SortMenu -> radiobutton(-label => "Sort by $_", -variable=>\$SortChoice, -value=> $_,
                                -command => \&NewSort);
         }
    }
    $SortMenu ->  radiobutton(-label =>"Custom sort", -variable =>\$SortChoice, -value=>'custom', -command =>\&NewSort);
    $SortMenu ->  separator();
    $SortMenu ->  command(-label=>"Reverse sort",       -command   => \&ReverseSort);
    $SortMenu ->  command(-label=>"Define custom sort", -command   => \&CreateCustomSort);


    track('creating edit menu');
    my $EditMenu   = $menubar -> Menubutton(-text =>"Edit", -menuitems  => [
          [ Button => "Single Channel",       -command   => \&EditSingle],
          [ Button => "Bulk by row range",    -command   => \&EditbyRow],
          [ Button => "Bulk by Source:mpx",   -command   => \&EditbyMpx],
          [ Button => "Bulk by CallSign",     -command   => \&EditbyName],
          [ Separator =>''],
          [ Button => "Undo",         -command   => sub{&EditUndo(0)}],
          [ Button => "Undo all",     -command   => sub{&EditUndo(1)}],
          ]) ->pack(-side => "left");

    track('creating xmltv menu');
    my $XMLTVmenu =  $menubar -> Menubutton(-text =>"XMLTV", -menuitems  => [
          [ Button => "Import XMLTV", -command   => \&ImportXMLTV],
          [ Button => "Show matches",   -command   => sub{&ShowXMLTV(1)}],
          [ Button => "Merge",        -command   => \&MatchXMLTV],
          [ Button => "Commit",       -command   => \&CommitXMLTV],
          ]) ->pack(-side => "left");

    track('creating help menu');
    my $HelpMenu  = $menubar -> Menubutton(-text => "Help", -menuitems  => [
          [ Button => "Version",           -command   => \&Version], 
          [ Button => "Open wki",          -command  => \&helpwiki],
          [ Button => "Diagnostics",       -command   => \&Diagnostics],
          ]) ->pack(-side => "left");

    #column headings
    track('creating headings');
    $headings=$main ->Label(-text => '', -font => $headerfont)->pack(-anchor => "nw");

    #create the scrolled pane 
    track('creating scrolled pane');
    $pane = $main->Scrolled("Pane", Name => 'fred',
            -scrollbars => 'e',
            -sticky     => 'we',
            -gridded    => 'y',
            );
       $pane->Frame;
       $pane->pack(-expand => 1,
                    -fill => 'both');

    #create label for content
    track('creating content label');
    $pane2= $pane -> Label(-text => '', -justify => 'left', -font => $font)-> pack(-side=>"left");

    #Off we go!

    preamble();
    NewSort('id');
    $text .="\n\nRestart with --nodemo if you really intend changing the database." if $demo;
    SimpleBox("Note \n$text");
    Import() if (-e 'channels.export') and (CheckOk('Found an export file.  Do you wish to import now?') eq 'ok');
    MainLoop;
};
postmortem($@) if ($@);
exit 0;


sub GetBackendfAddress{

    eval{
        if (!defined $spoof){
            #get backend address
            if ($backend){
                mylog(1,"Will use backend address $backend");
            }else{
                #look for a config file 
                my @dirs = qw (~/.mythtv/  /home/mythtv/.mythtv/ /etc/mythtv/);
                $_= $ENV{'MYTHCONFDIR'};
                if ($_){
                    unless (m!/$!){$_ .= '/'};
                    @dirs=($_);
                    mylog(1,"Found environment variable MYTHCONFDIR set to  $_");
                }
                for my $file (@dirs){
                    (my $fn)=glob($file);
                    $fn .='config.xml';
                    if ((defined $fn) && (-e $fn)){
                        unless (open CONFIG, "$fn") {print "Cannot open $fn $!\n"; exit 0};
                        mylog(1,"Opening $fn");
                        while ($_ = <CONFIG>){
	                        if (m!<Host>(\S+)</Host>!) {
                                $backend=$1; 
                                mylog(1,"Found host address $backend")};
                        }
                        close CONFIG;
                        last;
                    }else{
                        mylog(0, "$fn not found");
                    }
                }
            }
            unless ($backend){
                print "Need a backend address - please specify with --backend.\n"; 
                exit 0;
            }
            unless ($backend =~ /:/){$backend .=':6544'};
        }
    };
    postmortem($@) if ($@);

}
sub preamble{
    eval{
        my $text="unset";
        track();
        if (defined $spoof){$demo=1; $text=$spoof};
        mylog(0, "$0  Version=$version, demo=$demo,");
        mylog(0, "    spoof=$text, os=$^O");

        #ignore $Extra if invalid.
        if (( $Extra) && (exists $columns{$Extra})){
            SimpleBox("--extra $Extra is invalid - being ignored");
            $Extra='';
        }
        mylog(0,"Extra=$Extra");
        $columns{$Extra} = ["  $Extra", '%6s', 'RWCEB'] if $Extra;
 
        #check export file (if any) - note columns in it
        if (0){     #Removed - too complex
            if (-e 'channels.export'){
                unless (open  FH, "<channels.export") {mylog(1,'Cannot open channels.export'); exit 0};
                #read heading
                
                chomp (my $line=<FH>);
                $text='Import parameters found are: ';

                for (split /\[\]:\[\]/, $line){
                    #add to list of interesting columns
                    $text .= "  $_";
                    if ((!exists $columns{$_}) && ($_ ne 'OldCallSign') && ($_ ne 'Frequency') ){
                        $columns{$_}=["  $_", '%9s', 'RWXCEB'];
                    }
                }
                close FH;
                mylog(0, $text);

                #Sanity check:
                for (qw/ChanNum Source MplexId CallSign/){
                   if ($line !~ /$_/){
                        print "channels.export file is malformed:  cannot find $_ in header\n";
                        print "Please rectify or delete it then try again\n";
                        exit 0;
                   }
                }
           }
        }
        &InterrogateBackend;
    };
    postmortem($@) if ($@);
}

#-- Edit menu routines --------


sub EditSelection{


    my ($action, $ButtonChosen, $ValueChosen)=@_;
    eval{
        track($action);
        if (scalar @selection == 0){SimpleBox('No channels selected'); return};
        my ($allowvalue,$param, $set, $reset, $tag, $tagpos)=split /:/, $ButtonChosen;
        
        my $bad=0;
        if (($action eq 'Add') and ($allowvalue eq 'N')){$bad=1};
        if (($action eq 'Reset') and ($allowvalue eq 'Y')){$bad=1};
        if ($bad){SimpleBox('Invalid choice'); mylog(0,'bad choice');return};

        my $SetValue = $reset;
        $SetValue = $set if ($action eq 'Set');
        $SetValue = $ValueChosen if ($allowvalue eq 'Y');
        mylog(0,"  param=$param, val=$SetValue");

        #Checks before 'Add
        if ($action eq 'Add'){
            unless ($SetValue =~  /^\s*-?\d+\s*$/){
                SimpleBox('Integer expected!');
                return;
            }
            for (@selection){
                unless ($ChanData{$_}{$param} =~  /^\s*-?\d+\s*$/){
                    SimpleBox("$param for ChanId $_ is not numeric.  No changes made to any channel.");
                    return;
                }

                if (($ChanData{$_}{$param} + $SetValue)<0){
                    SimpleBox("$param for ChanId $_ would be negative.  No changes made to any channel.");
                    return;
                }
            } 
 
        }
        
        return unless &CheckOk(scalar @selection . ' channels selected') eq 'ok';
   
        ClearUflags();

        #now change channels
        push @UndoPointer, scalar @Undo;  #remember where we started this undo batch

        for (@selection){          
            if ($action eq 'Add'){
                SetNewValue($_, $param, $ChanData{$_}{$param} +$SetValue);
            }else{
                SetNewValue($_, $param, $SetValue);
            }
        }
        mylog(0,'  changes done');
        #now refresh screen
        TidyData();
        refresh();
    };
    postmortem($@) if ($@);
}

sub ClearUflags{
    my $id;
    for ($UndoPointer[-1] .. ((scalar @Undo) -1)){
        ($id)=split /:/, $Undo[$_];
        substr($ChanData{$id}{Flags},6,1)='.';  #resets U
    }
}  

sub SetNewValue{
    #set a value, maintaining undo stack and flags,
    eval{
        my ($id, $param, $value)=@_;

        if ($value ne $ChanData{$id}{$param}){
            if (($param eq 'CallSign') && ($ChanData{$id}{'OldCallSign'}eq '')){
                SetNewValue($id, 'OldCallSign', $ChanData{$id}{CallSign});
                $columns{OldCallSign}[2]='RWXIC';
            }
            push @Undo, "$id:$ChanData{$id}{Flags}:$param:$ChanData{$id}{$param}";  #maintain undo stack
            $ChanData{$id}{$param}=$value;
            substr($ChanData{$id}{Flags},6,2)='UM';  # set U & M
        }
        substr($ChanData{$id}{Flags},5,1)='.';  # reset Q
    };
   postmortem($@) if ($@);
}

sub EditbyRow{
    eval{
        my $first; my $last;

        my ($reply, $RowRange, $ButtonChosen, $ValueChosen)= BulkEditBox('Give row (eg 9) or row range (eg 7:11)');
        return if $reply eq 'Cancel';

        mylog(0,"EditbyRow range= => $RowRange reply=$reply button=$ButtonChosen value=$ValueChosen");

        if ($RowRange =~ /^\s*(\d+)\s*$/){
           ($first,$last)=($1,$1);
        }elsif ($RowRange =~ /^\s*(\d*):(\d*)\s*$/ ){
            ($first, $last)=($1,$2);
        }else{
            SimpleBox("Channel selection not recognised");
            return;
        }
        if (($last<$first) or ($last>=scalar @sorted)){
            SimpleBox("Sorry:  Limits of $first:$last not valid.");
            return;
        }
        #decide which channels
        @selection=();
        for ($first .. $last){
            push @selection, $sorted[$_];
        }

        #now change them
        EditSelection($reply, $ButtonChosen, $ValueChosen);
    };
    postmortem($@) if ($@);
}

sub EditbyMpx{
    eval{
        my ($reply, $selection, $ButtonChosen, $ValueChosen)= BulkEditBox('Give source or source:multiplex');
        return if $reply eq 'Cancel';

        mylog(0,"EditbyMpx range= => $selection reply=$reply button=$ButtonChosen value=$ValueChosen");
       
        my $src; my $mpx;
        if ($selection =~ /^\s*(\d+):(\d+)\s*$/){
            ($src, $mpx)=($1, $2);
        }elsif ($selection =~ /^\s*(\d+)\s*$/){
            ($src, $mpx)=($1, '*');
        }else {
            SimpleBox(" Source:multiplex $selection not recognised");
            return;
        }

        #select victims
        @selection=();
        for (keys %ChanData){
            if ($ChanData{$_}{SourceId} == $src){
                if (($mpx eq '*') || ($mpx == $ChanData{$_}{MplexId})){
                    push @selection, $_;
                }
            }
        }
        #now change them
        EditSelection($reply, $ButtonChosen, $ValueChosen);
    };
    postmortem($@) if ($@);
}

sub EditbyName{

    eval{
        my ($reply, $selection, $ButtonChosen, $ValueChosen)= BulkEditBox('Give text to match in CallSign');
        return if $reply eq 'Cancel';

        mylog(0,"EditbyMpx range= => $selection reply=$reply button=$ButtonChosen value=$ValueChosen");
  
        #Select victims
        @selection=();
        for (keys %ChanData){
            if ($ChanData{$_}{CallSign} =~ /$selection/i){
                push @selection, $_;
            }
        }
        #now change them
        EditSelection($reply, $ButtonChosen, $ValueChosen);
    };
    postmortem($@) if ($@);
}


sub EditSingle{

    eval{
        track(); 
       
        my ($reply, $row)=GetInput('Give Row number');
        return if ($reply ne 'ok');
        mylog(0,"EditSingle row=$row reply=$reply");
        if ($row !~ /\s*\d+\s*/){$row=-1};
        if (($row<0) or ($row>=scalar @sorted)){
            SimpleBox("Invalid row");
            return;
        }
        my $id= $sorted[$row];

        #generate local hash of interesting data for this row:
        my %hash=();
        my @items=columnlist('E');
  
        my $source= $ChanData{$id}{SourceId};
        my $mpx= $ChanData{$id}{MplexId};
        for(@items){
            $hash{$_} = $ChanData{$id}{$_};
        }
        $hash{ChanNum} =~ s/\s//g;

        my $box=$main->DialogBox(
            -title => "Edit single channel",
            -buttons => ['ok','Cancel'],
            -default_button => 'ok');

        $box -> add('Label', -text=> "\nEditing:  ChanID = $id,  Source=$source,  Multiplex=$mpx.\nCallSign=$hash{CallSign}\n")->pack;
        $box -> add('Label', -text=> "Edit boxes as required then ok or cancel\n")->pack;
        for(sort @items){
            my $tidylabel=sprintf "%-15s", $_;
            $box-> add('LabEntry', -textvariable=>\$hash{$_}, -width =>50,
              -labelPack    => [qw/-side left -anchor w/],
              -label        => $tidylabel) -> pack(-anchor => 'e');
        }
        
        my $text="Hint:  Valid values for:\n CommFree are: $CommFreeTrue or $CommFreeFalse,";
        $text .= "\nUseEIT are: true or false,\nVisible are: true, false or delete\n";
        $box -> add('Label', -text=> $text) ->pack;
        $box -> focus;
        my $return = $box -> Show();
        return if ($return ne 'ok');

        #check that we have tidy user input

       for (qw/Visible UseEIT CommFree/){
            if ($hash{$_} =~ /^t/i){$hash{$_}='true'};    #accept just first character
            if ($hash{$_} =~ /^d/i){$hash{$_}='delete'};
            if ($hash{$_} =~ /^f/i){$hash{$_}='false'};
        }

        unless ($hash{Visible} =~ /^true|false|delete$/){
            SimpleBox("Invalid value $hash{Visible} for Visible ignored");
            $hash{Visible}=$ChanData{$id}{Visible};
        }

        unless ($hash{UseEIT} =~ /^true|false$/){
            SimpleBox("Invalid value $hash{UseEIT} for UseEIT ignored");
            $hash{UseEIT}=$ChanData{$id}{UseEIT};
        }
        unless (($hash{CommFree} eq $CommFreeTrue) or ($hash{CommFree} eq $CommFreeFalse)){
            SimpleBox("Invalid value $hash{CommFree} for CommFree ignored");
            $hash{CommFree}=$ChanData{$id}{CommFree};
        }

        #prepare undo
        ClearUflags();  push @UndoPointer, scalar @Undo; 

        #Now change database
        my $count=0;
        $text='';
        for (keys %hash){
            if ($ChanData{$id}{$_} ne $hash{$_}){
                SetNewValue($id, $_, $hash{$_});
                $count++;
                $text .="$_ ";
                mylog(0,"  $_ set to $hash{$_}");
            }
        }
        #final tidy up
        substr($ChanData{$id}{Flags},5,1)='.'; #clear Q 
        TidyData();

        #Show data
        refresh();

        $text=($count)?"$text\nThe change(s) can be undone":'';
        SimpleBox("$count items changed.\n" . $text);
    };
    postmortem($@) if ($@);
}

sub EditUndo{
    eval{
        (my $everything)=@_;
        mylog(0,"EditUndo $everything");

        my $id, my $state; my $param; my $value;
        track();
    
        my $limit=pop @UndoPointer;
        $limit=0 if $everything;
        while (scalar @Undo > $limit){
            ($id, $state, $param, $value)=split /:/, pop @Undo, 4;
            $ChanData{$id}{Flags} = $state;
            $ChanData{$id}{$param} = $value;
        } 
        if (scalar @Undo ==0){
            @UndoPointer=(0);
        }else{
            #Mark 'U' for previous batch
            my $id;
            for ($UndoPointer[-1] .. ((scalar @Undo) -1)){
                 ($id)=split /:/, $Undo[$_];
                 substr($ChanData{$id}{Flags},6,1)='U';  
            }
        }
        TidyData();
        refresh();
        $exportcheck=-1 if $exportcheck>scalar @Undo;    #check for export reminder
    };
    postmortem($@) if ($@);   
}

#------------------Diagnostics, logging and and error handling ----------------

sub mylog{
    #log and (optionally) print message
    my ($print, $message)=@_;
    postmortem('undefined message in mylog') unless defined $message;
    if ($print){print "$message\n"};
    push @log, $message;
}

sub ShowLog{
    eval{
        track();
        mylog(0,"ShowLog");
        &ClearHeading;
        my $text=join "\n", @log;

#author's diagnostic aids
#       $text .= "\nTracking\n";
#       $text .=join "\n", @track;
#       $text .= "\nUndo stack\n";
#       $text .=join "\n", @Undo;

#$#text .="\n";
#for (sort keys %columns){
#    $text .= " $_  $columns{$_}[2]  $columns{$_}[1] $columns{$_}[0]\n";
#}

#$text .="\n";
#for (sort keys %sortitems){
#    $text .= " $_  $sortitems{$_}[0]  $sortitems{$_}[1] $sortitems{$_}[2]\n";
#}
 
#        $text .= "left=$ChNoLeft\n";
#        $text .= "right $ChNoRight\n";
 
        $pane2 -> configure(-text => $text, -anchor =>"nw", -justify=>'left'); 

     };
     postmortem($@) if ($@);  
}

sub TimeStamp{
    my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst)=localtime(time);
    my $nice_timestamp = sprintf ( "%04d%02d%02d%02d%02d%02d",
                                   $year+1900,$mon+1,$mday,$hour,$min,$sec);
    return $nice_timestamp;
}

sub ReadDiagnostics{
     # author's debugging aid / tutorial support
    return '' unless (defined $spoof);
    (my $section)=@_;
    my $out='';  my $interesting=0;
    unless (open FN, "<$spoof"){print "Cannot open $spoof\n";exit 0};
    while (<FN>){
        $interesting=0 if (/^##/);
        if ($interesting){
            chomp;
            $out .= $_;
        }
        $interesting=1 if (/##$section/);
    }
    close FH;
    $out =~ s!\r!!g;                    #kill off any linefeeds
    $out =~ s!<([^>]*)>\n</!<$1></!g;   #kill off newlines in blank fields
    return $out;
}

sub postmortem{
    #unexpected error

    my ($myerror, @params)=@_;
    track();

    chomp $myerror;
    #postmortem exceptions:
    exit 0 if ($myerror =~ /^_TK_EXIT_/);   #deliberate exit

    mylog(1,"Failure:  $myerror");
    if ($postmortemcount>0){
        print "Sorry - there has been a second error - fatal\n";
        print "$@\n";
        exit 0;
    }
    $postmortemcount++;


    mylog(0,"Call stack:");
    my $i=0;    
    while (my @stack=caller($i)){
        mylog(0,sprintf "line %4d called $stack[3]", $stack[2]);
        if (($i==1) and (scalar @params >0)){
             mylog(0,"Calling params:");
             for (@params){
                mylog(0, "  $_");
            }
        }
        $i++;
    }

    #add tracking to log
    mylog(0,"\nTracking");
    mylog(0, join "\n", @track);

    $myerror= "There has been a fatal error\n$myerror\n";
    $myerror .= "We cannot continue.\nDo you want diagnostics?";

    my $reply=&CheckOk($myerror);
    &Diagnostics if ($reply eq 'ok');
    exit 0;
}

sub Diagnostics{

   
    #show log
    my $filename= 'chedit'. TimeStamp() .'.diags'; 
    #$filename='channel.diags';

    my $temp;

    unless (open DI, ">$filename") {SimpleBox("Cannot open $filename $!"); return};
    print DI "##log\n";
    print DI join("\n", @log), "\n";

    #enough if spoof input
    if (!defined $spoof){
    
        #now sources, multiplexes and channels

        OutputDiags ('sources', 'VideoSourceList');

        #check again in case never read before
        ReadBackend($backend. '/Channel/VideoSourceList', $temp) unless (defined $spoof);
        my $reply=FillHashofHash(%sources, $temp, 'VideoSource', 'Id', 'SourceName');

        for (sort keys %sources){
            OutputDiags ("multiplex$_", "GetVideoMultiplexList?SourceID=$_");
            OutputDiags ("channels$_", "GetChannelInfoList?SourceID=$_&OnlyVisible=false&Details=true");
            OutputDiags ("XMLTV$_", "GetXMLTVIdList?SourceID=$_");
        }
        if ($mythversion gt '0.28.2015'){OutputDiags('##wsdl', 'wsdl')};
    }
    print DI "##end\n";
    close DI;
    mylog(1,"Diagnostics written to $filename");
    SimpleBox("Diagnostics written to $filename");
    
}
  
sub OutputDiags{
    my ($tag, $urltail)=@_;
    my $temp;
    print DI "\n##$tag\n";
    ReadBackend($backend. '/Channel/' . $urltail, $temp);
    $temp =~ s!><!>\n<!;             #initial line
    $temp =~ s!><!>\n<!;             #and again!
    $temp =~ s!</(\w*)>!</$1>\n!g;   #add newlines after </tag>
    $temp =~ s!/>!/>\n!g;            #ditto <tag/>
    print DI "$temp\n";           
}

sub track{

    #put entry in track log



    (my $param)=@_;
    $param ||='';
    $param =~ s/\n/ /;
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

sub columnlist{
    (my $tag)=@_;
    track("$tag");
    my @list;
    for (keys %columns){
        track("seeking $tag in $_");
        push @list, $_ if (index($columns{$_}[2], $tag)>-1);
    }
    return sort @list
}

sub SimpleBox{
    (my $message)=@_;
    my ($line1)=split "\n", $message;
    track($line1);
    my $box=$main->Dialog(
        -title => "Channel Editor",
        -text => $message,
        -buttons => ['ok'],
        -default_button => "ok")->Show();
}

sub GetInput{
    my ($question, $input)=@_;
    track($question);
    my $box=$main->DialogBox(
        -title => "Channel Editor",
        -buttons => ['ok', 'Cancel'],
        -default_button => "ok");
    $box-> add('LabEntry',-textvariable=>\$input, -width =>50,
                -label=> "$question   ",
                -labelPack => [-side => 'left'])->pack -> focus;
    my $reply= $box -> Show();
    return($reply, $input);
}

sub XMLTVBox{
    track(); 
    my %XMLTVtypes=(
       'UK Atlas'           =>    ['~/.xmltv/tv_grab_uk_atlas.map.channels.conf', 'atlas'],
       'UK Radio Times'     =>    ['/usr/share/xmltv/tv_grab_uk_rt/channel_ids', 'rt'],
       'XML file'           =>    ['', 'xml'],
    );

    my $xmlchoice='';
    while ($xmlchoice eq ''){
        my $box=$main->DialogBox(
            -title => "Edit channels",
            -buttons => ['ok'],
            -default_button => 'ok');
        

        $box -> add('Label', -text=> "XMLTVID file:  Please choose format:")->pack;
        for (sort keys %XMLTVtypes){
            $box -> add('Radiobutton', -text => $_,  -variable  =>\$xmlchoice, -value=>$_) 
                -> pack(-anchor => 'w');
        }
        $box -> Show();

    }
    return ($XMLTVtypes{$xmlchoice}[0], $XMLTVtypes{$xmlchoice}[1]); 
}


sub BulkEditBox{
    (my $question)=@_;
    track(); 
    my $ButtonChosen=''; my $ValueChosen=''; my $range='';my $reply='';

    while ($ButtonChosen eq ''){
        my $box=$main->DialogBox(
            -title => "Bulk edit channels",
            -buttons => ['Set', 'Clear', 'Add','Cancel'],
            -default_button => 'Cancel');
        
        $box-> add('LabEntry', -textvariable=>\$range, -width =>30,
                  -label=> $question) -> pack -> focus;
 
        $box -> add('Label', -text=> "\nPlease choose item below then click set or clear:")->pack;

        $box -> add('Radiobutton', -text => "Delete",   -variable  =>\$ButtonChosen, -value=>'N:Visible:delete:true:D:0') 
                -> pack(-anchor => 'w');
        $box -> add('Radiobutton', -text => "Visible",  -variable  =>\$ButtonChosen, -value=>'N:Visible:true:false:V:2') 
                -> pack(-anchor => 'w');
        $box -> add('Radiobutton', -text => "UseEIT",   -variable  =>\$ButtonChosen, -value=>'N:UseEIT:true:false:E:2') 
                -> pack(-anchor => 'w');
        $box -> add('Radiobutton', -text => "CommFree", -variable  =>\$ButtonChosen, 
                -value=>"N:CommFree:$CommFreeTrue:$CommFreeFalse:C:3") -> pack(-anchor => 'w');

        $box -> add('Label', -text=> "\n--- OR --- \n\nchoose item below, give new text and click 'set' ---\n\n --- OR ---\n\nGive numeric value (eg 65 or -65) then 'Add' ---\n\n  Use with care!!")->pack;

        for (columnlist('B')){
            $box -> add('Radiobutton', -text => $_,  -variable  =>\$ButtonChosen, -value=>"Y:${_}::::-1")  -> pack(-anchor => 'w');
        }

        $box-> add('LabEntry', -textvariable=>\$ValueChosen, -width =>30,
                  -label=> "Give new text to set\n or integer to add:\n (use negative to subtract)") -> pack;

        $reply= $box -> Show();
        return ('Cancel','','','') if $reply eq 'Cancel';
    }
    return ($reply, $range, $ButtonChosen, $ValueChosen);

}

sub CheckOk{
    (my $question)=@_;
    my $box=$main->DialogBox(
        -title => 'Channel Editor',
        -buttons => ['ok','cancel'],
        -default_button => "ok");
    $box-> add("Label",
                -text => "$question   ")->pack;
    $box -> Show();
}


#---- TidyData Routine(s) -----

sub TidyData{

    #note longest CallSign, XMLTVID and extra - allocate column widths.
    
    eval{
        track();
        my $temp;  my %dupcallsign; my %dupnumber; my %dupchanname; my $new;
        my @fields=columnlist('W');

        for my $field (@fields){
            my $heading=$columns{$field}[0];
            $heading =~ s/\s//g;
            my $align=1;  #1=numeric, -1=text
            my $max=2+length($heading);

            for (keys %ChanData){
                $temp=$ChanData{$_}{$field};
                $max=length($temp) if $max<length($temp);
                $align=-1 unless $temp =~ m!^\s*\d+\s*$!;
            }
 
            if ($align >0){
                #right justify numeric
                $columns{$field}[0]= ' ' x ($max-length $heading) . "$heading";
                $columns{$field}[1] = '%'. $max . 's';

            }else{
                #left justify string
                $columns{$field}[0]="  $heading" . ' ' x ($max-length $heading);
                $columns{$field}[1] = '  %-'. $max . 's';
            }
            #numeric or char sort?
            $align=2 if $align<0;
            $sortitems{$field}[2]=$align if exists $sortitems{$field};
        }


        $ChNoLeft=0; $ChNoRight=0;
        for (keys %ChanData){
            #Set flags
            substr($ChanData{$_}{Flags},0,1) = ($ChanData{$_}{Visible}  eq 'delete')?'D':'.';
            substr($ChanData{$_}{Flags},1,1) = ($ChanData{$_}{Visible}  eq 'true')?'V':'.';
            substr($ChanData{$_}{Flags},2,1) = ($ChanData{$_}{UseEIT}   eq 'true')?'E':'.';
            substr($ChanData{$_}{Flags},3,1) = ($ChanData{$_}{CommFree} eq $CommFreeTrue)?'C':'.';

            #channel number sort key
            SortOutChannelNos($_,0);

            #count callsigns and channel nos for duplicate detection 
            if ($ChanData{$_}{Visible} eq 'true'){ 
                #count callsigns
                $dupcallsign{$ChanData{$_}{CallSign}}++;
                #count channel nos.
                $dupnumber{$ChanData{$_}{ChanNum}}++;
            }
   

        }
        #sort out channel no field
        $temp=length($columns{ChanNum}[0]);
        my $temp2=$ChNoLeft+$ChNoRight +2;
        $temp=$temp2 if $temp<$temp2;
        $columns{ChanNum}[1]='%-' . $temp .'s';
        $columns{ChanNum}[0]='  ChNum' . ' ' x ($temp-7);

        #mark duplicates
        for (keys %ChanData){
           $new='.';
           if ($ChanData{$_}{Visible} eq 'true'){ 
               if ($dupcallsign{$ChanData{$_}{CallSign}} >1)    {$new='d'};
               if ($dupnumber{$ChanData{$_}{ChanNum}} >1)       {$new='d'};
           } 
           substr($ChanData{$_}{Flags},4,1)=$new;
         }
    };
    postmortem($@) if ($@);

}

sub SortOutChannelNos{
    
    my ($id, $phase)=@_;
    my $sort;my $left, my $right='';

    #phase 0 - set sort value and note widths
    #phase 1 - return aligned chan  no for printing

    my $chan=$ChanData{$id}{ChanNum};

    #simple numeric
    if ($chan=~ /^\s*(\d+)\s*$/){
        $left=$1;
        $sort=10000*$1;
        
    #or  _4_23
    }elsif ($chan =~ /^\s*(\D)(\d+)(\D)(\d+)\s*$/){    
        $sort = $2*10000 + $4*4 + 3;
        $left=$1 . $2;
        $right=$3 . $4;

    #or 4_1
    }elsif ($chan =~ /^\s*(\d+)(\D)(\d+)\s*$/){
        $sort =$1*10000 + 4*$3 +2;
        $left=$1;
        $right=$2 . $3;

    #or _23
    }elsif ($chan=~ /^\s*(\D)(\d+)\s*$/){
        $sort =$2*10000 +1;
        $left=$1 . $2;
    }else{
        $sort =0;
        $left=$chan;
    }

    if ($phase){
        
        return ' ' x ($ChNoLeft - length($left)+2) .$left .$right;
    };

    $ChanData{$id}{Sort}=$sort;

    $ChNoLeft=length($left) if $ChNoLeft<length($left);
    $ChNoRight=length($right) if $ChNoRight<length($right);
}


sub state{
    #eg call if (state($_,'d')) returns non zero if state found,
    return 1+index($ChanData{$_[0]}{Flags}, $_[1]);
}

#----File menu items--------

sub Import{
    eval{
        track('importing');
        mylog(0,"Importing channels.export");

        #
        # scan import file
        #

        my $rule; my $index; my %Chans; my $temp;
        unless (open  FH, "<channels.export") {SimpleBox("Cannot open channels.export"); return};

        #read heading
        chomp ($_=<FH>);
        s/\]Source\[/\]SourceId\[/;      #align legacy header
        my @headings = split /\[\]:\[\]/, $_;
        my $freqtype=(/FrequencyId/)?'FrequencyId':'Frequency';

        #read values from import file
        my %item; my $k, my $v; my $linecount=0;my @values;my $ChanId;
        while ($_= <FH>){
            chomp;

            #get values from line
            @values=split /\[\]:\[\]/, $_;
            push @values, '' if @headings>@values;   #null entry at end

            $item{OldCallSign}=''; #default
            for $k (@headings){
                $item{$k}=shift @values;
            }
            $item{OldCallSign}='' if ($item{OldCallSign} eq $item{CallSign});

            #tidy up version 1 data
            if (defined $item{NewState}){
                $v=index('VHD',$item{NewState});
                if ($v<0){SimpleBox('Invalid file - newstate field suspect'); return};
                $item{Visible}= qw/true false delete/[$v];
            }
            
            #now generate match entries for callsign and oldcallsign
            my $name;
            for $name (qw/CallSign OldCallSign/){
                next if $item{$name} eq '';
                for $rule (1..3){  
                    $index=fingerprint($rule, $item{ChanNum}, $item{SourceId}, $item{$freqtype}, $item{$name});
                    $Chans{$index}{count}++;
                    $Chans{$index}{FileLine}=$linecount;
                }
            }
            $linecount++;
        }
        close FH;

        #
        #now scan database and generate match hash entries
        #
        track();
        for (sort keys %ChanData){
           my $freq=$ChanData{$_}{FrequencyId};  #version 2
           if ($freqtype eq 'Frequency'){        #version 1
                 $freq=$MplexInfo{$ChanData{$_}{SourceId} .':'. $ChanData{$_}{MplexId}}{Frequency};
           }
           for $rule (1..3){
                $index=fingerprint($rule, $ChanData{$_}{ChanNum}, $ChanData{$_}{SourceId}, $freq, $ChanData{$_}{CallSign});
                $Chans{$index}{count} +=1000;
                $Chans{$index}{ChanId}=$_;
           }
        }

        #now try to match them  - enter matches in $line2chanid{file line no}=> channelid
        
        my @rulestats = (0,0,0,0,0);
        my %line2chanid=();

        for (sort keys %Chans){
            my $ok=0;
            $temp=$Chans{$_}{count};
            next if ($temp % 1001) !=0; 
            $ok=1 if $temp == 1001;
            next if $ok==0;
 
            $temp=$Chans{$_}{FileLine};
            next if exists ($line2chanid{$temp});  #got this one already
            $line2chanid{$temp}=$Chans{$_}{ChanId};
            /^(\d)/;
            $rulestats[$1]++;
        }

        #
        #now we have identified the matches, we can re-scan the file and change values in database.
        #

        unless (open  FH, "<channels.export") {SimpleBox("Cannot open channel.export"); return};

        #Initialise undo first
        ClearUflags();
        push @UndoPointer, scalar @Undo;  #remember where we started this undo batch
        $linecount=-1;

        #make a list of fields which can be changed
        my @changeitems=();

        for (reverse sort @headings){          #reverse places OldCallSign before CallSign
             if ($columns{$_}[2] =~ 'XI'){ 
                 push @changeitems, $_;
             }elsif ($columns{$_}[2] =~ 'Xi'){
                #omit
             }elsif ($columns{$_}[2] =~ 'X'){
                 if (CheckOk("\nExport file includes $_  \n\n  Do you wish to modify this field?  \n\n  Use this with caution!! \n\n  Choose cancel to leave it unchanged.") eq 'ok'){  
                    push @changeitems, $_;
                 }
             }
        }
  
        #
        #now change values
        #

        <FH>;  #skip headings
        while ($_=<FH>){
            chomp;
            $linecount++;

            if (exists $line2chanid{$linecount}){
                @values=split /\[\]:\[\]/, $_;
                push @values, '' if @headings>@values;  #fix if last one blank
                for $k (@headings){
                    $item{$k}=shift @values;
                }
                #tidy up the data  (again - sigh!)
                if (defined $item{NewState}){
                    $v=index('VHD',$item{NewState});
                    if ($v<0){SimpleBox('Invalid file - newstate field suspect'); return};
                    $item{Visible}= qw/true false delete/[$v]
                }

                #regularise 0.27/0.28 Commfree values 
                if (defined $item{CommFree}){
                    if (($item{CommFree} eq '0') or ($item{CommFree} eq 'false')){
                        $item{CommFree} = $CommFreeFalse;
                    }else{
                        $item{CommFree} = $CommFreeTrue;
                    }
                }   
                
                $ChanId=$line2chanid{$linecount};
                for $k (@changeitems){
                     if (exists $item{$k}){
                         track("k=$k");
                         SetNewValue($ChanId, $k, $item{$k});
                    }

                 }
            }
        }

        #now sort out Q flag - mark all initially as queried

        my $queries=0; my $match=0;
        for (keys %ChanData){
             substr($ChanData{$_}{Flags},5,1)='Q'; 
             $queries++;
        }
        #now clear Q for those matched
        for (keys %line2chanid){
            $ChanId=$line2chanid{$_};
            substr($ChanData{$ChanId}{Flags},5,1)='.';
            $queries--;
        }  
 
        #log the rule stats
        mylog(0,'    Rule stats');
        for (1 .. 3){
            mylog(0,"       Rule $_  $rulestats[$_]");
            $match+=$rulestats[$_];
        }
        mylog(0, "    Matches  $match  Queries $queries");

        TidyData();

        my $out='Import complete';
        $out .= "\n\n$match channels matched, $queries not.";
        if  ($queries){
            $out .= "\n\nSee channels marked 'Q'";
            $SortChoice='Query';
            refresh();
        }else{
            #leave page as it was!
            refresh();
        }   
        $exportcheck = scalar @Undo;     #export checking  
        SimpleBox($out);
    };
    postmortem($@) if ($@);
}

sub fingerprint{

    my ($rule, $chno, $src, $freq, $name)=@_;
   
    if ($rule ==1){
        return "1:$name";
    }elsif ($rule==2){
        $chno =~ s/\s//g;
        return "2:$chno:$name";
    }elsif ($rule==3){
        return "3:$src:$freq:$name";
    }elsif ($rule ==4){
        return "4:$name";
    }else{
        postmortem ("Import rule $rule missing");
    }
}



sub Export{
    eval{
        #export state of play
        track();
        mylog(0,"\nExporting to channel.export"); 
        unless (open  FH, ">channels.export"){
            SimpleBox("Cannot open channels.export"); return};
        my @fields= columnlist('X');

        print FH join '[]:[]', @fields;
        print FH "\n";
        my $count=0; my $csign; my $field;my $fq;
        for (sort keys %ChanData){
            my @out; my $val;

            #clear oldcallsign if user has reinstated callsign 
            $ChanData{$_}{OldCallSign}='' if ($ChanData{$_}{OldCallSign} eq $ChanData{$_}{CallSign});

            for $field (@fields){
                $val=$ChanData{$_}{$field};
                $val =~s/\s/ /g;    #kill newlines, linefeeds etc 
                push @out, $val;
            }   
            print FH  join '[]:[]', @out;
            print FH "\n";
            $count++;
        }
        close FH;
        $exportcheck = scalar @Undo; 
        track("$count channels exported");
        mylog(0, "    $count channels exported");
        SimpleBox("$count channels exported to 'channels.export'");
    };
    postmortem($@) if ($@);
}


sub Save{
    eval{
        #update database and exit
        track();
        mylog(0,'Saving');

        #Count candidates
        my %counts;
        $counts{M}=0; $counts{D}=0;
        for (keys %ChanData){
            if (state($_,'D')){$counts{D}++;
            }elsif (state($_,'M')){$counts{M}++;
            }
        }
        if ($counts{M} + $counts{D} ==0){
            SimpleBox('There are no changes to save to the database.');
            return;
        }  
        
        Export() if ((scalar @Undo != $exportcheck) && (CheckOk("Your export file is not up to date\nUpdate it now?") eq 'ok'));

        my $text= "\nYou have chosen to delete $counts{D} channels,";
        $text .= "\n and modify $counts{M} channels.\n";
        $text .= "\nDo you have a good backup?\nAre you sure you wish to update the database?";
        if ($demo==0){
            $text .="\n\nWARNING!!!\n You are NOT in demo mode!\n";
        }else{
            $text .="\n\n .. but you are in demo mode only\nNothing will change on backend.";
        }
        my $reply=CheckOk($text);
        return if ($reply ne 'ok');
        
        mylog(0,"    Updating database:  demo=$demo");
        mylog(0,"    Will delete $counts{D}, modify $counts{'M'}");

        for (sort keys %ChanData){
            if (state($_,'D')){
                DeleteChannel($_);
            }elsif (state($_,'M')){
                ModifyChannel($_);
            }
        } 
        
        #reset the undo stack, clear QUM, mark duplicates etc
        @UndoPointer=(0);
        @Undo=();
        $exportcheck=0;
        for (sort keys %ChanData){
            substr($ChanData{$_}{Flags},5,3)='...'; 
        } 
        TidyData();
        ShowLog();
    };
    postmortem($@) if ($@);
}

sub ModifyChannel{
    (my $id)=@_;
    eval{
        my %hash;  my $content; my $k; my $response;
        if (defined $spoof){
            mylog(0,"    Demo: modifying $id:$ChanData{$id}{CallSign}");
            return;
        }
        #read backend
        ReadBackend($backend . '/Channel/GetChannelInfo?ChanID=' . $id, $content);
        GetAllFields(%hash, $content, '<ChannelInfo', '</ChannelInfo>');

        #change fields
        my $logtext="    $id $ChanData{$id}{CallSign} changing: ";
        $hash{'#Icon'}='' unless (defined $hash{Icon});    #default it unless now available
        my $v;
        for $k (sort keys %hash){
            if (defined $ChanData{$id}{$k}){
                $v=$ChanData{$id}{$k}; 
                $v=~ s/^\s+//;    #strip leading and trailing spaces (Chan num needs this)
                $v =~ s/\s+$//;
                if ($hash{$k} ne $v){
                    $hash{$k} = $v;
                    $logtext .= "  $k";
                }
            }
        }
        if ($demo){$logtext = 'Demo: '.$logtext};
        mylog(0,$logtext);
        if ($demo==0){
            ValidatePost(%hash, $backend . '/Channel/UpdateDBChannel', 'raw',12);
        }
    };
    postmortem($@, "id=$id") if ($@);
}

sub DeleteChannel{
   (my $id)=@_;
    eval{
        if ($demo){
            mylog(0,"    Demo: deleting $id:$ChanData{$id}{CallSign}");
            delete($ChanData{$id});
            return;
        }
        mylog(0,"    Deleting $id:$ChanData{$id}{CallSign}");

        #issue post 
        my %hash;
        track($id);
        $hash{ChannelID}=$id;
        ValidatePost(%hash, "$backend/Channel/RemoveDBChannel", 'raw', 1);
        delete($ChanData{$id});
    };
    postmortem($@) if ($@);
}

sub exitscript{
    exit if scalar @Undo ==0;
    exit if CheckOk('Changes have been made.  Really exit?') eq 'ok';
}


#----- Sorting and Listing code ---------

sub ReverseSort{
    eval{
        mylog(0,"reverseSort");
        return if $SortChoice eq 'Log';
        return if $SortChoice eq 'Mpxs';
        @sorted=reverse @sorted;
        refresh();
    };
    postmortem($@) if ($@);
}

sub ListMultiplexes{
    eval{
        track();
        mylog(0,"ListMultiplexes");
        &ClearHeading;
        #list sources
        my $out=" Source   Name\n";
        for (sort keys %sources){
            $out .= "    $_     $sources{$_}{SourceName}\n";
        }
        my $total=0;
        #list multiplexes
        $out .= "\n Source  Mplex   Freq (MHz)    Channels  Standard\n";
        for (sort {$MplexInfo{$a}{sort}  <=> $MplexInfo{$b}{sort}} keys %MplexInfo){
            my ($src, $mpx) =split ":", $_;
            $out .= sprintf "  %3d    %3d     ",$src,$mpx;
            $out .= sprintf " %7.3f  ", $MplexInfo{$_}{Frequency}/1000000;
            $out .= sprintf "  %7d     ", $MplexInfo{$_}{Count};
            $out .= "$MplexInfo{$_}{Standard}\n";
            $total += $MplexInfo{$_}{Count};
        }
        $out .= "\n Total channels:    $total\n";
        $pane2 -> configure(-text => $out, -anchor =>"nw", -justify=>'left');
    };
    postmortem($@) if ($@);
}



sub NewSort{

    eval{
        mylog(0,"NewSort $SortChoice");
        $ViewChoice=$LastChannelView;       #force back to most recent channel view from mpx/log 



        my @fields= split ':',$sortitems{$SortChoice}[1];

        $LastSortChoice=$SortChoice;
        while (scalar @fields <6){push @fields, 'id'};
        track(join ":", @fields);
        mylog(0, "sorting:" . join ":", @fields);
        @sorted=sort {sortx($fields[0],$a,$b)  ||
                     sortx($fields[1],$a,$b)  ||
                     sortx($fields[2],$a,$b)  ||
                     sortx($fields[3],$a,$b)  ||
                     sortx($fields[4],$a,$b)  ||
                     sortx($fields[5],$a,$b)  ||
                     ($a <=> $b)}  keys %ChanData;

        TidyData();
        refresh(); 
    };
    postmortem($@) if ($@);      
}

sub sortx{
    ($_, my $A, my $B)=@_;
    return $A<=>$B if (/id/);

    if (/^-/){
        ($A,$B)=($B,$A);
        s/-//;
    }

    if (/^[d|Q|U|M|E|C]$/){
        return state($A, $_) <=> state($B, $_);
    }
    my $type=$sortitems{$_}[2];

    if ($type ==2){
        return ($ChanData{$A}{$_} cmp $ChanData{$B}{$_});
    }elsif ($type ==1){
        return ($ChanData{$A}{$_} <=> $ChanData{$B}{$_});
    }else{
         postmortem("Error in sortx $_ type $type");
    }
}

sub ChooseDisplay{
    mylog(0,"ChooseDisplay $ViewChoice"); track();
    $LastChannelView=$ViewChoice;
    if ($ViewChoice eq 'Normal'){
        @columnswanted=qw/ChanId ChanNum SourceId MplexId FrequencyId Flags CallSign XMLTVID/;
    }elsif ($ViewChoice eq 'ChannelName'){
        @columnswanted=qw/ChanId ChanNum SourceId MplexId FrequencyId Flags CallSign ChannelName/;
    }elsif ($ViewChoice eq 'Extra'){
        @columnswanted=qw/ChanId ChanNum SourceId MplexId Flags CallSign/;
        push @columnswanted, $Extra;
    }elsif ($ViewChoice eq 'custom'){
        @columnswanted = @customcolumns;
    }else {
        postmortem("Choice $ViewChoice not recognised in ChooseDisplay");
        exit 0;
    }
    refresh();
}

sub ClearHeading{
    $headings -> configure(-text => '', -anchor =>"nw", -justify=>'left');
}

sub CreateColumns{

    eval{
        #allow user defined columns in display
        mylog(0,"Create columns"); track();
        @customcolumns=();
        my %items;
        for (columnlist('C')){
            $items{$_}=1;
        }
        $items{$Extra}=1 if $Extra;

        $ViewChoice ='custom';
        ChooseDisplay();
        my $choice='';
        while ($choice ne 'x'){
            $choice='x';
            @columnswanted = @customcolumns;
            refresh();    #show progress to date
            return if scalar keys %items == 0;
            my $box=$main->DialogBox(
                -title => "Choose columns",
                -buttons => ['ok'],
                -default_button => 'ok');
            $box -> add('Label', -text=> "Please choose next column then ok:\n(or just ok to finish)")->pack;
            for (sort keys %items){
                $box -> add('Radiobutton', -text => $_,  -variable  =>\$choice, -value=>$_) 
                    -> pack(-anchor => 'w');
            }
            $box -> Show();
            if ($choice eq 'Src:Mpx'){
                push @customcolumns, 'SourceId', 'MplexId';
                delete $items{'Src:Mpx'};
            }elsif ($choice ne 'x'){
                push @customcolumns, $choice;
                delete $items{$choice};
            }
        }
        $ViewChoice='custom';
    };
    postmortem($@) if ($@);

}


sub refresh{

   eval{
       track();
       $showdata='';
       my $format='%4d';  
       my @values; my $heading =' Row';
       #do heading
       for my $k (@columnswanted){
            track("k=$k");
            $heading .= $columns{$k}[0];
            $format .= $columns{$k}[1];
       }

       $headings -> configure(-text => $heading, -anchor =>"nw", -justify=>'left');

        #now try to print real data

       my $row=0; my $out='';
       for my $id (@sorted){
            @values=($row++);
            for (@columnswanted){
                track("id=$id  column=$_");
                if ($_ eq 'ChanId'){
                    push @values, $id;
                }elsif ($_ eq 'ChanNum'){
                    push @values, SortOutChannelNos($id, 1);

                }else{
                    push @values, $ChanData{$id}{$_};
                }
                $values[-1] =~ s/\s/ /g;  #eliminate tabs etc in data (eg ChannelName)
            }
            $showdata .= sprintf "$format\n", @values;
       }
       $pane2 -> configure(-text => $showdata, -anchor =>"nw", -justify=>'left');
    };
    postmortem($@) if ($@);
}  

sub CreateCustomSort{
    #Create custom sort rule
    eval{
        mylog(0,'Create custom sort'); track();
        my %items; 
        for (sort keys %sortitems){
            $items{$_}=1 if ($sortitems{$_}[0] >1);
         }

        $sortitems{custom}[1]='';
        my $choice='x'; my $chosen=''; my $ascending='';
        while ($choice ne ''){
            $choice='';
            
            return if scalar keys %items == 0;
            my $box=$main->DialogBox(
                -title => "Choose sort items",
                -buttons => ['ok'],
                -default_button => 'ok');
            my $label='';
            
            if ($chosen){
                $label= "Already chosen:$chosen\n";
                $label =~ s/:/\n/g;
            } 
            $box -> add('Label', -text=> "$label\nPlease choose next sort key then ok:\n(or just ok to finish)")->pack;
            for (sort keys %items){
                $box -> add('Radiobutton', -text => $_,  -variable  =>\$choice, -value=>$_) 
                    -> pack(-anchor => 'w');
            }
            $box -> add('Label', -text=> '')->pack;
            $box -> add('Radiobutton', -text => 'ascending',  -variable =>\$ascending, -value => '')   -> pack(-anchor => 'w');
            $box -> add('Radiobutton', -text => 'descending', -variable =>\$ascending, -value => '-')  -> pack(-anchor => 'w');
            $box -> Show();
            if ($choice ne ''){
                delete $items{$choice};
                $chosen .= ':' . $choice;
                my $newitem=$sortitems{$choice}[1];
                $newitem =~ s/\-//;
                $sortitems{custom}[1] .= ":$ascending$newitem";
            }
            if (scalar split (':',$chosen) >5) {$choice=''};  
        }
        $sortitems{custom}[1] =~ s/^://;   #remove initial :
        $SortChoice='custom';
        mylog(0, "Custom rule= $sortitems{custom}[1]");
        NewSort();
    };
    postmortem($@) if ($@);  
}

# XMLTV menu items

sub ImportXMLTV{

    eval{
        track();
        @mergelog=();
        $xmltvmatchcount=0;
        my $k=0; my $name; my $xmlid; my $reply;
        %xmlhash=();
        #
        # user input
        #
        while ($k==0){
           ($reply, $xmltvmultiplex)= GetInput("Which channel source do you wish to match?\nGive source number or * for all",'');
           return unless $reply eq 'ok';
           $k=1 if $xmltvmultiplex eq '*';
           $k=1 if $xmltvmultiplex =~ /^\d+$/;
        }
        mylog(0,"ImportXMLTV source=$xmltvmultiplex");

        #scan database
        for (keys %ChanData){
            next if state($_,'D');   #skip deleted channels
            next unless(($xmltvmultiplex eq '*') or ($xmltvmultiplex == $ChanData{$_}{SourceId}));  #sieve by source
            $name=$ChanData{$_}{CallSign};
            $k=$name;
            $k =~s/\s//g;
            $k =lc($k);
            $k =~ s/://g;
            $xmlhash{$k}{CallSign}=$name;
            $xmlhash{$k}{XMLTVID}='';
            $xmlhash{$k}{XMLTVname}='';
        }

        $k=scalar keys %xmlhash;
        SimpleBox("$k unique callsigns.");
        
        return if $k==0;

        #what format of file?
        my ($filename, $FileType) = XMLTVBox();

        #open xmltv listing file
        ($reply, $filename)=GetInput("Give XMLTV listing filename", $filename);
        return unless  $reply eq 'ok';

        unless (open  XM, '<', (glob ($filename))[0]) {SimpleBox("Cannot open xmltv listing file"); return};
        mylog(0,"    ImportXMLTV listing file $filename  type $FileType");

        #now read xmltv file
        my $k2; my $matches=0;
        
        if ($FileType eq 'xml'){

            while (<XM>){
                $_= &KillEscapes($_);
                if (m!<channel id=([^>]*)!){
                    $xmlid=$1;     #xmltvid
                    $xmlid =~ s/"//g;
                }elsif(m!<display-name>([^<]*)!){
                    $k=$1;         #callsign in xmltv file
                    $name=$k;
                    #generate key
                    $k =~s/\s//g; $k =lc($k);$k =~ s/://g;
                    $xmlhash{$k}{XMLTVID}=$xmlid;
                    $xmlhash{$k}{XMLTVname}=$name;
                    $xmlhash{$k}{CallSign}||='';
                }

            }
        }elsif ($FileType eq 'atlas'){
            while  (<XM>){
                chomp;
                #   Sample:   
                #   map==999==f1.sports.sky.com                             # (2700) -- Sky Sports F1 
                if (/^map==[^=]*==([^#]*)#(.*)/){
                    $xmlid=$1;
                    $name=$2;
                    $xmlid =~ s/\s*$//;
                    $name =~ m!\)\s+--\s*(.*)!;
                    $name = $1;
                    $name =~ s/\s*$//;
                    $k =$name;
                    $k =~ s/\s//g;  $k=lc($k);   #key

                    #print "k=$k  xmlid=$xmlid  name=$name\n";
                    $xmlhash{$k}{XMLTVID}=$xmlid;
                    $xmlhash{$k}{XMLTVname}=$name;
                    $xmlhash{$k}{CallSign}||='';
                }
            }
       }elsif ($FileType eq 'rt'){
            my @temp;
            while  (<XM>){
                chomp;
                next if /^\s*#/;
                ($xmlid, undef, $name)=split /\|/, $_;
                next if ($name =~ /Do Not Use/);
                $k =$name;
                $k =~ s/\s//g;  $k=lc($k);   #key
                $xmlhash{$k}{XMLTVID}=$xmlid;
                $xmlhash{$k}{XMLTVname}=$name;
                $xmlhash{$k}{CallSign}||='';
            }
        }
        close XM;

        ReadMergeLog();
        #   author has come to the conclusion that hints in earlier code only added confusion.
        #   Merge log is simpler and better for the euser.

        #count matches and show results
        for (keys %xmlhash){
           $matches++ if (($xmlhash{$_}{XMLTVname} ne '') and ($xmlhash{$_}{CallSign} ne ''));
        }
        ShowXMLTV(0);
        mylog(0,"    $matches channels have been matched");
        SimpleBox("$matches channels have been matched.
Please manually merge further 
channels then 'commit' them.");
    };
    postmortem($@) if ($@);
}

sub ShowXMLTV{
    eval{
        mylog(0,"ShowXMLTV") if $_[0];track();

        my $count; 
        my $max=13;   #width of file callsign
        for (keys %xmlhash){
            $count=length $xmlhash{$_}{XMLTVname};
            $max=$count if $count>$max;
        }

        $showdata =''; $count=0;
        my $format= $columns{CallSign}[1] . '%7s  %-' . $max .'s %-20s';

        my $header = sprintf $format, 'CallSign', 'Row' , 'File_CallSign', 'XMLTVID';
        for (sort keys %xmlhash){
            $showdata .= sprintf "$format\n", $xmlhash{$_}{CallSign}, 
                     $count++, $xmlhash{$_}{XMLTVname}, $xmlhash{$_}{XMLTVID};
        }
        $headings -> configure(-text => $header, -anchor =>"nw", -justify=>'left');
        $pane2 -> configure(-text => $showdata, -anchor =>"nw", -justify=>'left');
        return;
    };
    postmortem($@) if ($@);
}


sub MatchXMLTV{
 
    eval{
        mylog(0,"MatchXMLTV");track();
        ShowXMLTV(0);
        my $text="Match database callsign to XMLTV name.\n (Give row for left column and row for right)\n eg 25:24";
        my ($reply, $input)=GetInput($text,'');
        return unless ($reply eq 'ok');
        unless ($input =~ m!^\s*\d+:\d+\s*$!){SimpleBox('Error: expected number:number'); return};
        my ($d, $x)=split /:/, $input;   #database & xmltv file refs
        #check rows valid
        my $L=scalar(keys %xmlhash)-1;
        if (($d<0) || ($d > $L) || ($x<0) || ($x>$L) || ($x==$d)){ SimpleBox("Invalid row"); return};
        my ($dname, $xname) = (sort keys %xmlhash)[$d, $x];
        return unless (&CheckOk("Matching: $xmlhash{$dname}{CallSign} -> $xmlhash{$xname}{XMLTVname}") eq 'ok');
        MatchXMLTVdetail($dname, $xname);
        ShowXMLTV(0);
        $xmltvmatchcount++;
    };
    postmortem($@) if ($@);
}

sub MatchXMLTVdetail{

    my ($dname, $xname)=@_;
    eval{
        mylog(0, "XMLTV merge $dname -> $xname");
        if ((!exists $xmlhash{$dname}) or (!exists $xmlhash{$xname})){ SimpleBox("Cannot merge $dname -> $xname"); return};
        $xmlhash{$dname}{XMLTVID}=$xmlhash{$xname}{XMLTVID};
        $xmlhash{$dname}{XMLTVname}=$xmlhash{$xname}{XMLTVname};
        delete $xmlhash{$xname} if $xmlhash{$xname}{CallSign} eq '';
        push @mergelog, "$dname:$xname";
    };
    postmortem($@) if ($@);
}

sub ReadMergeLog{
    eval{
        return unless (-e 'channels.merges');
        return if (CheckOk("Use previously saved XMLTV merges?") ne 'ok');
        unless (open  MERGES, '<channels.merges') {SimpleBox("Cannot open merge file"); return}; 
        mylog(0,"Reading merge log");    
        while (<MERGES>){
            if (/\s*#/){
            }elsif(/:/){
                chomp;
                MatchXMLTVdetail(split ':',$_);
            }
        }
        close MERGES;  
    };
    postmortem($@) if ($@);
}


sub CommitXMLTV{
    mylog(0,'CommitXMLTV');track();
    eval{
       if (scalar keys %xmlhash ==0){SimpleBox('Need to complete XMLTV import first!');return};

       #write XMLTVIDs to main hash
       my $k;
       ClearUflags();
       push @UndoPointer, scalar @Undo;  #remember where we started this undo batch
       for (keys %ChanData){
            next unless(($xmltvmultiplex eq '*') or ($xmltvmultiplex == $ChanData{$_}{SourceId}));  #sieve by source
   #        next unless state($_,'.V.');   #visible and non UseEIT
            
            $k=$ChanData{$_}{CallSign};
            $k =~s/\s//g;
            $k=lc($k);

            if ((defined $xmlhash{$k}) && ($xmlhash{$k}{XMLTVID} ne '')){  
                SetNewValue($_, 'XMLTVID', $xmlhash{$k}{XMLTVID});
            }
        }
        TidyData();
        refresh();

        #Write merge log out?
        return if $xmltvmatchcount==0;
        $_="XMLTVIDs have been written to the database image in memory.\n Do you now wish to save all the manual merges to a file for future use?";
        return if (CheckOk($_) ne 'ok');
        unless (open  MERGES, '>channels.merges') {SimpleBox("Cannot open merge file"); return}; 
        mylog(0,"Writing merge log file");  
        print MERGES "# Merge log written " . TimeStamp() . "\n";  
        while ($_=shift @mergelog){print MERGES "$_\n"};
        close MERGES;   
        $xmltvmatchcount=0;
    };
    postmortem($@) if ($@);
}

sub KillEscapes{
    my ($data)=@_;
    return $data unless ($data =~ /&\w+;/);
    my $a=';';    #trick to prevent wiki from corrupting this code 
    $data =~ s/&quot$a/"/g; 
    $data =~ s/&lt$a/</g; 
    $data =~ s/&gt$a/>/g; 
    $data =~ s/&apos$a/'/g; 
    $data =~ s/&amp$a/&/g; 
    $data;
}


#-------  Read backend --------

sub InterrogateBackend{

    eval{
        track('Interrogate backend');
        
        #Get video sources
        my $videosource; my %header;my $temp;
        track('VideoSourceList');
        $temp=&ReadDiagnostics('sources');
        ReadBackend($backend. '/Channel/VideoSourceList', $temp) unless (defined $spoof);

        if ($temp =~ m!<Version>(.*)</Version>!){$mythversion=$1};
        mylog(0, "MythTV version $mythversion");
        
        my $reply=FillHashofHash(%sources, $temp, 'VideoSource', 'Id', 'SourceName');
        mylog(0,"Found $reply video sources");    
         
        for my $source (sort keys %sources){
		    #get source:mpx info
            my %freqs=();
            track("GetMpxlist $source");

            $temp=&ReadDiagnostics("multiplex$source");
            unless (defined $spoof){
                ReadBackend($backend . '/Channel/GetVideoMultiplexList?SourceID='.$source, $temp);
            }
            $reply=FillHashofHash(%freqs, $temp, 'VideoMultiplex', 'MplexId',
                                  'Frequency','SIStandard');
            mylog(0,"Found $reply multiplexes in source $source");
            
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
            track("ChanInfo $source");
            $temp=&ReadDiagnostics("channels$source");
            unless (defined $spoof){
                ReadBackend($backend . '/Channel/GetChannelInfoList?SourceID='.$source.
                    '&OnlyVisible=false&Details=true', $temp);
            }
            if ($Extra){
                if ($temp !~ m!<ChannelInfo>.*?<$Extra>!s){print "-extra parameter $Extra not found in database.\n";exit 1}; 
            }
            my @items=columnlist('R');
            $reply=FillHashofHash(%temp, $temp, 'ChannelInfo', 'ChanId', @items);
            mylog(0,"Found $reply channels in source $source");


            #CommFree values change from 0/1 in 0.27 to false/true with 0.28pre.  Let's see which we are:
            $temp =~ m!<CommFree>(.*?)<!;
            if ($1 =~ /\d/){($CommFreeTrue, $CommFreeFalse)=(1,0)};

            #Add in multiplex hash
            for (keys %temp){
                #$temp{$_}{SourceId}= $source;
                #fix spurious multiplex=32767 (-1) in USA satellite data
                $temp{$_}{MplexId}=0 unless $multiplexesexist;
            }
            #add in to main hash
            %ChanData = (%ChanData, %temp);
        }

        #post-process channels:
  
        foreach (keys %ChanData){
            track("id=$_");
            #new state code
            $ChanData{$_}{Flags}='........';
            $ChanData{$_}{OldCallSign}='';

                     #count channels for multiplex listing
            my $k = "$ChanData{$_}{SourceId}";
            $k .= ":$ChanData{$_}{MplexId}";
            $MplexInfo{$k}{Count}++ if (defined $MplexInfo{$k});
        }
        TidyData();
        track('  Backend done');
    };    #end eval

    if ($@){
       if ($@ =~ /^500/){print "$@\n"; exit 0;};
       postmortem($@) ;
       exit 0;
    }
}

#-------help--------

sub Version{
    my $out= "MythTV Channel Editor\nVersion $version";
    $out .= "\n\nGPL license conditions\n\n";
    $out .= "Phil Brady 2016\n\nContact via:\nPhilB at MythTV Forum";
    SimpleBox($out);
}


sub helpwiki{
    eval{
          mylog(0, 'Help > wiki');
          my $url = 'https://www.mythtv.org/wiki/Channel_Editor';
          #my $url = 'https://www.mythtv.org/wiki/User:PhilB';
          my $platform = $^O;
          my $cmd;
          if    ($platform eq 'darwin')  { $cmd = "open \"$url\"";       }  # OS X
          elsif ($platform eq 'MSWin32' or $platform eq 'msys') { $cmd = "start \"\" \"$url\""; } # Windows native or MSYS / Git Bash
          elsif ($platform eq 'cygwin')  { $cmd = "cmd.exe /c start \"\" \"$url \""; } # Cygwin; !! Note the required trailing space.
          else { $cmd = "xdg-open \"$url\" & "; }  # assume a Freedesktop-compliant OS, which includes many Linux distros, PC-BSD, OpenSolaris, ...
          if (system($cmd) != 0) {
            mylog(0,"Help wiki fail.  Platform=$platform cmd=$cmd");
            mylog(1,"Please open wiki manually:  $url");
            SimpleBox("Cannot open wiki.  Please check log");
            
          }
    };
    postmortem($@) if ($@);
}


