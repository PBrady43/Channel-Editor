#!/usr/bin/perl -w
package scan_database;
use strict;
use Exporter;
use LWP::UserAgent;  # needs 'sudo apt-get install libwww-perl'

#Version 1.01 25 Aug 2015.     APISupported ValidatePost and GetAPIParameters added.
#Version 1.02 26 Aug 2015.     Changes to ValidatePost:
#Version 1.03 15 Sep 2015.     Fixed bug:  Misuse of $_ in KillEscapes causes various problems with escape sequences.
#Version 1.04. 23 Sept 2015.   ValidatePost 'test' shows values extracted. 
#Version 1.05  24 Sept 2015.   Allow ReadBackend in scalar context - return 1 if ok, 0 if host not responding.
#                              Still die in void context.
#Version 1.06  29 Sept 2015.   Allow external access via 'our' %APICallingParameters.
#                              Fix bug if wsdl shows API call has no calling parameters.  Affects APISupported and 
#                              GetAPIParameters.
#Version 1.07   1 Oct 2015.    Rework of wsdl with no parameters 29/9/15.  (oops!).
#version 1.08  17 Oct 2015     Extend APISupported to return 1 if a get, 2 if a post. 
#                              Tweak to accept 0.28 wsdl format
#                              ValidatePost to return the POST response eg <bool>true</bool>.
#                              ValidatePost to check that it is a post function
#Version 1.09  10 Nov 2015     Request compressed content in ReadBackend.

# DOCUMENTATION:  See https://www.mythtv.org/wiki/Perl_API_examples


our $VERSION     = 1.09;
our @ISA         = qw(Exporter);
our @EXPORT      = qw(ReadBackend FillHashofHash GetAllFields APISupported ValidatePost GetDBinfo GetDBheader GetAPIParameters);

my $browseropen=0;
my $browser;
my $counter;
our %APICallingParameters;
our %APItype;


#steering file for GetDBHeader and GetDBinfo
my %steer = (
    getchannelinfolist  => ['Channel/GetChannelInfoList', 'ChannelInfo','ChannelInfos'],
    getrecordedlist     => ['Dvr/GetRecordedList?Descending=true', 'Program','Programs'],
    videosourcelist     => ['Channel/VideoSourceList', 'VideoSource','VideoSources'],
    
    #add more like this => [url, separator for getDBinfo, separator for getDBheader],  
);

#--------------------------
# published routines follow
#--------------------------

sub ReadBackend($\$) {
 
    my ($url, $buff)=@_;
    unless ($browseropen){
        $browser = LWP::UserAgent->new;
        $browser->timeout(10);
        $browser->default_header('accept-Encoding' => 'gzip,deflate'); 
        $browseropen = 1;
    }
    my $response = $browser->get(tidyurl($url));
    unless($response->is_success){
        (defined wantarray()) || die $response->status_line;
        return 0;
    }
    $$buff = $response -> decoded_content;
    return 1;
}
#------------------------------
sub FillHashofHash(\%\$@){

    my ($hashref, $buff, $separator, $key_name, @params)=@_;
    %$hashref=();
    $counter=0;
    my $endrecord;
    my $base=index($$buff, "<$separator>");
    
    while ($base>-1){
        my $nextbase=index($$buff, "<$separator>", $base+10);
        $endrecord= ($nextbase<0)?length($$buff):$nextbase;
        &ProcessRecord($hashref, $buff, $base, $endrecord, $key_name, @params);
        $base=$nextbase;
        $counter++;
    }
    return $counter;
}
#-------------------------

sub GetAllFields(\%\$@){

    #   Read the buffer and populate a hash with all tags found between delimiting text.
    #   GetAllFields(%hash, $buffer, $start_text, $end_text)
    #       if $start_text or $end_text are empty strings, then start or end of buffer are assumed.
    #       eg
    #       ReadBackend('192.168.1.67:6544/Channel/GetChannelInfoList', $buffer)
    #       GetAllfields(%hash, $buffer, '', '<ChannelInfos>')
    #       print "$hash{'ProtoVer'}\n";
    
    my ($hashref, $buff, $start_text,$end_text)=@_;

    my $start_index= $start_text?index($$buff,$start_text):0;
    if ($start_index<0) {die "cannot find start string $start_text"};

    my $end_index= $end_text? index($$buff,$end_text,$start_index):length($$buff);
    if ($end_index<0){die "cannot find end string $end_text"};

    %$hashref=();
    $counter=0;
    my @bits = split />/, substr($$buff,$start_index,$end_index-$start_index);
    foreach (@bits){
        if (m!([^<]*)</(.*)!) {
            $$hashref{$2}=&KillEscapes($1);
            $counter++;
        }elsif (/^\s?<([^\/]*)\/\s?$/){
            $$hashref{$1}='';
            $counter++;
        } 
    }
    $counter;
}

#-----------------------------
sub APISupported($){
    #Check API against wsdl.
    #return 0=not known, 1=a GET, 2=a POST
    my ($APIurl)=@_;
    if ($APIurl =~ /\?/) {die "APISupported does not expect '?' in $APIurl"};
    my @URLbits = split '/', $APIurl;
    my $apicall=pop(@URLbits);
    my $service=$URLbits[-1];
    $apicall = $service . '/' . $apicall;
  
    #Do we know about this api service?  
    unless (defined $APICallingParameters{$service}){
        # Nope!  do a wsdl call        
        push  @URLbits, 'wsdl';
        my $url=join '/', @URLbits;
        my $content;
        ReadBackend($url,$content);
        #$content=&GetDummyWsdl;   #test facility

        while ($content =~ m!<xs:element name="(\w*)">(.*?)</xs:complexType>!gs){
            (my $func, my $list)=($1, $2);
              
            unless ($func =~ /Response$/){
                @{$APICallingParameters{$service .'/' . $func}}=();  #In case no params found
                while ($list =~ m!name="(\w*)"!g){
                    push ( @{$APICallingParameters{$service .'/' . $func}}, $1);
                }
            }
        } 
        $APICallingParameters{$service}=1;  #to allow caching
        
        #now see if post or get: sample text is:
        #     <operation name="AddVideoSource"><documentation>POST </documentation>
        while ($content =~ /<operation name="([\w]*)">\s?<documentation>([\w]*)/g) {
            if ($2 eq 'POST') {
                $APItype{$service .'/' .$1}=2;
            }elsif ($2 eq 'GET'){
                $APItype{$service .'/' .$1}=1;
            }else{
                die "Not recognised operation type $2 for API $1 in APISupported"
            }
        }    
    }
    return $APItype{$apicall} || 0;
}
#----------------------
sub GetAPIParameters($){
    my ($p)=@_;
    unless (APISupported($p)){die "Unsupported API $p"};
    my @URLbits = split '/', $p;
    $p=$URLbits[-2] . '/' .$URLbits[-1];
    @{${APICallingParameters{$p}}};
}


#------------------------
sub ValidatePost(\%$$$){

    #Validate data for a POST before issuing it
    my ($hashref, $APIurl,$action, $SanityCount)=@_;

    unless ($APIurl =~ /^http:/) {$APIurl= 'http://' . $APIurl};
    unless ($action =~ /^post$|^test$|^raw$|^quiettest$/){
        die "ValidatePost actions are post, test, quiettest or raw.  $action not supported"
    };

    unless (&APISupported($APIurl)==2){
        if ($action !~ /quiettest/){print "$APIurl not supported or not a post on this backend"};
        if ($action =~ /test/){return 1};
        die '';
    }
     
    #split the url
    
    my @URLbits = split '/', $APIurl;
    my $apicall=pop(@URLbits);
    my $service=$URLbits[-1];
    $apicall = $service . '/' . $apicall;

    #ok, start by generating equivalent parameter names
    my %alias;my $k, my $v;
    while (($k, $v) = each %$hashref){
            $_=$k; 
            unless ($action =~ /raw/){$v=&InsertEscapes($v)};
            $alias{$_}=$v;
            $_=lc $_; $alias{$_}=$v;
            s/chan/channel/ unless (/channel/);
            s/freq/frequency/ unless (/frequency/);
            s/num$/number/;
            s/auth$/authority/;
            $alias{$_}=$v;
    }

    
   #now let us check against the wsdl output - build up a valid hash in %final
    my $missing=0;my %final;my $found=0;
    for (GetAPIParameters($APIurl)){    
        if (defined $alias{lc $_}){
            if ($action eq 'test'){print "   $apicall found $_: Setting to: $alias{lc $_}\n"};
            $final{$_}=$alias{lc $_};
            $found++;
        }elsif (defined $alias{"#$_"}){
            #ok to omit this one - user declares it as optional.
            $found++;
        }else{
            print "** $apicall needs $_ **\n" unless  ($action eq 'quiettest');
            $missing++;
        }
    }
    if ($found<$SanityCount){
        #something has gone horribly wrong!
        $missing++; #to force exit
        unless ($action =~ /quiet/){
            print "Failed sanity check:  found $found params but expected at least $SanityCount\n";
        }
    }
    
    if ($action =~ /test/){return ($missing==0)?1:0};
    if ($missing){die "Unsafe to proceed with ValidatePost "};
    
    #Now post it!
    my $response = $browser -> post($APIurl,\%final);
    unless($response->is_success){die "Error updating recording"}; 
    my $url_buffer = $response -> content; 
    return $url_buffer;
}


#--------------
sub GetDBheader{
    #deprecated.
    #expects hash reference as first item; returns count of header items. 

    my ($hashref, $ip_addr, $class,$extra)=@_;
    $class=lc $class; 
    unless (defined ($steer{$class})) {die "Sorry - $class not supported"};
    $counter=0;
    #read from backend 
    my $url= &FormURL($ip_addr, $steer{$class}[0], $extra);
    my $buffer;
    ReadBackend($url, $buffer);
    return GetAllFields(%$hashref, $buffer,'',$steer{$class}[2]);
}
#---------------------

sub GetDBinfo{

my ($hashref, $ip_addr, $class, $extra, $key_name, @params)=@_;

    $class=lc $class; 
    unless (defined ($steer{$class})) {die "Sorry - $class not supported"};
 
    #read from backend 
    my $url= &FormURL($ip_addr, $steer{$class}[0], $extra);
    my $buffer;
    ReadBackend($url, $buffer);
    #process buffer
    FillHashofHash(%$hashref, $buffer, $steer{$class}[1], $key_name, @params);
}


#-------------------------
#internal routines follow
#-------------------------

sub tidyurl{
    my ($url)=@_;
    $url='http://'. $url unless ($url =~ m!^http://!);
    $url;
}


sub FormURL{
    #used in 
    my ($ip, $class, $extra)=@_;
    my $addr="http://$ip:6544/$class";
    if ($extra){
        if ($addr =~ /\?/){
            $addr .= '&' . $extra;
        }else{
            $addr .= '?' . $extra;
        }
    }
    return $addr;
}


sub getparameter{
    my ($param, $buff, $base, $endat) = @_;

    my $start= index($$buff, "<$param>",$base);
   
    if (($start<0) or ($start>$endat)) {
        #oops!  look for <param/> instead
        $start= index($$buff, "<$param/>",$base);
        if (($start>0) and ($start < $endat)){return ''};
        die "cannot find $param in record";
    }
    $start=$start + length($param) +2;
    my $end=index($$buff, "</$param>", $start);
    my $data=substr $$buff, $start, $end-$start;
    return &KillEscapes($data);
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
#   $data =~ s/&amp$a/&/g; 
#   $data =~ s/&amp$a/&/g; 
    $data;
}

sub InsertEscapes{
    my ($data)= @_;
    $a=';';
    $data =~ s/&/&amp$a/g; 
    $data =~ s/"/&quot$a/g; 
    $data =~ s/</&lt$a/g; 
    $data =~ s/>/&gt$a/g; 
    $data =~ s/'/&apos$a/g; 
    $data;
}
sub ProcessRecord{
    #strip interesting data from record (where record=channel, recording, video source etc)
    my ($hashref, $buff, $start_at, $endat, $key_name, @params) = @_;

    my $key=$counter;
    if ($key_name ne '#'){ $key=&getparameter($key_name,$buff, $start_at, $endat)};

    foreach (@params){
        if (/^#$/){
            $$hashref{$key}{$_}=$counter;
        }else{
            $$hashref{$key}{$_}=&getparameter($_, $buff, $start_at, $endat);
            my $t=$$hashref{$key}{$_};
        }
    }
}
sub GetDummyWsdl{
    #developer test facility to check sample 0.28 wsdl.  Please ignore this!
    my $in; my $out;
    open FH, '<wsdl28.xml';
    while ($in = <FH>){$out .= $in};
    close FH;
    $out;
}
1;
