#!/usr/bin/perl

use IO::Socket;

$socket = IO::Socket::INET->new(PeerAddr => 'localhost',
                                PeerPort => 7777,
                                Proto    => "tcp",
                                Type     => SOCK_STREAM);

print $socket "x.UP\n";
print <$socket>;

