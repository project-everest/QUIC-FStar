# QUIC-F* - QUIC implemented in F*

## Building QUIC-F*
QUIC-F* depends on the [F* compiler](https://github.com/FStarLang/FStar) and [KreMLin](https://github.com/FStarLang/kremlin) tool in order to build.

QUIC-F* depends on a [miTLS](https://github.com/project-everest/mitls-fstar) and [EverCrypt](https://github.com/project-everest/hacl-star) binary drop:
* Source files: mipki.h, mitlsffi.h, quic_provider.h
* Import libs: ibmipki.lib, libmitls.lib, libquiccrypto.lib
* Binaries: libevercrypt.dll, libmipki.dll, libmitls.dll, libquiccrypto.dll

On Linux or Cygwin, run
```
make KREMLIN_HOME=<path_to_everest_kremlin_tree>
```
That will compile the F* source, extract to C source, and build binaries (httpclient and httpserver).  On Cygwin, they default to building with mingw.

On Windows, after running the Cygwin make, from a Visual Studio x64 command prompt, run
```
nmake -f makefile.vs
```
to compile the already-extracted C to build Windows 
native binaries (httpclientvs.exe and httpservervs.exe).

## Testing
### Server
Create a scratch directory to act as the root of the webserver (for example, c:\wwwroot).  And put some content there.  The default client app will open HandshakeMessages.fst (the name of a source file from the miTLS codebase).

Then run
```
httpservervs.exe --listen:127.0.0.1 -port:4443 -root:c:\wwwroot\
```
Note the trailing '\\' in the root path.  It is required.  The --listen address supports ipv6 addresses too.

### Client
Run
```
httpclientvs.exe
```
with no arguments, to connect to localhost on port 4443 and request file `HandshakeMessages.fst`.  To override, the first argument can be the server's name/address, and the second can be the port number.

The client will download the file and print it to stdout.

If the server sends back 0-RTT data, the client will store it in a file named `0rtt_ticket.dat` in the current directory.  On subsequent connections, if that file exists, the client will include that ticket in initiate a 0-RTT connection.  It is safe to simply delete the file, to initiate a 1-RTT connection.
