!IFNDEF KREMLIN_HOME
KREMLIN_HOME = ../../../everest/kremlin
!ENDIF

CCOPTS = /nologo /Od /MD /Zi /DKRML_NOUINT128=1 -I $(KREMLIN_HOME)\include -I.
CCOPTS_KRML = $(CCOPTS) -DQUIC_KREMLIN=1 -FIQUICFStar.h
QUIC_OBJS = QUICTypes.obj QUICMutators.obj QUICUtils.obj QUICFFI.obj QUICConnection.obj QUICStream.obj QUICFrame.obj QUICLossAndCongestion.obj QUICEngine.obj QUICTLS.obj QUICFStar.obj C_Failure.obj libmitls.lib libquiccrypto.lib libmipki.lib libkremlib.lib

all: httpclientVS.exe pingfstarVS.exe httpserverVS.exe

C_Failure.obj: C_Failure.c C_Failure.h
    cl $(CCOPTS_KRML) -c -FoC_Failure.obj C_Failure.c

httpclient.obj: httpclient.c QUICTypes.h QUICFFI.h QUICConnection.h QUICMutators.h
    cl $(CCOPTS) -c httpclient.c

httpserver.obj: httpserver.c QUICTypes.h QUICFFI.h QUICConnection.h QUICMutators.h
    cl $(CCOPTS) -c httpserver.c

httpclientVS.exe: httpclient.obj $(QUIC_OBJS)
    cl /nologo /FehttpclientVS.exe /MD /Zi httpclient.obj $(QUIC_OBJS) ws2_32.lib ntdll.lib
    
httpserverVS.exe: httpserver.obj $(QUIC_OBJS)
    cl /nologo /FehttpserverVS.exe /MD /Zi httpserver.obj $(QUIC_OBJS) ws2_32.lib ntdll.lib
    
pingfstar.obj: pingfstar.c QUICTypes.h QUICFFI.h QUICConnection.h QUICMutators.h
    cl $(CCOPTS) -c pingfstar.c

pingfstarVS.exe: pingfstar.obj $(QUIC_OBJS)
    cl /nologo /FepingfstarVS.exe /MD /Zi pingfstar.obj $(QUIC_OBJS) ws2_32.lib ntdll.lib

.c.obj::
    cl $(CCOPTS_KRML) /MP -c $<

clean:
    -del *VS.exe
    -del *.obj
