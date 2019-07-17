KREMLIN_HOME	?= ../everest/kremlin
MITLS_HOME      ?= ../everest/mitls-fstar
KRML_BIN        = $(KREMLIN_HOME)/_build/src/Kremlin.native
QUIC_OPTS       = -cc msvc -skip-compilation -I . -warn-error @4
KRML            = $(KRML_BIN) $(KOPTS) $(TEST_OPTS)
CCOPTS          = -g -I$(KREMLIN_HOME)/include/ -I$(KREMLIN_HOME)/kremlib/extracted/ -I$(MITLS_HOME)/libs/ffi -I$(MITLS_HOME)/src/pki -I. -Werror
CCOPTS_KRML     = -g -I$(KREMLIN_HOME)/include/ -I$(KREMLIN_HOME)/kremlib/extracted/ -I$(MITLS_HOME)/libs/ffi -I$(MITLS_HOME)/src/pki -I. -DQUIC_KREMLIN=1 --include QUICFStar.h -Werror
CC              ?= x86_64-w64-mingw32-gcc

ifeq ($(OS),Windows_NT)
MITLS_LIBS=$(MITLS_HOME)/src/windows/mitls/libmitls.lib $(MITLS_HOME)/src/windows/quiccrypto/libquiccrypto.lib $(MITLS_HOME)/src/pki/libmipki.lib
LINK_LIBS=-lws2_32
else
MITLS_LIBS=libmitls.so libquiccrypto.so libmipki.so
LINK_LIBS=-lpthread
endif

all: httpclient.exe pingfstar.exe httpserver.exe

verify: DoublyLinkedList.fst-ver DoublyLinkedListIface.fst-ver DoublyLinkedListIface.fsti-ver

-include .depend

FSTAR_INCLUDE_ARGS = \
	--include $(KREMLIN_HOME)/kremlib

FSTAR_ADDITIONAL_ARGS ?=

FSTAR_ARGS = $(FSTAR_INCLUDE_ARGS) $(FSTAR_ADDITIONAL_ARGS)
FSTAR = fstar.exe $(FSTAR_ARGS)

%-ver: %.checked
	@true

%-in:
	@echo $(FSTAR_INCLUDE_ARGS)

%.checked:
	@echo "[Verifying] $<"
	@$(FSTAR) --cache_checked_modules --record_hints --use_hints $< >/dev/null
	@echo "[Verified] $*"

FST_FILES=$(shell find . -name '*.fst')
FSTI_FILES=$(shell find . -name '*.fsti')

dep.graph: $(FST_FILES) $(FSTI_FILES)
	@echo "[Generating dependencies]"
	@$(FSTAR) --dep graph $^ 2>/dev/null 1>/dev/null
	@echo "[Generated dependencies]"

%.png: %.graph
	cat $< | grep -v fstar_ | grep -v lowstar_ | grep -v prims | tred | dot -Tpng -o$@

depgraph: dep.png

depend: .depend
	@true

.depend: $(FST_FILES) $(FSTI_FILES)
	$(FSTAR) --dep full $^ 2>/dev/null >.depend

QUIC_OBJS = QUICTypes.o QUICMutators.o QUICUtils.o QUICFFI.o QUICConnection.o QUICStream.o QUICFrame.o QUICLossAndCongestion.o QUICEngine.o QUICTLS.o QUICFStar.o $(MITLS_LIBS) $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a C_Failure.o

QUICTypes.c QUICTypes.h QUICMutators.c QUICMutators.h QUICUtils.c QUICUtils.h QUICFFI.c QUICFFI.h QUICConnection.c QUICConnection.h QUICStream.c QUICStream.h QUICFrame.c QUICFrame.h QUICLossAndCongestion.c QUICLossAndCongestion.h QUICEngine.c QUICEngine.h QUICTLS.c QUICTLS.h FStar.h C_Failure.c C_Failure.h: QuicKremlin

.INTERMEDIATE: QuicKremlin
QuicKremlin: QUICTypes.fst QUICMutators.fst QUICUtils.fst QUICFFI.fst QUICConnection.fst QUICStream.fst QUICFrame.fst QUICLossAndCongestion.fst QUICEngine.fst QUICTLS.fst
	$(KRML) $(QUIC_OPTS) QUICTypes.fst QUICMutators.fst QUICUtils.fst QUICFFI.fst QUICConnection.fst QUICStream.fst QUICFrame.fst QUICLossAndCongestion.fst QUICEngine.fst QUICTLS.fst

C_Failure.o: C_Failure.c
	$(CC) $(CCOPTS_KRML) -c -o C_Failure.o $<
    
QUICFStar.o: QUICFStar.c FStar.h
	$(CC) $(CCOPTS_KRML) -c QUICFStar.c

QUICTypes.o: QUICTypes.c QUICTypes.h
	$(CC) $(CCOPTS_KRML) -c QUICTypes.c

QUICMutators.o: QUICMutators.c QUICMutators.h QUICTypes.h
	$(CC) $(CCOPTS_KRML) -c QUICMutators.c

QUICUtils.o: QUICUtils.c QUICUtils.h QUICTypes.h
	$(CC) $(CCOPTS_KRML) -c QUICUtils.c

QUICFFI.o: QUICFFI.c QUICFFI.h QUICTypes.h
	$(CC) $(CCOPTS_KRML) -c QUICFFI.c

QUICConnection.o: QUICConnection.c QUICConnection.h QUICTypes.h QUICUtils.h QUICFFI.h QUICMutators.h
	$(CC) $(CCOPTS_KRML) -c QUICConnection.c

QUICStream.o: QUICStream.c QUICStream.h QUICTypes.h QUICMutators.h
	$(CC) $(CCOPTS_KRML) -c QUICStream.c

QUICFrame.o: QUICFrame.c QUICFrame.h QUICLossAndCongestion.h QUICStream.h QUICTypes.h QUICUtils.h QUICMutators.h
	$(CC) $(CCOPTS_KRML) -c QUICFrame.c

QUICLossAndCongestion.o: QUICLossAndCongestion.c QUICLossAndCongestion.h QUICTypes.h QUICStream.h QUICMutators.h
	$(CC) $(CCOPTS_KRML) -c QUICLossAndCongestion.c

QUICEngine.o: QUICEngine.c QUICEngine.h QUICTypes.h QUICMutators.h QUICConnection.h QUICFFI.h QUICLossAndCongestion.h
	$(CC) $(CCOPTS_KRML) -c QUICEngine.c

QUICTLS.o: QUICTLS.c QUICTypes.h QUICFFI.h QUICUtils.h QUICMutators.h QUICFFI.h
	$(CC) $(CCOPTS_KRML) -c QUICTLS.c

httpclient.o: httpclient.c QUICTypes.h QUICUtils.h QUICFFI.h QUICConnection.h
	$(CC) $(CCOPTS) -c httpclient.c

httpserver.o: httpserver.c QUICTypes.h QUICUtils.h QUICFFI.h QUICConnection.h
	$(CC) $(CCOPTS) -c httpserver.c

httpclient.exe: httpclient.o $(QUIC_OBJS)
	$(CC) -g -o httpclient.exe httpclient.o $(QUIC_OBJS) $(LINK_LIBS)

httpserver.exe: httpserver.o $(QUIC_OBJS)
	$(CC) -g -o httpserver.exe httpserver.o $(QUIC_OBJS) $(LINK_LIBS)

pingfstar.o: pingfstar.c QUICTypes.h QUICUtils.h QUICFFI.h QUICConnection.h
	$(CC) $(CCOPTS) -c pingfstar.c

pingfstar.exe: pingfstar.o $(QUIC_OBJS)
	$(CC) -g -o pingfstar.exe pingfstar.o $(QUIC_OBJS) $(LINK_LIBS)

clean:
	-rm *.exe
	-rm *.o
	-rm FStar.c FStar.h Prims.c Prims.h
	-rm QUICTypes.c QUICTypes.h QUICUtils.c QUICUtils.h QUICFFI.c QUICFFI.h QUICConnection.c QUICConnection.h QUICMutators.c QUICMutators.h QUICStream.c QUICStream.h QUICEngine.c QUICEngine.h

