#if defined(_MSC_VER) || defined(__MINGW32__)
// Compiling for Windows
#define IS_WINDOWS 1

#define _WIN32_WINNT 0x0600 // for WSAConnectByName
#include <winsock2.h>
#include <windows.h>
#include <mswsock.h>
#include <ws2tcpip.h>
#define THREAD_PROC(x) DWORD WINAPI x(LPVOID lpv)
#else
// Compiling for Unix
#define IS_WINDOWS 0

#include <sys/types.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <pthread.h>
#include <sys/errno.h>
#include <netdb.h>
#include <unistd.h>
typedef int SOCKET;
typedef struct addrinfo ADDRINFO;
#define INVALID_SOCKET -1
#define SOCKET_ERROR -1
#define WSAGetLastError() errno
#define closesocket close
#define THREAD_PROC(x) void* x(void* lpv)
typedef void* PTP_POOL;
#endif
#include <stdlib.h>
#include <stdio.h>
#include "mitlsffi.h"
#include "QUICFStar.h"
#include "QUICEngine.h"

QUICTypes_engine *eng;
SOCKET sock;
QUICTypes_mitls_ticket *ticket;

typedef struct _CONNECTION_STATE {
  QUICTypes_connection *cs;
  struct sockaddr_storage peer;  // The address to reply to
} CONNECTION_STATE;

THREAD_PROC(SendThread)
{
  while (1) {
    char packet[2048];
    QUICEngine_eng_packet result;

    result = QUICEngine_quic_PreparePacket(eng, packet, sizeof(packet));
    if (result.packet_len == 0xffffffff) {
      printf("QUIC_PreparePacket failed\n");
      exit(1);
    } else if (result.packet_len == 0) {
      // false alarm.
      continue;
    }
    CONNECTION_STATE *conn_state = (CONNECTION_STATE*)result.app_data;
    printf("Sending 0x%x bytes\n", result.packet_len);
#if IS_WINDOWS    
    WSABUF buf;
    buf.len = result.packet_len;
    buf.buf = packet;
    DWORD NumberOfBytesSent;
    int s = WSASendTo(sock, &buf, 1, &NumberOfBytesSent, 0, (struct sockaddr*)&conn_state->peer, sizeof(conn_state->peer), NULL, NULL);
    if (s == SOCKET_ERROR) {
      printf("WSASendTo() failed: %d\n", WSAGetLastError());
      exit(1);
    }
#else
    int s = sendto(sock, packet, result.packet_len, 0, (struct sockaddr*)&conn_state->peer, sizeof(conn_state->peer));
    if (s == -1) {
      printf("sendto() failed: %d\n", errno);
      exit(1);
    }
#endif
  }
}

struct sockaddr_storage from;

THREAD_PROC(RecvThread)
{
#if IS_WINDOWS  
  WSAOVERLAPPED o = {0};
  o.hEvent = WSACreateEvent();
#endif
  while (1) {
    char packet[2048];
#if IS_WINDOWS    
    WSABUF buf;
    buf.len = sizeof(packet);
    buf.buf = packet;
    DWORD dwBytesReceived;
    DWORD dwFlags = 0;
    INT fromlen = sizeof(from);
    int result = WSARecvFrom(sock, &buf, 1, NULL, &dwFlags, (struct sockaddr*)&from, &fromlen, &o, NULL);
    if (result == SOCKET_ERROR && (WSAGetLastError() != WSA_IO_PENDING)) {
      printf("WSARecvFrom() failed: %d\n", WSAGetLastError());
      exit(1);
    }
    if (!WSAGetOverlappedResult(sock, &o, &dwBytesReceived, TRUE, &dwFlags)) {
      printf("WSAGetOverlappedResult() failed: %d\n", WSAGetLastError());
      exit(1);
    }
#else
    int fromlen = sizeof(from);
    int r = recvfrom(sock, packet, sizeof(packet), 0, (struct sockaddr*)&from, &fromlen);
    if (r == -1) {
      printf("recvfrom() failed: %d\n", errno);
      exit(1);
    }
    unsigned int dwBytesReceived = (unsigned int)r;
#endif
    printf("Received 0x%x bytes\n", dwBytesReceived);
    uint32_t ret = QUICConnection_quic_ProcessPacket(eng, packet, dwBytesReceived);
    if (ret == 0xffffffff) {
      printf("QUIC_ProcessPacket failed!\n");
      exit(2);
    }
  }
}

SOCKET OpenClientSocket(const char *server, const char *port, /* out */ struct sockaddr_storage *pdest)
{
  ADDRINFO hints = {
    AI_PASSIVE, // ai_flags
    AF_UNSPEC,  // ai_family
    SOCK_DGRAM, // ai_socktype
    0,          // ai_protocol
    0,          // ai_addrlen
    NULL,       // ai_canonname
    NULL,       // ai_addr
    NULL,       // ai_next
  };
  ADDRINFO *pResult;
  int r = getaddrinfo(server, port, &hints, &pResult);
  if (r != 0) {
    // failed
    printf("getaddrinfo failed for '%s:%s' - %d\n", server, port, r);
    return INVALID_SOCKET;
  }
  ADDRINFO *p;
  SOCKET s = INVALID_SOCKET;
  for (p=pResult; p!=NULL; p=p->ai_next) {
#if IS_WINDOWS
    s = WSASocket(p->ai_family, SOCK_DGRAM, IPPROTO_UDP, NULL, 0, WSA_FLAG_OVERLAPPED);
#else
    s = socket(p->ai_family, SOCK_DGRAM, IPPROTO_UDP);
#endif
    if (s != INVALID_SOCKET) {
      struct sockaddr_storage local = {0}; // Initialize as INADDR_ANY /  in6addr_any 
      local.ss_family = p->ai_family; // then set the family to match the server
      if (bind(s, (struct sockaddr*)&local, sizeof(local)) == SOCKET_ERROR) {
        printf("bind() failed - gle=%d\n", WSAGetLastError());
        closesocket(s);
        return INVALID_SOCKET;
      }
      memcpy(pdest, p->ai_addr, p->ai_addrlen);
      break;
    }
  }
  freeaddrinfo(pResult);
  return s;
}

SOCKET OpenServerSocket(const char *server, const char *port)
{
  ADDRINFO hints = {
    AI_PASSIVE, // ai_flags
    AF_UNSPEC,  // ai_family
    SOCK_DGRAM, // ai_socktype
    0,          // ai_protocol
    0,          // ai_addrlen
    NULL,       // ai_canonname
    NULL,       // ai_addr
    NULL,       // ai_next
  };
  ADDRINFO *pResult;
  int r = getaddrinfo(server, port, &hints, &pResult);
  if (r != 0) {
    // failed
    printf("getaddrinfo failed for '%s:%s' - %d\n", server, port, r);
    return INVALID_SOCKET;
  }
  ADDRINFO *p;
  SOCKET s = INVALID_SOCKET;
  for (p=pResult; p!=NULL; p=p->ai_next) {
#if IS_WINDOWS    
    s = WSASocket(p->ai_family, SOCK_DGRAM, IPPROTO_UDP, NULL, 0, WSA_FLAG_OVERLAPPED);
#else
    s = socket(p->ai_family, SOCK_DGRAM, IPPROTO_UDP);
#endif
    if (s != INVALID_SOCKET) {
      if (bind(s, p->ai_addr, p->ai_addrlen) == SOCKET_ERROR) {
        printf("bind() failed - gle=%d\n", WSAGetLastError());
        closesocket(s);
        return INVALID_SOCKET;
      }
      break;
    }
  }
  freeaddrinfo(pResult);
  return s;
}

void SaveTicket(const QUICTypes_mitls_ticket *ticket, const char *server, const char *port)
{
  FILE *fp = fopen("0rtt_ticket.dat", "wb");
  if (!fp) {
    return;
  }
  fprintf(fp, "%s\n%s\n", server, port);
  fwrite(&ticket->ticket_len, sizeof(ticket->ticket_len), 1, fp);
  fwrite(&ticket->session_len, sizeof(ticket->session_len), 1, fp);
  fwrite(ticket->ticket, ticket->ticket_len, 1, fp);
  fwrite(ticket->session, ticket->session_len, 1, fp);
  fclose(fp);
  printf("Saved 0RTT ticket\n");
}

QUICTypes_mitls_ticket *LoadTicket(const char *server, const char *port)
{
  FILE *fp = fopen("0rtt_ticket.dat", "rb");
  if (!fp) {
    printf("Not using 0RTT - no ticket file present\n");
    return NULL;
  }
  char buf[1024];

  if (fgets(buf, sizeof(buf), fp) == NULL) {
    printf("Not using 0RTT - ticket file is corrupt (server)\n");
    fclose(fp);
    return NULL;
  }
  char *p = strchr(buf, '\n');
  if (p) {
    *p = '\0';
  }
  if (strcmp(server, buf) != 0) {
    printf("Not using 0RTT - server mismatch '%s' vs '%s'\n", server, buf);
    fclose(fp);
    return NULL;
  }
  
  if (fgets(buf, sizeof(buf), fp) == NULL) {
    printf("Not using 0RTT - ticket file is corrupt (port)\n");
    fclose(fp);
    return NULL;
  }
  p = strchr(buf, '\n');
  if (p) {
    *p = '\0';
  }
  if (strcmp(port, buf) != 0) {
    printf("Not using 0RTT - port mismatch\n");
    fclose(fp);
    return NULL;
  }

  // Server and port match.  Use the ticket.
  QUICTypes_mitls_ticket *ticket = malloc(sizeof(QUICTypes_mitls_ticket));
  if (!ticket) {
    printf("Not using 0RTT - out of memory\n");
    fclose(fp);
    return NULL;
  }
  if (fread(&ticket->ticket_len, sizeof(ticket->ticket_len), 1, fp) != 1) {
    printf("Not using 0RTT - ticket file is corrupt (ticket_len)\n");
    fclose(fp);
    free(ticket);
    return NULL;
  }
  if (fread(&ticket->session_len, sizeof(ticket->session_len), 1, fp) != 1) {
    printf("Not using 0RTT - ticket file is corrupt (session_len)\n");
    fclose(fp);
    free(ticket);
    return NULL;
  }
  ticket->ticket = malloc(ticket->ticket_len);
  if (ticket->ticket == NULL) {
    printf("Not using 0RTT - out of memory or corrupt ticket file (ticket)\n");
    fclose(fp);
    free(ticket);
    return NULL;
  }
  ticket->session = malloc(ticket->session_len);
  if (ticket->session == NULL) {
    printf("Not using 0RTT - out of memory or corrupt ticket file (session)\n");
    fclose(fp);
    free(ticket->ticket);
    free(ticket);
    return NULL;
  }
  if (fread(ticket->ticket, ticket->ticket_len, 1, fp) != 1 ||
      fread(ticket->session, ticket->session_len, 1, fp) != 1) {
    printf("Not using 0RTT - ticket file is corrupt (read ticket and session)\n");
    fclose(fp);
    free(ticket->ticket);
    free(ticket->session);
    free(ticket);
    return NULL;
  }
  fclose(fp);
  printf("Using 0RTT ticket!\n");
  return ticket;
}

#define DEFAULT_PORT 4433
#define DEFAULT_TIMEOUT (60*1000) // ms
#define DEFAULT_CONNECTIONS 1
#define DEFAULT_LENGTH 1200
#define DEFAULT_SERVER_BIDI 100
#define DEFAULT_SERVER_UNI 100

// Common args
char *port = "4433";

// Client args
char *target_hostname;
//int num_connections = DEFAULT_CONNECTIONS;
int bidi_stream_count;
int uni_stream_count=1;
int bidi_rem_stream_count;
int uni_rem_stream_count;
int ping_length=DEFAULT_LENGTH;
int timeout=DEFAULT_TIMEOUT;

// Server args
char *listen_addr;
int server_bidi_stream_count=DEFAULT_SERVER_BIDI;
int server_uni_stream_count=DEFAULT_SERVER_UNI;

void PrintUsageAndExit(void)
{
    printf("Client Usage:\n");
    printf("  -target:<hostname>\n");
    printf("  -port:<####>        default:%u\n", DEFAULT_PORT);
    printf("  -timeout:<####>     default:%u\n", DEFAULT_TIMEOUT);
    //printf("  -connections:<####> default:%u\n", DEFAULT_CONNECTIONS);
    printf("  -bidi:<####>        default:0\n");
    printf("  -uni:<####>         default:1\n");
    printf("  -length:<####>      default:%u\n", DEFAULT_LENGTH);
    printf("  -bidirem:<####>     default:0\n"); // bugbug: implement;
    printf("  -unirem:<####>      default:0\n");
    printf("\n");
    printf("Server Usage:\n");
    printf("  -listen:<addr>\n");
    printf("  -port:<####>        default:%u\n", DEFAULT_PORT);
    printf("  -bidi:<####>        default:%u\n", DEFAULT_SERVER_BIDI);
    printf("  -uni:<####>         default:%u\n", DEFAULT_SERVER_UNI);
    printf("  -length:<####>      default:%u\n", DEFAULT_LENGTH);
    exit(1);
}

void ParseClientArgs(int argc, char* argv[])
{
    for (int i=1; i<argc; ++i) {
        char *argname = argv[i];
        char *argopt = strchr(argname, ':');
        if (argopt) {
            *argopt = '\0';
            argopt++;
        }
        if (strcmp(argname, "-target")==0) {
            if (argopt == NULL) {
                printf("Error:  -target must include ':hostname'\n");
                PrintUsageAndExit();
            }
            target_hostname = argopt; 
        } else if (strcmp(argname, "-port")==0) {
            if (argopt == NULL) {
                printf("Error:  -port must include ':portnumber'\n");
                PrintUsageAndExit();
            }
            port = argopt;
        //} else if (strcmp(argname, "-connections") == 0) {
        //    if (argopt == NULL) {
        //        printf("Error:  -port must include ':portnumber'\n");
        //        PrintUsageAndExit();
        //    }
        //    num_connections = atoi(argopt);
        } else if (strcmp(argname, "-bidi") == 0) {
            bidi_stream_count = (argopt==NULL) ? 1 : atoi(argopt);
        } else if (strcmp(argname, "-uni") == 0) {
            uni_stream_count = (argopt==NULL) ? 1 : atoi(argopt);
        } else if (strcmp(argname, "-bidirem") == 0) {
            bidi_rem_stream_count = (argopt==NULL) ? 1 : atoi(argopt);
        } else if (strcmp(argname, "-unirem") == 0) {
            uni_rem_stream_count = (argopt==NULL) ? 1 : atoi(argopt);
        } else if (strcmp(argname, "-length")==0) {
            if (argopt == NULL) {
                printf("Error:  -length must include ':bytecount'\n");
                PrintUsageAndExit();
            }
            ping_length = atoi(argopt);
        } else if (strcmp(argname, "-timeout")==0) {
            if (argopt == NULL) {
                printf("Error:  -timeout must include ':time_in_ms'\n");
                PrintUsageAndExit();
            }
            timeout = atoi(argopt);
        } else {
            printf("Invalid arg: %s\n", argname);
            PrintUsageAndExit();
        }
    }
}

void ParseServerArgs(int argc, char* argv[])
{
    for (int i=1; i<argc; ++i) {
        char *argname = argv[i];
        char *argopt = strchr(argname, ':');
        if (argopt) {
            *argopt = '\0';
            argopt++;
        }
        if (strcmp(argname, "-listen")==0) {
            if (argopt == NULL) {
                printf("Error:  -listen must include ':addr'\n");
                PrintUsageAndExit();
            }
            listen_addr = argopt; 
        } else if (strcmp(argname, "-port")==0) {
            if (argopt == NULL) {
                printf("Error:  -port must include ':portnumber'\n");
                PrintUsageAndExit();
            }
            port = argopt;
        } else if (strcmp(argname, "-bidi") == 0) {
            server_bidi_stream_count = (argopt==NULL) ? 1 : atoi(argopt);
        } else if (strcmp(argname, "-uni") == 0) {
            server_uni_stream_count = (argopt==NULL) ? 1 : atoi(argopt);
        } else if (strcmp(argname, "-length")==0) {
            if (argopt == NULL) {
                printf("Error:  -length must include ':bytecount'\n");
                PrintUsageAndExit();
            }
            ping_length = atoi(argopt);
        } else {
            printf("Invalid arg: %s\n", argname);
            PrintUsageAndExit();
        }
    }
}

bool IsClient(int argc, char *argv[])
{
    for (int i=1; i<argc; ++i) {
        if (strncmp(argv[i], "-target:", 8) == 0) {
            return true;
        } else if (strncmp(argv[i], "-listen:", 8) == 0) {
            return false;
        }
    }
    PrintUsageAndExit();
    exit(1);
}

#if IS_WINDOWS
HANDLE hPingsComplete;
#else
pthread_mutex_t hPingsCompleteMutex;
pthread_cond_t  hPingsCompleteCond;
int PingsComplete;
#endif
volatile long int PingStreamsActive;

typedef struct _PingStream {
  QUICTypes_connection *cs;
  uint64_t StreamID;
  char *StreamBuffer;
} PingStream;

PingStream* NewPingStream(QUICTypes_connection *cs, uint64_t StreamID) {
  PingStream *p = (PingStream*)malloc(sizeof(PingStream));
  p->cs = cs;
  p->StreamID = StreamID;
  p->StreamBuffer = (char*)malloc(ping_length);
  memset(p->StreamBuffer, 0, ping_length);
#if IS_WINDOWS
  sprintf_s(p->StreamBuffer, ping_length, "%I64u", StreamID);
#else
  unsigned int id_low = (unsigned int)StreamID;
  unsigned int id_high = (unsigned int)(StreamID >> 32);
  snprintf(p->StreamBuffer, ping_length, "%u:%u", id_high, id_low);
#endif
  return p;
}

void StartPingStream(PingStream *p)
{
  QUICTypes_quic_stream *strm = QUICStream_quic_OpenStream(p->cs, p->StreamID);
  if (!strm) {
    unsigned int id_low = (unsigned int)p->StreamID;
    unsigned int id_high = (unsigned int)(p->StreamID >> 32);
    printf("Error during OpenStream for %u:%u.  Aborting.\n", id_high, id_low);
    exit(3);
  }
  QUICStream_quic_SendStream(p->cs, strm, p->StreamBuffer, ping_length, 1);
  
#if IS_WINDOWS    
  if (InterlockedDecrement(&PingStreamsActive) == 0) {
    SetEvent(hPingsComplete);
  }
#else
  pthread_mutex_lock(&hPingsCompleteMutex);
  PingStreamsActive--;
  if (PingStreamsActive == 0) {
    PingsComplete = 1;
    pthread_cond_signal(&hPingsCompleteCond);
  }
  pthread_mutex_unlock(&hPingsCompleteMutex);
#endif
  
  free(p->StreamBuffer);
  free(p);
}

#if IS_WINDOWS
VOID CALLBACK PingStreamWorkCallback(
    PTP_CALLBACK_INSTANCE Instance,
    PVOID                 Parameter,
    PTP_WORK              Work
    )
{
    PingStream *s = (PingStream*)Parameter;
    StartPingStream(s);
}
#else
THREAD_PROC(PingStreamWorkCallback)
{
  PingStream *s = (PingStream*)lpv;
  StartPingStream(s);
}
#endif

void CreatePingStream(QUICTypes_connection *cs, PTP_POOL pool, uint64_t StreamID)
{
  PingStream *s = NewPingStream(cs, StreamID);
  if (pool) {
#if IS_WINDOWS    
    PTP_WORK_CALLBACK workcallback = PingStreamWorkCallback;
    PTP_WORK work = CreateThreadpoolWork(workcallback, s, NULL);
    SubmitThreadpoolWork(work);
#else
    pthread_t t;
    pthread_create(&t, NULL, PingStreamWorkCallback, (void*)s);
#endif
  } else {
    StartPingStream(s);
  }
}

int DoClient(void)
{
  printf("Connecting to %s:%s\n", target_hostname, port);

  eng = QUICEngine_quic_InitializeClient(target_hostname, 8); // 8-byte Connection IDs
  if (!eng) {
    printf("QUIC_InitializeClient failed!\n");
    return 1;
  }
  
  struct sockaddr_storage peer;
  sock = OpenClientSocket(target_hostname, port, &peer);
  if (sock == INVALID_SOCKET) {
    printf("OpenClientSocket() failed\n");
    return 1;
  }
  
  QUICTypes_connection *cs = QUICEngine_quic_GetClient(eng);
  if (!cs) {
    printf("Error during handshake.  Aborting.\n");
    return 2;
  }
  CONNECTION_STATE *conn_state = malloc(sizeof(CONNECTION_STATE));
  conn_state->cs = cs;
  memcpy(&conn_state->peer, &peer, sizeof(conn_state->peer));
  QUICConnection_quic_SetAppState(cs, (intptr_t)conn_state);

#if IS_WINDOWS
  HANDLE hRecv = CreateThread(NULL, 0, RecvThread, NULL, 0, NULL);
  HANDLE hSend = CreateThread(NULL, 0, SendThread, NULL, 0, NULL);
#else
  pthread_t hRecv;
  pthread_t hSend;
  pthread_create(&hRecv, NULL, RecvThread, NULL);
  pthread_create(&hSend, NULL, SendThread, NULL);
#endif
  
  ticket = LoadTicket(target_hostname, port);
  if (ticket) {
    QUICConnection_quic_SetTicket(cs, ticket);
  }
  
  QUICConnection_quic_Handshake(cs);

#if IS_WINDOWS  
  hPingsComplete = CreateEvent(NULL, FALSE, FALSE, NULL);
#else
  pthread_mutex_init(&hPingsCompleteMutex, NULL);
  pthread_cond_init(&hPingsCompleteCond, NULL);
#endif
  PingStreamsActive = bidi_stream_count + uni_stream_count;
  PTP_POOL pool = NULL;
  if (PingStreamsActive > 1) {
#if IS_WINDOWS    
      pool = CreateThreadpool(NULL);
#else
      pool = (PTP_POOL)1;
#endif
  }
  uint64_t StreamID = 4; // lowest client-initiated bidi stream (stream 0 is for TLS)
  for (int i=0; i<bidi_stream_count; ++i) {
    CreatePingStream(cs, pool, StreamID);
    StreamID += 4;
  }
  StreamID = 2; // lowest client-initiated uni stream
  for (int i=0; i<uni_stream_count; ++i) {
    CreatePingStream(cs, pool, StreamID);
    StreamID += 4;
  }
#if IS_WINDOWS
  DWORD dw = WaitForSingleObject(hPingsComplete, timeout);
  if (dw == STATUS_TIMEOUT) {
      printf("Timeout!\n");
      return 3;
  }
#else
  struct timespec ts;
  pthread_mutex_lock(&hPingsCompleteMutex);
  clock_gettime(CLOCK_REALTIME, &ts);
  ts.tv_sec += (timeout+999)/1000;
  do {
    pthread_cond_timedwait(&hPingsCompleteCond, &hPingsCompleteMutex, &ts);
  } while (!PingsComplete);
  pthread_mutex_unlock(&hPingsCompleteMutex);
#endif
  printf("Success!\n");
  QUICConnection_quic_CloseConnection(cs);
#if IS_WINDOWS
  Sleep(1000); // give the connection enough time to complete the close.
#else
  sleep(1);
#endif
  return 0;
}

// One is created per connection
THREAD_PROC(ConnectionRecvThread)
{
    CONNECTION_STATE *conn_state = (CONNECTION_STATE *)lpv;
    while (1) {
      QUICStream_stream_recv data;
      data = QUICStream_quic_RecvStream(conn_state->cs);
      switch (data.tag) {
      case QUICStream_ReceivedData: {
          unsigned int id_low = (unsigned int)data.case_ReceivedData.stream_id;
          unsigned int id_high = (unsigned int)(data.case_ReceivedData.stream_id >> 32);
          printf("Recv from cs=%p stream %u:%u\n%*s\n", conn_state->cs, id_high, id_low, data.case_ReceivedData.recv_len, data.case_ReceivedData.recv_data);
          }
          break;
      case QUICStream_Reset: {
          unsigned int id_low = (unsigned int)data.case_Reset.rst_stream_id;
          unsigned int id_high = (unsigned int)(data.case_Reset.rst_stream_id >> 32);
          printf("Recv from cs=%p stream %u:%u:  RST_STREAM %u\n", conn_state->cs, id_high, id_low, data.case_Reset.rst_error_code);
          }
          break;
      default:
        printf("Unknown return from QUIC_RevStream: %d\n", data.tag);
        break;
      }
    }
}

// Callback from QUIC-F* when a new connection has been established
intptr_t OnNewConnection(intptr_t eng_state, QUICTypes_connection *cs)
{
    CONNECTION_STATE *conn_state = malloc(sizeof(CONNECTION_STATE));
    conn_state->cs = cs;
    memcpy(&conn_state->peer, &from, sizeof(conn_state->peer));
    if (cs) {
#if IS_WINDOWS      
        HANDLE hConnRecv = CreateThread(NULL, 0, ConnectionRecvThread, conn_state, 0, NULL);
#else
	pthread_t hConnRecv;
	pthread_create(&hConnRecv, NULL, ConnectionRecvThread, (void*)conn_state);
#endif
    } // else cs==NULL means a connectionless scenario:  version negotiation
    printf("OnNewConnection was called!\n");
    return (intptr_t)conn_state;
}

int DoServer(void)
{
  printf("Listening on %s:%s\n", listen_addr, port);
  
  eng = QUICEngine_quic_InitializeServer(listen_addr, OnNewConnection, 0 /* opaque state pointer */, 8 /* bytes for Connection IDs */);
  
  sock = OpenServerSocket(listen_addr, port);
  if (sock == INVALID_SOCKET) {
    printf("OpenServerSocket() failed\n");
    return 1;
  }
  
#if IS_WINDOWS  
  HANDLE hRecv = CreateThread(NULL, 0, RecvThread, NULL, 0, NULL);
  HANDLE hSend = CreateThread(NULL, 0, SendThread, NULL, 0, NULL);
#else
  pthread_t hRecv;
  pthread_t hSend;
  pthread_create(&hRecv, NULL, RecvThread, NULL);
  pthread_create(&hSend, NULL, SendThread, NULL);
#endif

  printf("Success\n");
#if IS_WINDOWS
  Sleep(INFINITE);
#else
  sleep(0xffffffff);
#endif
  return 0;
}

int SetGlobalTicketKey(void)
{
    unsigned char r[12+32];
    
    srand(time(NULL));
    for (int i=0; i<sizeof(r); ++i) {
        r[i] = (unsigned char)rand();
    }
    return FFI_mitls_set_ticket_key("CHACHA20-POLY1305", r, sizeof(r));
}

int main(int argc, char* argv[])
{
  int result;

  result = FFI_mitls_init();
  if (result == 0) {
    printf("FFI_mitls_init() failed\n");
    return 1;
  }
  result = SetGlobalTicketKey();
  if (result == 0) {
      printf("FFI_mitls_set_ticket_key failed\n");
      return 1;
  }
  
#if IS_WINDOWS  
  WSADATA wsaData;
  result = WSAStartup(MAKEWORD(2,2), &wsaData);
  if (result != 0) {
    printf("WSAStartup failed: %d\n", result);
    return 1;
  }
#endif
  
  if (IsClient(argc, argv)) {
      ParseClientArgs(argc, argv);
      int ret = DoClient();
      exit(ret);
  } else {
      ParseServerArgs(argc, argv);
      int ret = DoServer();
      exit(ret);
  }
  
  return 0;
}
