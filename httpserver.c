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
#endif
#include <stdlib.h>
#include <stdio.h>
#include "mitlsffi.h"
#include "QUICFStar.h"
#include "QUICEngine.h"

QUICTypes_engine *eng;
SOCKET sock;
QUICTypes_mitls_ticket *ticket;
size_t MaxPacketLength;

#define DEFAULT_PORT 4433
char *port = "4433";
char *listen_addr;
char *root_path;

typedef struct _REQUEST {
  struct _REQUEST *Next;
  
  uint64_t id; // stream ID
  QUICTypes_quic_stream *strm; // stream pointer
  
  char Request[65536]; // the received HTTP request
  uint32_t RequestLength;
} REQUEST;

typedef struct _CONNECTION_STATE {
  QUICTypes_connection *cs;
  struct sockaddr_storage peer;  // The address to reply to
  
  REQUEST *Requests;
} CONNECTION_STATE;

THREAD_PROC(SendThread)
{
  char *packet = malloc(MaxPacketLength);
  while (1) {
    QUICEngine_eng_packet result;

    result = QUICEngine_quic_PreparePacket(eng, packet, MaxPacketLength);
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
  char *packet = malloc(MaxPacketLength);
  while (1) {
#if IS_WINDOWS    
    WSABUF buf;
    buf.len = MaxPacketLength;
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
      int err = WSAGetLastError();
      if (err == WSAECONNRESET) {
          // WSARecvFrom() documentation says that this code is returned if a previous
          // send operation resulted in an ICMP "Port Unreachable" error.
          //
          // Ignore it.
      } else {
        printf("WSAGetOverlappedResult() failed: %d\n", WSAGetLastError());
        exit(1);
      }
    }
#else
    int fromlen = sizeof(from);
    int r = recvfrom(sock, packet, MaxPacketLength, 0, (struct sockaddr*)&from, &fromlen);
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

SOCKET OpenServerSocket(const char *server, const char *port, /* out */ size_t *MaxPacketLength)
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
  *MaxPacketLength = 0;
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
	  switch (p->ai_family) {
		case AF_INET6:
			*MaxPacketLength = 1500-48; // 40-byte IPv6 header and 8-byte UDP header
		case AF_INET:
			*MaxPacketLength = 1500-28; // 20-byte IPv4 header and 8-byte UDP header
			break;
		default: // AF_NETBIOS, AF_IRDA, AF_BTH, etc.
			*MaxPacketLength = 1200;
			break;
	  }
      break;
    }
  }
  freeaddrinfo(pResult);
  return s;
}

void PrintUsageAndExit(void)
{
    printf("Usage:\n");
    printf("  -listen:<addr>\n");
    printf("  -port:<####>        default:%u\n", DEFAULT_PORT);
    printf("  -root:<path>\n");
    exit(1);
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
        } else if (strcmp(argname, "-root") == 0) {
            root_path = argopt;
        } else {
            printf("Invalid arg: %s\n", argname);
            PrintUsageAndExit();
        }
    }
    
    if (listen_addr == NULL || root_path == NULL) {
        PrintUsageAndExit();
    }
}

// Find an active request matching the stream ID, or allocate a new one.
REQUEST *GetRequest(CONNECTION_STATE *conn_state, uint64_t id)
{
    REQUEST *r = conn_state->Requests;
    while (r) {
        if (r->id == id) {
            return r;
        }
        r = r->Next;
    }
    r = (REQUEST*)malloc(sizeof(REQUEST));
    memset(r, 0, sizeof(*r));
    r->RequestLength = 0;
    r->Next = conn_state->Requests;
    conn_state->Requests = r;
    return r;
}

void ProcessRequest(CONNECTION_STATE *conn_state, REQUEST *r)
{
    r->Request[r->RequestLength] = '\0';
    
    if (_strnicmp(r->Request, "get ", 4)) {
        printf("Unsupported HTTP verb: (%s)\n", r->Request);
        return;
    }
    if (strstr(r->Request, "..")) {
        printf("Unsupported request containing a '..' path component: (%s)\n", r->Request);
        return;
    }
    char* end;
    if ((end = strchr(r->Request, '\n')) != NULL) {
        if (end[-1] == '\r') {
            end--;
        }
        end[0] = 0;
    }
    
    char FullPath[2048];
    strcpy_s(FullPath, sizeof(FullPath), root_path);
    strcat_s(FullPath, sizeof(FullPath), r->Request+5);
    
    FILE *fp = fopen(FullPath, "rb");
    if (fp == NULL) {
        // bugbug: report HTTP 404
        printf("Not found: file %s\n", FullPath);
    } else {
        printf("Sending file %s\n", FullPath);
        bool is_eof = false;
		const int MaxLength = 65536;
		char *buf = (char*)malloc(MaxLength);
        do {
            int result = fread(buf, 1, MaxLength, fp);
            is_eof = feof(fp);
            printf("Sending chunk length %d eof=%d\n", result, is_eof);
            QUICTypes_err__bool sresult = QUICStream_quic_SendStream(conn_state->cs, r->strm, (uint8_t*)buf, (uint32_t)result, (is_eof) ? TRUE: FALSE);
            if (sresult.tag != QUICTypes_Ok) {
                printf("SendStream failed: %s\n", sresult.case_Fail);
                break;
            }
        } while (!is_eof);
		free(buf);
    }
    printf("Finished request.\n");
}

void ProcessReceivedData(CONNECTION_STATE *conn_state, const QUICStream_data_recv *data)
{
      unsigned int id_low = (unsigned int)data->stream_id;
      unsigned int id_high = (unsigned int)(data->stream_id >> 32);
      if (data->recv_len == 0) {
        printf("Recv from cs=%p stream %u:%u\n<<empty>>\n", conn_state->cs, id_high, id_low);
      } else { // null-terminate the data string, as printf with *s depends on it.
        char ch = data->recv_data[data->recv_len-1];
        data->recv_data[data->recv_len-1] = '\0';
        printf("Recv from cs=%p stream %u:%u\n%*s%c\n", conn_state->cs, id_high, id_low, data->recv_len, data->recv_data, ch);
        data->recv_data[data->recv_len-1] = ch;
      }
      
      REQUEST *r = GetRequest(conn_state, data->stream_id);
      uint32_t Available = (uint32_t)sizeof(r->Request) - r->RequestLength;
      if (data->recv_len >= Available) {
          printf("Recv overflows the buffer.  Dropping.\n");
      } else {
          memcpy(&r->Request[r->RequestLength], data->recv_data, data->recv_len);
          r->RequestLength += data->recv_len;
      }
      if (r->strm == NULL) {
          r->strm = QUICStream_quic_OpenStream(conn_state->cs, data->stream_id);
      }
      if (QUICStream_quic_StreamIsFin(conn_state->cs, r->strm)) {
          ProcessRequest(conn_state, r);
      }
      free(data->recv_data);
}

void ProcessStreamReset(CONNECTION_STATE *conn_state, const QUICStream_reset_recv *data)
{
      unsigned int id_low = (unsigned int)data->rst_stream_id;
      unsigned int id_high = (unsigned int)(data->rst_stream_id >> 32);
      printf("Recv from cs=%p stream %u:%u - RST_STREAM Error %u\n", conn_state->cs, id_high, id_low, data->rst_error_code);
}

// One is created per connection
THREAD_PROC(ConnectionRecvThread)
{
    CONNECTION_STATE *conn_state = (CONNECTION_STATE *)lpv;
    QUICTypes_quic_stream *strm = NULL;
    while (1) {
      QUICStream_stream_recv data;
      data = QUICStream_quic_RecvStream(conn_state->cs);
      switch (data.tag) {
      case QUICStream_ReceivedData:
          ProcessReceivedData(conn_state, &data.case_ReceivedData);
          break;
      case QUICStream_Reset:
          ProcessStreamReset(conn_state, &data.case_Reset);
          break;
      default:
          printf("Unknown return from QUIC_RecvStream: %d\n", data.tag);
          break;
      }
      
    }
}

// Callback from QUIC-F* when a new connection has been established
intptr_t OnNewConnection(intptr_t eng_state, QUICTypes_connection *cs)
{
    CONNECTION_STATE *conn_state = malloc(sizeof(CONNECTION_STATE));
    conn_state->Requests = NULL;
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
  
  ParseServerArgs(argc, argv);

#if IS_WINDOWS  
  WSADATA wsaData;
  result = WSAStartup(MAKEWORD(2,2), &wsaData);
  if (result != 0) {
    printf("WSAStartup failed: %d\n", result);
    return 1;
  }
#endif  

  printf("Listening on %s:%s (root=%s)\n", listen_addr, port, root_path);
  
  eng = QUICEngine_quic_InitializeServer(listen_addr, OnNewConnection, 0 /* opaque state pointer */, 8 /* bytes for Connection IDs */);
  
  sock = OpenServerSocket(listen_addr, port, &MaxPacketLength);
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
