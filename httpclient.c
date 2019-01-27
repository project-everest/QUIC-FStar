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

typedef struct _CONNECTION_STATE {
  struct sockaddr_storage peer;  // The address to reply to
} CONNECTION_STATE;

THREAD_PROC(SendThread)
{
  char *packet = malloc(MaxPacketLength);
  while (1) {
    QUICEngine_eng_packet result;

    result = QUICEngine_quic_PreparePacket(eng, packet, MaxPacketLength);
    if (result.packet_len == 0xffffffff) {
      KRML_HOST_PRINTF("QUIC_PreparePacket failed\n");
      exit(1);
    } else if (result.packet_len == 0) {
      // false alarm.
      continue;
    }
    CONNECTION_STATE *conn_state = (CONNECTION_STATE*)result.app_data;
    KRML_HOST_PRINTF("Sending 0x%x bytes\n", result.packet_len);
#if IS_WINDOWS    
    WSABUF buf;
    buf.len = result.packet_len;
    buf.buf = packet;
    DWORD NumberOfBytesSent;
    int s = WSASendTo(sock, &buf, 1, &NumberOfBytesSent, 0, (struct sockaddr*)&conn_state->peer, sizeof(conn_state->peer), NULL, NULL);
    if (s == SOCKET_ERROR) {
      KRML_HOST_PRINTF("WSASendTo() failed: %d\n", WSAGetLastError());
      exit(1);
    }
#else
    int s = sendto(sock, packet, result.packet_len, 0, (struct sockaddr*)&conn_state->peer, sizeof(conn_state->peer));
    if (s == -1) {
      KRML_HOST_PRINTF("sendto() failed: %d\n", errno);
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
      KRML_HOST_PRINTF("WSARecvFrom() failed: %d\n", WSAGetLastError());
      exit(1);
    }
    if (!WSAGetOverlappedResult(sock, &o, &dwBytesReceived, TRUE, &dwFlags)) {
      KRML_HOST_PRINTF("WSAGetOverlappedResult() failed: %d\n", WSAGetLastError());
      exit(1);
    }
#else
    int fromlen = sizeof(from);
    int r = recvfrom(sock, packet, MaxPacketLength, 0, (struct sockaddr*)&from, &fromlen);
    if (r == -1) {
      KRML_HOST_PRINTF("recvfrom() failed: %d\n", errno);
      exit(1);
    }
    unsigned int dwBytesReceived = (unsigned int)r;
#endif
    KRML_HOST_PRINTF("Received 0x%x bytes\n", dwBytesReceived);
    uint32_t ret = QUICConnection_quic_ProcessPacket(eng, packet, dwBytesReceived);
    if (ret == 0xffffffff) {
      KRML_HOST_PRINTF("QUIC_ProcessPacket failed!\n");
      exit(2);
    }
  }
}

SOCKET OpenClientSocket(const char *server, const char *port, /* out */ struct sockaddr_storage *pdest, /* out */ size_t *MaxPacketLength)
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
  *MaxPacketLength = 0;
  int r = getaddrinfo(server, port, &hints, &pResult);
  if (r != 0) {
    // failed
    KRML_HOST_PRINTF("getaddrinfo failed for '%s:%s' - %d\n", server, port, r);
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
        KRML_HOST_PRINTF("bind() failed - gle=%d\n", WSAGetLastError());
        closesocket(s);
        return INVALID_SOCKET;
      }
      memcpy(pdest, p->ai_addr, p->ai_addrlen);
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

  char *server = (argc > 1) ? argv[1] : "127.0.0.1";
  char *port = (argc > 2) ? argv[2] : "4433";

  printf("Connecting to %s:%s\n", server, port);

  eng = QUICEngine_quic_InitializeClient(server, 8); // use 8-byte connection IDs
  if (!eng) {
    printf("QUIC_InitializeClient failed!\n");
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

  struct sockaddr_storage peer;
  sock = OpenClientSocket(server, port, &peer, &MaxPacketLength);
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

  ticket = LoadTicket(server, port);
  if (ticket) {
    QUICConnection_quic_SetTicket(cs, ticket);
  }
  
  QUICConnection_quic_SetMaxStreamID(cs, 5);
  QUICConnection_quic_SetMaxData(cs, 512*1024);
  QUICConnection_quic_Handshake(cs);

  // Stream 0 is the first client-initiated bidirectional stream #
  QUICTypes_quic_stream *strm1 = QUICStream_quic_OpenStream(cs, 0u);
  if (!strm1) {
    printf("Error during OpenStream.  Aborting.\n");
    return 3;
  }
  char *request = "GET /HandshakeMessages.fst\r\n";
  QUICTypes_err__bool sresult = QUICStream_quic_SendStream(cs, strm1, request, strlen(request), 1);
  if (sresult.tag != QUICTypes_Ok) {
      printf("SendStream failed: %s\n", sresult.case_Fail);
      return 1;
  }
  printf("Send message\n");
  FILE *fp = fopen("result.txt", "wb");
  while (!QUICStream_quic_StreamIsFin(cs, strm1)) {
    if (!ticket) {
      ticket = QUICConnection_quic_GetTicket(cs);
      if (ticket) {
        SaveTicket(ticket, server, port);
      }
    }

    QUICStream_stream_recv data;
    data = QUICStream_quic_RecvStream(cs);
    switch (data.tag) {
    case QUICStream_ReceivedData: {
        unsigned int id_low = (unsigned int)data.case_ReceivedData.stream_id;
        unsigned int id_high = (unsigned int)(data.case_ReceivedData.stream_id >> 32);
        //printf("Recv from stream %u:%u\n%*s\n", id_high, id_low, data.recv_len, data.recv_data);
        char lastChar = data.case_ReceivedData.recv_data[data.case_ReceivedData.recv_len - 1];
        data.case_ReceivedData.recv_data[data.case_ReceivedData.recv_len - 1] = '\0'; // NULL-terminate, as %*s is unhappy if the string isn't
        printf("%*s%c", data.case_ReceivedData.recv_len, data.case_ReceivedData.recv_data, lastChar);
        data.case_ReceivedData.recv_data[data.case_ReceivedData.recv_len - 1] = lastChar;
        fwrite(data.case_ReceivedData.recv_data, sizeof(char), data.case_ReceivedData.recv_len, fp);
        free(data.case_ReceivedData.recv_data);
      }
      break;

   case QUICStream_Reset: {
        unsigned int id_low = (unsigned int)data.case_Reset.rst_stream_id;
        unsigned int id_high = (unsigned int)(data.case_Reset.rst_stream_id >> 32);
        printf("Stream  %u:%u was reset by the peer:  Error code=%u\n", id_high, id_low, data.case_Reset.rst_error_code);
      }
      break;

   default:
     printf("Unknown return code from RecvStream: %d\n", data.tag);
     break;
     }
  }
  fclose(fp);
  printf("***** DONE *****\n");
  QUICConnection_quic_CloseConnection(cs); // queue an async CONNECTION_CLOSE
  
  // allow async work to happen
#if IS_WINDOWS
  Sleep(2*1000);
#else
  sleep(5);
#endif

  return 0;
}
