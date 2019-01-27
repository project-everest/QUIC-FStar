#if defined(_MSC_VER) || defined(__MINGW32__)
// Compiling for Windows
#define IS_WINDOWS 1

#define _WIN32_WINNT 0x0600
#include "kremlib.h"
#include <windows.h>
#include <threadpoolapiset.h>
#else
// Compiling for Unix
#define IS_WINDOWS 0
#include "kremlib.h"
#include <pthread.h>
#include <sys/time.h>
#include <sys/errno.h>
#include <alloca.h>
#define _alloca alloca
#endif

// Temporarily rename functions whose signatures don't quite match F*'s
#define FFI_mitls_quic_process ignore_quic_process
#define FFI_mitls_find_custom_extension ignore_find_custom_extension
#define FFI_mitls_quic_free ignore_quic_free
#define FFI_mitls_quic_get_record_key ignore_mitls_quic_get_record_key
#include "mitlsffi.h"
#undef FFI_mitls_quic_process
#undef FFI_mitls_find_custom_extension
#undef FFI_mitls_quic_free
#undef FFI_mitls_quic_get_record_key

#include "QUICFFI.h"
#include "mipki.h"

#if IS_WINDOWS
typedef struct _timer_holder {
  HANDLE hThread;
  HANDLE hTimer;
  PTP_TIMER_CALLBACK cb;
  void *cb_state;
} timer_holder;

#else
enum _event_holder_type {
  AutoResetEvent,
  ManualResetEvent
};

typedef struct _manual_event_holder {
} manual_event_holder;

typedef struct _event_holder {
  enum _event_holder_type t;
  
  pthread_mutex_t mutex;
  pthread_cond_t cond;
  int is_set;
  int handle_refcount;
} event_holder;

typedef struct _critical_section {
  pthread_mutex_t mutex;
  pthread_t owning_thread;
  uint32_t lock_count;
} critical_section;

enum _timer_holder_type {
  NoTimer,
  PeriodicTimer,
  OneShotTimer
};

typedef void (*PTP_TIMER_CALLBACK)(void *state, void *context, void* timer);

typedef struct _timer_holder {
  pthread_t thread;
  PTP_TIMER_CALLBACK cb;
  void *cb_state;
  pthread_mutex_t mutex;
  pthread_cond_t cond;
  int is_cancelled;
  enum _timer_holder_type t;
  
  int64_t DueTime;    // for OneShot
  uint32_t msPeriod;  // for Periodic
} timer_holder;

#endif // !IS_WINDOWS

intptr_t QUICFFI_createEvent(int32_t x0, int32_t x1)
{
#if IS_WINDOWS  
    return (intptr_t)CreateEventW(NULL, x0, x1, NULL);
#else
    event_holder *e = (event_holder*)malloc(sizeof(*e));
    pthread_mutex_init(&e->mutex, NULL);
    pthread_cond_init(&e->cond, NULL);
    e->handle_refcount = 1;
    
    if (x0) {
      // Manual-reset event
      e->t = ManualResetEvent;
    } else {
      // Auto-reset event
      e->t = AutoResetEvent;
    }
    
    if (x1) {
      e->is_set = 1;
      pthread_cond_signal(&e->cond);
    } else {
      e->is_set = 0;
    }
#endif
}

#if !IS_WINDOWS
void addrefHandle(event_holder *e)
{
    __sync_fetch_and_add(&e->handle_refcount, 1);
}

void releaseHandle(event_holder *e)
{
    int refcount = __sync_fetch_and_sub(&e->handle_refcount, 1);
    if (refcount == 0) {
        pthread_mutex_destroy(&e->mutex);
        pthread_cond_destroy(&e->cond);
        free(e);
    }
}
#endif

void QUICFFI_closeHandle(intptr_t h)
{
#if IS_WINDOWS
    CloseHandle((HANDLE)h);
#else
    event_holder *e = (event_holder *)h;
    releaseHandle(e);
#endif
}

intptr_t QUICFFI_monitorAlloc(void)
{
#if IS_WINDOWS
  PCRITICAL_SECTION p = (PCRITICAL_SECTION)malloc(sizeof(*p));
  InitializeCriticalSection(p);
  return (intptr_t)p;
#else
  critical_section *p = (critical_section*)malloc(sizeof(*p));
  pthread_mutex_init(&p->mutex, NULL);
  p->owning_thread = 0;
  p->lock_count = 0;
  return(intptr_t)p;
#endif
}

void QUICFFI_monitorEnter(intptr_t cs)
{
#if IS_WINDOWS
  EnterCriticalSection((PCRITICAL_SECTION)cs);
#else
  critical_section *p = (critical_section*)cs;
  if (pthread_self() == p->owning_thread) {
    p->lock_count++;
  } else {
    pthread_mutex_lock(&p->mutex);
    p->lock_count=1;
    p->owning_thread = pthread_self();
  }
#endif
}

void QUICFFI_monitorExit(intptr_t cs)
{
#if IS_WINDOWS
  LeaveCriticalSection((PCRITICAL_SECTION)cs);
#else
  critical_section *p = (critical_section*)cs;
  if (0 == p->lock_count) {
    printf("Error!  exiting a lock that isn't owned!\n");
    exit(1);
  } else if (pthread_self() != p->owning_thread) {
    printf("Error!  exiting a lock not owned by the current thread!\n");
    exit(1);
  }
  p->lock_count--;
  if (0 == p->lock_count) {
    p->owning_thread = 0;
    pthread_mutex_unlock(&p->mutex);
  }
#endif
}

void QUICFFI_waitForSingleObject(intptr_t h, uint32_t dwMilliseconds)
{
#if IS_WINDOWS
  WaitForSingleObject((HANDLE)h, dwMilliseconds);
#else
  event_holder *e = (event_holder*)h;
  
  addrefHandle(e);
  pthread_mutex_lock(&e->mutex);
  while (!e->is_set) {
    pthread_cond_wait(&e->cond, &e->mutex);
  }
  if (e->t == AutoResetEvent) {
    e->is_set = 0;
  }
  pthread_mutex_unlock(&e->mutex);
  releaseHandle(e);
#endif
}

void QUICFFI_setEvent(intptr_t h)
{
#if IS_WINDOWS  
  SetEvent((HANDLE)h);
#else
  event_holder *e = (event_holder*)h;
  
  // Note that this wakes up AT LEAST one thread.
  pthread_mutex_lock(&e->mutex);
  e->is_set = 1;
  pthread_cond_signal(&e->cond);
  pthread_mutex_unlock(&e->mutex);
#endif  
}

void QUICFFI_resetEvent(intptr_t h)
{
#if IS_WINDOWS
  ResetEvent((HANDLE)h);
#else
  event_holder *e = (event_holder*)h;
  
  pthread_mutex_lock(&e->mutex);
  e->is_set = 0;
  pthread_mutex_unlock(&e->mutex);
#endif
}

char 	*stpcpy(char *__restrict s1, const char *__restrict s2)
{
  strcpy(s1, s2);
  return s1 + strlen(s2);
}

// Return the current time in 100 ns intervals
int64_t QUICFFI_getSystemTime(void)
{
#if IS_WINDOWS
  SYSTEMTIME st;
  LARGE_INTEGER li;
  GetSystemTime(&st);
  SystemTimeToFileTime(&st, (FILETIME*)&li);
  return li.QuadPart;
#else
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC, &t) != 0) {
    printf("clock_gettime failed!\n");
    exit(1);
  }
  int64_t seconds_part = (int64_t)t.tv_sec * 10000;
  int64_t ns_part = (int64_t)t.tv_nsec/100;
  return seconds_part + ns_part;
#endif
}

uint32_t QUICFFI_intptr_t_to_uint32(intptr_t p)
{
  return (uint32_t)p;
}

intptr_t QUICFFI_uint32_to_intptr_t(uint32_t p)
{
  return (intptr_t)p;
}

typedef int (*qsort_compare)(const void *, const void *);
void QUICFFI_qsort64(uint64_t *buffer, uint32_t length, int (__cdecl *compare )(uint64_t *, uint64_t *))
{ 
  qsort(buffer, length, sizeof(uint64_t), (qsort_compare)compare);
}

intptr_t QUICFFI_createTimer(QUICTypes_connection *x0, void (*pfnti)(intptr_t x0, QUICTypes_connection *x1, intptr_t x2))
{
#if IS_WINDOWS
  timer_holder *t = (timer_holder*)malloc(sizeof(*t));
  if (!t) {
    return (intptr_t)0;
  }
  t->cb = (PTP_TIMER_CALLBACK)pfnti;
  t->cb_state = x0;
  t->hTimer = CreateWaitableTimer(NULL, FALSE, NULL);
  t->hThread = NULL;
  return (intptr_t)t;
#else
  timer_holder *t = (timer_holder*)malloc(sizeof(*t));
  if (!t) {
    return (intptr_t)0;
  }
  t->thread = 0;
  t->DueTime = 0;
  t->msPeriod = 0;
  t->t = NoTimer;
  t->cb = (PTP_TIMER_CALLBACK)pfnti;
  t->cb_state = x0;
  t->is_cancelled = 0;
  pthread_mutex_init(&t->mutex, NULL);
  pthread_cond_init(&t->cond, NULL);
  return (intptr_t)t;
#endif
}

#if IS_WINDOWS
DWORD WINAPI TimerProc(void *lpv)
{
    timer_holder *t = (timer_holder*)lpv;

    while (1) {
        DWORD dw = WaitForSingleObject(t->hTimer, INFINITE);
        if (dw == STATUS_WAIT_0) {
          // The timer fired.  Call the callback then reset.
          (t->cb)(NULL, t->cb_state, (PTP_TIMER)t);
        } else {
          // Something went wrong.
          printf("TimerProc:  WFSO failed gle=%d\n", GetLastError());
        }
    }

    return 0;
}
#else // !IS_WINDOWS
#define TICKS_PER_SEC (10*1000*1000)
#define NSEC_PER_SEC  (1000*1000*1000)
#define TICKS_PER_NSEC (10)
#define TICKS_PER_MS  (10*1000)
void AbsoluteFromRelative(struct timespec *ts, int64_t rel_ticks) // in 100ns ticks
{
  struct timeval tv;
  gettimeofday(&tv, NULL);

  int rel_sec = rel_ticks / TICKS_PER_SEC;
  int rel_nsec=(rel_ticks % TICKS_PER_SEC) * TICKS_PER_NSEC;
  
  ts->tv_sec = tv.tv_sec + rel_sec;
  ts->tv_nsec = (tv.tv_usec * 1000) + rel_nsec;
  ts->tv_sec += ts->tv_nsec / NSEC_PER_SEC;
  ts->tv_nsec %= NSEC_PER_SEC;
}

void *OneShotTimerProc(void *lpv)
{
  timer_holder *t = (timer_holder*)lpv;
  struct timespec ts;
  
  // t->DueTime is in 100ns units and is relative to now
  while (1) {
    AbsoluteFromRelative(&ts, t->DueTime);
    pthread_mutex_lock(&t->mutex);
    int r = pthread_cond_timedwait(&t->cond, &t->mutex, &ts);
    if (t->is_cancelled) {
      // The timer was cancelled.
      pthread_mutex_unlock(&t->mutex);
      break;
    } else if (r == ETIMEDOUT) {
      // The timer fired.  Call the callback then reset.
      (t->cb)(NULL, t->cb_state, t);
      t->t = NoTimer;
      pthread_mutex_unlock(&t->mutex);
      break;
    } else {
      // Else the cond was signalled but the timer wasn't cancelled.  Update
      // the duetime and wait again.
      pthread_mutex_unlock(&t->mutex);
    }
  }

  return t;
}

void *PeriodicTimerProc(void *lpv)
{
  timer_holder *t = (timer_holder*)lpv;
  struct timespec ts;

  while (1) {
    AbsoluteFromRelative(&ts, ((int64_t)t->msPeriod) * TICKS_PER_MS);
    pthread_mutex_lock(&t->mutex);
    pthread_cond_timedwait(&t->cond, &t->mutex, &ts);
    if (t->is_cancelled) {
      t->t = NoTimer;
      pthread_mutex_unlock(&t->mutex);
      break;
    }
    (t->cb)(NULL, t->cb_state, t);
    pthread_mutex_unlock(&t->mutex);
  }
  return t;
}
#endif // !IS_WINDOWS

void QUICFFI_setOneShotTimer(intptr_t pti, int64_t DueTime)
{
#if IS_WINDOWS
  timer_holder *t = (timer_holder*)pti;
  if (!t->hThread) {
      // Create the thread suspended, so the assignment to t->hThread
      // completes before the threadproc begins to run.
      t->hThread = CreateThread(NULL, 0, TimerProc, t, CREATE_SUSPENDED, NULL);
      SetThreadPriority(t->hThread, THREAD_PRIORITY_ABOVE_NORMAL);
      ResumeThread(t->hThread);
  }
  LARGE_INTEGER liDueTime;
  liDueTime.QuadPart = DueTime;
  if (!SetWaitableTimer(t->hTimer, &liDueTime, 0, NULL, NULL, 0)) {
      printf("SetWaitableTimer failed gle=%d\n", GetLastError());
  }
#else
  if (DueTime < 0) {
    printf("QUICFFI_setOneShotTimer: invalid DueTime\n");
    exit(1);
  }
  timer_holder *t = (timer_holder*)pti;
  pthread_mutex_lock(&t->mutex);
  if (t->t != NoTimer) {
    // This timer is still active.  Interrupt it to change its DueTime.
    t->DueTime = DueTime;
    pthread_cond_signal(&t->cond);
    pthread_mutex_unlock(&t->mutex);
  } else {
    t->t = OneShotTimer;
    t->DueTime = DueTime;
    pthread_mutex_unlock(&t->mutex);
    pthread_create(&t->thread, NULL, OneShotTimerProc, t);
  }
#endif
}

void QUICFFI_cancelTimer(intptr_t pti)
{
#if IS_WINDOWS
  timer_holder *t = (timer_holder*)pti;
  CancelWaitableTimer(t->hTimer);
#else
  timer_holder *t = (timer_holder*)pti;
  pthread_mutex_lock(&t->mutex);
  t->is_cancelled = 1;
  pthread_cond_signal(&t->cond);
  pthread_mutex_unlock(&t->mutex);
  pthread_join(t->thread, NULL);
#endif
}

void QUICFFI_setRepeatingTimer(intptr_t pti, uint32_t msPeriod)
{
#if IS_WINDOWS
  timer_holder *t = (timer_holder*)pti;
  LARGE_INTEGER DueTime;
  DueTime.QuadPart = msPeriod*-10000; // make the time relative to now
  if (!SetWaitableTimer(t->hTimer, &DueTime, msPeriod, NULL, NULL, FALSE)) {
      printf("SetWaitableTimerEx() failed - gle=%d\n", GetLastError());
  }
  if (!t->hThread) {
      // Create the thread suspended, so the assignment to t->hThread
      // completes before the threadproc begins to run.
      t->hThread = CreateThread(NULL, 0, TimerProc, t, CREATE_SUSPENDED, NULL);
      SetThreadPriority(t->hThread, THREAD_PRIORITY_ABOVE_NORMAL);
      ResumeThread(t->hThread);
  }
#else
  timer_holder *t = (timer_holder*)pti;
  if (t->t != NoTimer) {
    printf("setOneShotTimer, but the timer type is already set\n");
    exit(1);
  }
  pthread_mutex_lock(&t->mutex);
  t->t = PeriodicTimer;
  t->msPeriod = msPeriod;
  pthread_mutex_unlock(&t->mutex);
  pthread_create(&t->thread, NULL, PeriodicTimerProc, t);
#endif
}

bool __eq__C_intptr_t(intptr_t x0, intptr_t x1)
{
  return x0==x1;
}


typedef void (*quic_ticket_callback)(QUICTypes_connection *x0, Prims_string x1, QUICTypes_mitls_ticket *x2);

struct native_state {
  QUICTypes_connection *cs;
  quic_ticket_callback cb;
  mipki_state *pki;
  pfn_FFI_nego_cb nego_callback;
};

// Select a certificate based on the given SNI and list of signatures.
// Signature algorithms are represented as 16-bit integers using the TLS 1.3 RFC code points
void* MITLS_CALLCONV CertSelect(void *cb_state, mitls_version ver, const unsigned char *sni, size_t sni_len, const unsigned char *alpn, size_t alpn_len, const mitls_signature_scheme *sigalgs, size_t sigalgs_len, mitls_signature_scheme *selected)
{
  struct native_state *holder = (struct native_state*)cb_state;

  if (ver != TLS_1p3) {
      return NULL;
  }

  return (void*)mipki_select_certificate(holder->pki, sni, sni_len, sigalgs, sigalgs_len, selected);
}

// Write the certificate chain to buffer, returning the number of written bytes.
// The chain should be written by prefixing each certificate by its length encoded over 3 bytes
size_t MITLS_CALLCONV CertFormat(void *cb_state, const void *cert_ptr, unsigned char buffer[MAX_CHAIN_LEN])
{
  struct native_state *holder = (struct native_state*)cb_state;

  return mipki_format_chain(holder->pki, cert_ptr, buffer, MAX_CHAIN_LEN);
}

// Tries to sign and write the signature to sig, returning the signature size or 0 if signature failed
size_t MITLS_CALLCONV CertSign(void *cb_state, const void *cert_ptr, const mitls_signature_scheme sigalg, const unsigned char *tbs, size_t tbs_len, unsigned char *sig)
{
  struct native_state *holder = (struct native_state*)cb_state;
  size_t sig_len = MAX_SIGNATURE_LEN;

  if (mipki_sign_verify(holder->pki, cert_ptr, sigalg, tbs, tbs_len, sig, &sig_len, MIPKI_SIGN)) {
    return sig_len;
  }
  return 0;
}

// Verifies that the chain (given in the same format as above) is valid, and that sig is a valid signature
// of tbs for sigalg using the public key stored in the leaf of the chain.
// N.B. this function must validate the chain (including applcation checks such as hostname matching)
int MITLS_CALLCONV CertVerify(void *cb_state, const unsigned char* chain, size_t chain_len, const mitls_signature_scheme sigalg, const unsigned char *tbs, size_t tbs_len, const unsigned char *sig, size_t sig_len)
{
  struct native_state *holder = (struct native_state*)cb_state;
  
  // make a copy of sig, as mipki_sign_verify requires sig to be non-const.
  unsigned char *sigcopy = (unsigned char*)_alloca(sig_len);
  memcpy(sigcopy, sig, sig_len);

  mipki_chain parsedchain = mipki_parse_chain(holder->pki, chain, chain_len);
  int r = mipki_sign_verify(holder->pki, parsedchain, sigalg, tbs, tbs_len, sigcopy, &sig_len, MIPKI_VERIFY);
  mipki_free_chain(holder->pki, parsedchain);
  return r;
}

// Kremlin type for mitls_ticket doesn't exactly match miTLS's.
void MITLS_CALLCONV quic_ticket_cb(void *cb_state, const char *sni, const mitls_ticket *ticket)
{
  // Make a copy into the heap, so QUICConnection.fst can hold onto it without making its own copy
  struct native_state *holder = (struct native_state*)cb_state;
  QUICTypes_mitls_ticket *t = (QUICTypes_mitls_ticket *)malloc(sizeof(QUICTypes_mitls_ticket));
  t->ticket_len = ticket->ticket_len;
  t->ticket = (char*)ticket->ticket;
  t->session_len = ticket->session_len;
  t->session = (char*)ticket->session;

  (holder->cb)(holder->cs, sni, t);
}

mitls_nego_action MITLS_CALLCONV quic_nego_cb(void *cb_state, mitls_version ver, const unsigned char *exts, size_t exts_len, /*out*/ mitls_extension **custom_exts, /*out*/size_t *custom_exts_len, /*inout*/ unsigned char **cookie, size_t *cookie_len)
{
  struct native_state *holder = (struct native_state*)cb_state;
  
  return (holder->nego_callback)(holder->cs, ver, exts, exts_len, custom_exts, custom_exts_len, cookie, cookie_len);
}

// Kremlin types don't let us precisely match the layout of struct quic_config.  So the QUICFFI
// type approximates it, and we must copy that into a true quic_config before calling miTLS
int32_t QUICFFI_ffi_mitls_quic_create(intptr_t *x0, QUICFFI_quic_config x1)
{
  struct native_state *holder = malloc(sizeof(struct native_state));
  holder->cs = x1.callback_state;
  holder->cb = x1.ticket_callback;
  holder->nego_callback = (pfn_FFI_nego_cb)x1.nego_callback;
  int erridx;

  if (x1.is_server) {
    mipki_config_entry pki_config = {
      .cert_file = "server.crt",
      .key_file = "server.key",
      .is_universal = 1 // ignore SNI
      };

    holder->pki = mipki_init(&pki_config, 1, NULL, &erridx);
  } else {
    holder->pki = mipki_init(NULL, 0, NULL, &erridx);
    mipki_add_root_file_or_path(holder->pki, "CAFile.pem");
  }

  mitls_ticket *ticket;
  if (x1.server_ticket) {
    ticket = malloc(sizeof(mitls_ticket));
    ticket->ticket_len = x1.server_ticket->ticket_len;
    ticket->session_len = x1.server_ticket->session_len;
    ticket->ticket = x1.server_ticket->ticket;
    ticket->session = x1.server_ticket->session;
  } else {
    ticket = NULL;
  }

  mitls_cert_cb cert_callbacks = {
    CertSelect,
    CertFormat,
    CertSign,
    CertVerify
  };
    
  quic_config cfg = {0};
  cfg.is_server = x1.is_server;
  
  cfg.alpn = (const mitls_alpn*)x1.alpn;
  cfg.alpn_count = x1.alpn_count;
  cfg.cipher_suites = x1.cipher_suites;
  cfg.signature_algorithms = x1.signature_algorithms;
  cfg.named_groups = x1.named_groups;
  cfg.enable_0rtt = x1.enable_0rtt;
  
  cfg.host_name = x1.host_name;
  cfg.server_ticket = ticket;
  cfg.exts = (const mitls_extension *)x1.exts; // types are identical but named differently
  cfg.exts_count = x1.exts_count;
  
  cfg.callback_state = holder;
  cfg.ticket_callback = quic_ticket_cb;
  cfg.nego_callback = quic_nego_cb;
  if (x1.cert_callbacks != 0) {
      printf("BUGBUG: F* code should not be providing cert callbacks.  We send these direct to libmipki from C.\n");
      exit(1);
  }
  cfg.cert_callbacks = &cert_callbacks;
  
  cfg.ticket_enc_alg = (const char*)x1.ticket_enc_alg;
  cfg.ticket_key = (const char*)x1.ticket_key;
  cfg.ticket_key_len = x1.ticket_key_len;

  return FFI_mitls_quic_create((quic_state**)x0, &cfg);
}

// Cast from a C type to an opaque value
intptr_t QUICFFI_to_engine_t(QUICTypes_engine *x0)
{
  return (intptr_t)x0;
}

// Cast back from opaque value to C type
QUICTypes_engine *QUICFFI_from_engine_t(intptr_t x0)
{
  return (QUICTypes_engine*)x0;
}

extern QUICTypes_connection *QUICEngine_createServerConnection(QUICTypes_engine *x0, QUICTypes_connectionid_t x1);
QUICTypes_connection *QUICFFI_createServerConnection(QUICTypes_engine *x0, QUICTypes_connectionid_t x1)
{
    return QUICEngine_createServerConnection(x0, x1);
}

// Kremlib's C.fst declares but does not implement this
uint8_t uint8_of_char(char x0)
{
    return (uint8_t)x0;
}

// Kremlib's FStar.String.h declares but does not implement this
extern Prims_string FStar_String_string_of_char(FStar_Char_char x0)
{
    char *str = KRML_HOST_MALLOC(2);
    str[0] = x0;
    str[1] = '\0';
    return str;
}
