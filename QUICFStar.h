// QUICFStar.h - C-side support for Kremlin-extracted code
#pragma once
#define _WIN32_WINNT 0x0600
#include <stdint.h>

// Temporarily support garbage-collected Prims.string.  It it only
// used by printf() for debugging messages.
typedef const char *Prims_string;

#define KRML_NOUINT128 1
typedef const char *C_String_t, *C_String_t_;
int64_t QUICFFI_getSystemTime(void);

#ifdef _MSC_VER
extern void DbgPrint(const char* fmt, ...);
#define KRML_HOST_PRINTF DbgPrint
#endif

// Map F* names for miTLS and libquiccrypto functions into their C names
#if QUIC_KREMLIN
#define QUICFFI_ffi_mitls_init                FFI_mitls_init
#define QUICFFI_ffi_mitls_quic_process        FFI_mitls_quic_process
#define QUICFFI_ffi_mitls_quic_get_exporter   FFI_mitls_quic_get_exporter
#define QUICFFI_ffi_mitls_quic_close          FFI_mitls_quic_close
#define QUICFFI_ffi_mitls_quic_free           FFI_mitls_quic_free
#define QUICFFI_ffi_mitls_find_custom_extension  FFI_mitls_find_custom_extension
#define QUICFFI_ffi_mitls_quic_get_record_key FFI_mitls_quic_get_record_key

#define QUICFFI_quic_derive_initial_secrets   quic_derive_initial_secrets
#define QUICFFI_quic_crypto_derive_key        quic_crypto_derive_key
#define QUICFFI_quic_crypto_tls_derive_secret quic_crypto_tls_derive_secret
#define QUICFFI_quic_crypto_encrypt           quic_crypto_encrypt
#define QUICFFI_quic_crypto_decrypt           quic_crypto_decrypt
#define QUICFFI_quic_crypto_create            quic_crypto_create
#define QUICFFI_quic_crypto_packet_number_otp quic_crypto_packet_number_otp
#endif

char 	*stpcpy(char *__restrict, const char *__restrict);

