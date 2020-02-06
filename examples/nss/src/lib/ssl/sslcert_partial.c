/* -*- Mode: C; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*- */
/*
 * SSL server certificate configuration functions.
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "ssl.h"
#include "sslimpl.h"
#include "secoid.h"   /* for SECOID_GetAlgorithmTag */
#include "pk11func.h" /* for PK11_ReferenceSlot */
#include "nss.h"      /* for NSS_RegisterShutdown */
#include "prinit.h"   /* for PR_CallOnceWithArg */

/* This global item is used only in servers.  It is is initialized by
 * SSL_ConfigSecureServer(), and is used in ssl3_SendCertificateRequest().
 */


/* STUBS */
SECStatus
ssl_SetupCAList(const sslSocket *ss)
{
    return SECSuccess;
}

static struct {
    PRCallOnceType setup;
    CERTDistNames *names;
} ssl_server_ca_list;

int main() {
	return 0;
}

SECStatus
ssl_GetCertificateRequestCAs(const sslSocket *ss, unsigned int *calen,
                             const SECItem **names, unsigned int *nnames)
{
    const SECItem *name;
    const CERTDistNames *ca_list;
    unsigned int i;

    *calen = 0;
    *names = NULL;
    *nnames = 0;

    /* ssl3.ca_list is initialized to NULL, and never changed. */
    ca_list = ss->ssl3.ca_list;
    if (!ca_list) {
        if (ssl_SetupCAList(ss) != SECSuccess) {
            return SECFailure;
        }
        ca_list = ssl_server_ca_list.names;
    }

    if (ca_list != NULL) {
        *names = ca_list->names;
        *nnames = ca_list->nnames;
    }

    for (i = 0, name = *names; i < *nnames; i++, name++) {
        *calen += 2 + name->len;
    }
    return SECSuccess;
}



const sslServerCert *
ssl_FindServerCert(const sslSocket *ss, SSLAuthType authType,
                   const sslNamedGroupDef *namedCurve)
{
    PRCList *cursor;

    for (cursor = PR_NEXT_LINK(&ss->serverCerts);
         cursor != &ss->serverCerts;
         cursor = PR_NEXT_LINK(cursor)) {
        sslServerCert *cert = (sslServerCert *)cursor;
        if (!SSL_CERT_IS(cert, authType)) {
            continue;
        }
        if (SSL_CERT_IS_EC(cert)) {
            /* Note: For deprecated APIs, we need to be able to find and
               match a slot with any named curve. */
            if (namedCurve && cert->namedCurve != namedCurve) {
                continue;
            }
        }
        return cert;
    }
    return NULL;
}

