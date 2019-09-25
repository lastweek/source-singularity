//////////////////////////////////////////////////////////////////////////////
//
//  Abstract:   Implementation of Template CHashTable64<> and class CHashTable64PVOID.
//
//  NOTE: The keys 0 and ~0 are both reserved for internal use.
//

#pragma once

#include <winlean.h>
#include "hashtab.h"

//////////////////////////////////////////////////////////////////////////////
#undef EMPTY
#undef DELETED
#define EMPTY       0
#define DELETED     ~0u

CHashTable32PVOID::CHashTable32PVOID()
{
    m_pTable = NULL;
    m_nSize = 0;
    m_nValid = 0;
}

CHashTable32PVOID::CHashTable32PVOID(INT nInitialSize)
{
    m_pTable = NULL;
    m_nSize = 0;
    m_nValid = 0;
    Resize(nInitialSize);
}

CHashTable32PVOID::~CHashTable32PVOID()
{
    if (m_pTable) {
        delete[] m_pTable;
        m_pTable = NULL;
    }
    m_nSize = 0;
    m_nValid = 0;
}

CHashTable32PVOID::Entry * CHashTable32PVOID::FindEntry(UINT32 key)
{
    if (key == EMPTY || key == DELETED || m_nSize <= 0) {
        return NULL;
    }

    INT offset = Offset(key);
    INT orig_offset = offset;

    for (;;) {
        if (m_pTable[offset].key == EMPTY) {
            break;                                      // EMPTY, stop.
        }
        else if (m_pTable[offset].key == key) {         // Match, return TRUE
            if (offset != orig_offset) {                // Increase locality.
                Swap(m_pTable[offset], m_pTable[orig_offset]);
                offset = orig_offset;
            }
            return &m_pTable[offset];
        }
        else {                                          // Not, try next bucket.
            offset = (offset + 1) % m_nSize;
        }
    }
    return NULL;
}

PVOID CHashTable32PVOID::Find(UINT32 key)
{
    Entry *pEntry = FindEntry(key);
    return pEntry ? pEntry->value : NULL;
}

BOOL CHashTable32PVOID::Change(UINT32 key, PVOID value)
{
    Entry *pEntry = FindEntry(key);
    if (pEntry) {
        pEntry->value = value;
        return TRUE;
    }
    return Insert(key, value);
}

BOOL CHashTable32PVOID::Insert(UINT32 key, PVOID value)
{
    if (key == EMPTY || key == DELETED) {
        return FALSE;
    }

    if ((m_nValid + 1) > (m_nSize / 2)) {               // Table is never > 1/2 full!
        if (m_nSize == 0) {
            if (!Resize(32))
                return FALSE;
        }
        else {
            if (!Resize(m_nSize * 2))
                return FALSE;
        }
    }

    INT offset = Offset(key);

    for (;;) {
        if (m_pTable[offset].key == EMPTY || m_pTable[offset].key == DELETED) {
            // EMPTY, Insert
            m_pTable[offset].key = key;
            m_pTable[offset].value = value;
            m_nValid++;
            return TRUE;
        }
        else {                                          // Not, try next bucket.
            offset = (offset + 1) % m_nSize;
        }
    }
    // return FALSE;
}

BOOL CHashTable32PVOID::Delete(UINT32 key)
{
    if (key == EMPTY || key == DELETED) {
        return FALSE;
    }

    if (m_nSize == 0) {
        return FALSE;
    }

    INT offset = Offset(key);

    // First, find the value.
    for (;;) {
        if (m_pTable[offset].key == EMPTY) {            // EMPTY, stop.
            return FALSE;
        }
        else if (m_pTable[offset].key == key) {         // Match, return TRUE
            m_pTable[offset].key = DELETED;
            m_pTable[offset].value = 0;
            m_nValid--;
            return TRUE;
        }
        else {                                          // Not, try next bucket.
            offset = (offset + 1) % m_nSize;
        }
    }
    // return FALSE;
}

BOOL CHashTable32PVOID::Resize(INT nNewSize)
{
    Entry *pOldTable = m_pTable;
    INT nOldSize = m_nSize;

    m_pTable = new Entry[nNewSize];
    if (m_pTable == NULL) {
        return FALSE;
    }

    for (INT i = 0; i < nNewSize; i++) {
        m_pTable[i].key = EMPTY;
        m_pTable[i].value = 0;
    }

    m_nSize = nNewSize;
    m_nValid = 0;

    if (pOldTable) {
        for (INT i = 0; i < nOldSize; i++) {
            if (pOldTable[i].key != EMPTY && pOldTable[i].key != DELETED) {
                Insert(pOldTable[i].key, pOldTable[i].value);
            }
        }
        delete[] pOldTable;
        pOldTable = NULL;
    }

    return TRUE;
}

PVOID CHashTable32PVOID::Enumerate(UINT32& key, INT& nIterator)
{
    for (; (INT)nIterator < m_nSize; nIterator++) {
        if (m_pTable[nIterator].key == EMPTY ||
            m_pTable[nIterator].key == DELETED) {
            continue;
        }

        key = m_pTable[nIterator].key;
        return m_pTable[nIterator++].value;
    }

    key = EMPTY;
    nIterator = 0;
    return NULL;
}

//////////////////////////////////////////////////////////////////////////////

#undef EMPTY
#undef DELETED
#define EMPTY       0
#define DELETED     ~0uI64

CHashTable64PVOID::CHashTable64PVOID()
{
    m_pTable = NULL;
    m_nSize = 0;
    m_nValid = 0;
}

CHashTable64PVOID::CHashTable64PVOID(INT nInitialSize)
{
    m_pTable = NULL;
    m_nSize = 0;
    m_nValid = 0;
    Resize(nInitialSize);
}

CHashTable64PVOID::~CHashTable64PVOID()
{
    if (m_pTable) {
        delete[] m_pTable;
        m_pTable = NULL;
    }
    m_nSize = 0;
    m_nValid = 0;
}

CHashTable64PVOID::Entry * CHashTable64PVOID::FindEntry(UINT64 key)
{
    if (key == EMPTY || key == DELETED || m_nSize <= 0) {
        return NULL;
    }

    INT offset = Offset(key);
    INT orig_offset = offset;

    for (;;) {
        if (m_pTable[offset].key == EMPTY) {
            break;                                      // EMPTY, stop.
        }
        else if (m_pTable[offset].key == key) {         // Match, return TRUE
            if (offset != orig_offset) {                // Increase locality.
                Swap(m_pTable[offset], m_pTable[orig_offset]);
                offset = orig_offset;
            }
            return &m_pTable[offset];
        }
        else {                                          // Not, try next bucket.
            offset = (offset + 1) % m_nSize;
        }
    }
    return NULL;
}

PVOID CHashTable64PVOID::Find(UINT64 key)
{
    Entry *pEntry = FindEntry(key);
    return pEntry ? pEntry->value : NULL;
}

BOOL CHashTable64PVOID::Change(UINT64 key, PVOID value)
{
    Entry *pEntry = FindEntry(key);
    if (pEntry) {
        pEntry->value = value;
        return TRUE;
    }
    return Insert(key, value);
}

BOOL CHashTable64PVOID::Insert(UINT64 key, PVOID value)
{
    if (key == EMPTY || key == DELETED) {
        return FALSE;
    }

    if ((m_nValid + 1) > (m_nSize / 2)) {               // Table is never > 1/2 full!
        if (m_nSize == 0) {
            if (!Resize(32))
                return FALSE;
        }
        else {
            if (!Resize(m_nSize * 2))
                return FALSE;
        }
    }

    INT offset = Offset(key);

    for (;;) {

        if (m_pTable[offset].key == EMPTY || m_pTable[offset].key == DELETED) {
            // EMPTY, Insert
            m_pTable[offset].key = key;
            m_pTable[offset].value = value;
            m_nValid++;
            return TRUE;
        }
        else {                                          // Not, try next bucket.
            offset = (offset + 1) % m_nSize;
        }
    }
    // return FALSE;
}

BOOL CHashTable64PVOID::Delete(UINT64 key)
{
    if (key == EMPTY || key == DELETED) {
        return FALSE;
    }

    if (m_nSize == 0) {
        return FALSE;
    }

    INT offset = Offset(key);

    // First, find the value.
    for (;;) {
        if (m_pTable[offset].key == EMPTY) {            // EMPTY, stop.
            return FALSE;
        }
        else if (m_pTable[offset].key == key) {         // Match, return TRUE
            m_pTable[offset].key = DELETED;
            m_pTable[offset].value = 0;
            m_nValid--;
            return TRUE;
        }
        else {                                          // Not, try next bucket.
            offset = (offset + 1) % m_nSize;
        }
    }
    // return FALSE;
}

BOOL CHashTable64PVOID::Resize(INT nNewSize)
{
    Entry *pOldTable = m_pTable;
    INT nOldSize = m_nSize;

    m_pTable = new Entry[nNewSize];
    if (m_pTable == NULL) {
        return FALSE;
    }

    for (INT i = 0; i < nNewSize; i++) {
        m_pTable[i].key = EMPTY;
        m_pTable[i].value = 0;
    }

    m_nSize = nNewSize;
    m_nValid = 0;

    if (pOldTable) {
        for (INT i = 0; i < nOldSize; i++) {
            if (pOldTable[i].key != EMPTY && pOldTable[i].key != DELETED) {
                Insert(pOldTable[i].key, pOldTable[i].value);
            }
        }
        delete[] pOldTable;
        pOldTable = NULL;
    }

    return TRUE;
}

PVOID CHashTable64PVOID::Enumerate(UINT64& key, INT& nIterator)
{
    for (; (INT)nIterator < m_nSize; nIterator++) {
        if (m_pTable[nIterator].key == EMPTY ||
            m_pTable[nIterator].key == DELETED) {
            continue;
        }

        key = m_pTable[nIterator].key;
        return m_pTable[nIterator++].value;
    }

    key = EMPTY;
    nIterator = 0;
    return NULL;
}
//
///////////////////////////////////////////////////////////////// End of File.
