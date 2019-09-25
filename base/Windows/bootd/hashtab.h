//////////////////////////////////////////////////////////////////////////////
//
//  Abstract:   Definition of Template CHashTable32<> and class CHashTable32PVOID.
//
//  NOTE: The keys 0 and ~0 are both reserved for internal use.
//

#pragma once

//////////////////////////////////////////////////////////////// Base Classes.
//
class CHashTable32PVOID
{
  public:
    CHashTable32PVOID();
    CHashTable32PVOID(INT nInitialSize);
    ~CHashTable32PVOID();

    BOOL    Insert(UINT32 key, PVOID value);
    BOOL    Change(UINT32 key, PVOID value);
    BOOL    Delete(UINT32 key);

    PVOID   Find(UINT32 key);
    PVOID   Enumerate(UINT32& key, INT& nIterator);

    INT     Count(void) { return m_nValid; }

  protected:
    struct Entry
    {
        UINT32  key;
        PVOID   value;
    };

    INT     Offset(UINT32 key) { return (INT)((key*1000000007L)%m_nSize); }
    VOID    Swap(Entry& a, Entry& b) { Entry t = a; a = b; b = t; }
    BOOL    Resize(INT nNewSize);
    Entry * FindEntry(UINT32 key);

  protected:
    Entry * m_pTable;
    INT     m_nSize;
    INT     m_nValid;
};

class CHashTable64PVOID
{
  public:
    CHashTable64PVOID();
    CHashTable64PVOID(INT nInitialSize);
    ~CHashTable64PVOID();

    BOOL    Insert(UINT64 key, PVOID value);
    BOOL    Change(UINT64 key, PVOID value);
    BOOL    Delete(UINT64 key);

    PVOID   Find(UINT64 key);
    PVOID   Enumerate(UINT64& key, INT& nIterator);

    INT     Count(void) { return m_nValid; }

  protected:
    struct Entry
    {
        UINT64  key;
        PVOID   value;
    };

    INT     Offset(UINT64 key) { return (INT)((key*1000000007UL)%m_nSize); }
    VOID    Swap(Entry& a, Entry& b) { Entry t = a; a = b; b = t; }
    BOOL    Resize(INT nNewSize);
    Entry * FindEntry(UINT64 key);

  protected:
    Entry * m_pTable;
    INT     m_nSize;
    INT     m_nValid;
};

/////////////////////////////////////////////////////////////////// Templates.
//
template<class T> class CHashTable32 : public CHashTable32PVOID
{
  public:
    CHashTable32()
        : CHashTable32PVOID() {}
    CHashTable32(INT nInitialSize)
        : CHashTable32PVOID(nInitializeSize) {}

    BOOL Insert(UINT32 key, T value)
    { return CHashTable32PVOID::Insert(key, (PVOID)value); }

    BOOL Change(UINT32 key, T value)
    { return CHashTable32PVOID::Change(key, (PVOID)value); }

    T Find(UINT32 key)
    { return (T)CHashTable32PVOID::Find(key); }

    T Enumerate(UINT32& key, INT& nIterator)
    { return (T)CHashTable32PVOID::Enumerate(key, nIterator); }
};

template<class T> class CHashTable64 : public CHashTable64PVOID
{
  public:
    CHashTable64()
        : CHashTable64PVOID() {}
    CHashTable64(INT nInitialSize)
        : CHashTable64PVOID(nInitializeSize) {}

    BOOL Insert(UINT64 key, T value)
    { return CHashTable64PVOID::Insert(key, (PVOID)value); }

    BOOL Change(UINT64 key, T value)
    { return CHashTable64PVOID::Change(key, (PVOID)value); }

    T Find(UINT64 key)
    { return (T)CHashTable64PVOID::Find(key); }

    T Enumerate(UINT64& key, INT& nIterator)
    { return (T)CHashTable64PVOID::Enumerate(key, nIterator); }
};
//
///////////////////////////////////////////////////////////////// End of File.
