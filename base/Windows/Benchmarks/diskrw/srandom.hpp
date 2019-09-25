#include <assert.h>
#include <stdio.h>

#ifdef HAVE_INTTYPES_H
#include <inttypes.h>
#elif HAVE_STDINT_H
#include <stdint.h>
#else
typedef int                int32_t;
typedef unsigned int       uint32_t;
typedef unsigned long long uint64_t;
#endif

#define static_assert(x)  switch(x) case 0: case (x):

class SRandom
{
    static const uint64_t m = 2147483647;
    static const uint64_t a = 16807;
    static const uint32_t zero = 0x23456789;
    uint32_t last;
  public:
    static const int32_t Maximum = 0x7fffffff;

  public:
  inline SRandom() : last (zero) {}

  inline void reset() { last = zero; }

  inline uint32_t next()
    {
        static_assert(sizeof(uint64_t) == 8);
        static_assert(sizeof(uint32_t) == 4);
        static_assert(sizeof(int32_t) == 4);
        uint64_t tmp = (a * last) % m;
        last = (uint32_t) tmp;
        return ((int)last) & Maximum;
    }

  inline static void check()
    {
        static const int test_iterations = 10000000;
        SRandom r;
        int32_t hash = 0;
        for (int i = 0; i < test_iterations; i++)
        {
            int32_t n = r.next();
            assert(n != 0);
            hash ^= n;
        }
        fprintf(stderr, "xor sum 1...%d = %u\n", test_iterations, hash);
        assert(hash == 1080076236);
    }
};

