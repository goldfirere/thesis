#include <string.h>
#include "primitive-memops.h"

void hsprimitive_memcpy( void *dst, int doff, void *src, int soff, size_t len )
{
  memcpy( (char *)dst + doff, (char *)src + soff, len );
}

void hsprimitive_memmove( void *dst, int doff, void *src, int soff, size_t len )
{
  memmove( (char *)dst + doff, (char *)src + soff, len );
}

#define MEMSET(TYPE, ATYPE)                                                  \
void hsprimitive_memset_ ## TYPE (Hs ## TYPE *p, int off, int n, ATYPE x)    \
{                                                                            \
  p += off;                                                                  \
  if (x == 0)                                                                \
    memset(p, 0, n * sizeof(Hs ## TYPE));                                    \
  else if (sizeof(Hs ## TYPE) == sizeof(int)*2) {                            \
    int *q = (int *)p;                                                       \
    const int *r = (const int *)(void *)&x;                                  \
    while (n>0) {                                                            \
      q[0] = r[0];                                                           \
      q[1] = r[1];                                                           \
      q += 2;                                                                \
      --n;                                                                   \
    }                                                                        \
  }                                                                          \
  else {                                                                     \
    while (n>0) {                                                            \
      *p++ = x;                                                              \
      --n;                                                                   \
    }                                                                        \
  }                                                                          \
}

void hsprimitive_memset_Word8 (HsWord8 *p, int off, int n, HsWord x)
{
  memset( (char *)(p+off), x, n );
}

/* MEMSET(HsWord8, HsWord) */
MEMSET(Word16, HsWord)
MEMSET(Word32, HsWord)
MEMSET(Word64, HsWord64)
MEMSET(Word, HsWord)
MEMSET(Ptr, HsPtr)
MEMSET(Float, HsFloat)
MEMSET(Double, HsDouble)
MEMSET(Char, HsChar)
