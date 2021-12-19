/*
Wojciech Adamiec, 310064
I am the author of this code.
All exception from this statement are marked in comments.
*/

/*
Short story of my malloc:

TODO
*/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define debug(...) // printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

#define FREE 0
#define ALLOCATED 1

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))
#define PACK_WITH_PREV(size, alloc, prev) ((size) | (alloc) | ((prev) << 1))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_BYTES(p) (*(unsigned int *)(p))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PREV_ALLOC(p) ((GET(p) & 0x2) >> 1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

static char *heap_listp;
static size_t last_prev_alloc = 1;

static void set_prev_alloc(void *bp, size_t prev_allloc) {
  size_t size = GET_SIZE(HDRP(bp));
  size_t alloc = GET_ALLOC(HDRP(bp));
  PUT(HDRP(bp), PACK_WITH_PREV(size, alloc, prev_allloc));
}

static void *coalesce(void *bp) {
  // printf("Coalesce pointer=%p\n", bp);

  size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc) { /* Case 1 */
    set_prev_alloc(NEXT_BLKP(bp), FREE);
    // printf("Coalesce without merge\n");
    return bp;
  }

  else if (prev_alloc && !next_alloc) { /* Case 2 */
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    // printf("Coalesce with next merge\n");
    return bp;
  }

  else if (!prev_alloc && next_alloc) { /* Case 3 */
    set_prev_alloc(NEXT_BLKP(bp), FREE);
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
    // printf("Coalesce with prev merge\n");
  }

  else { /* Case 4 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
    // printf("Coalesce with full merge\n");
  }
  return bp;
}

static void *extend_heap(size_t words) {

  // printf("Extent_heap: words=%li\n", words);
  char *bp;
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  // printf("Extent_heap: bytes=%li\n", size);
  if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;

  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK_WITH_PREV(size, 0, last_prev_alloc));
  PUT(FTRP(bp), PACK_WITH_PREV(size, 0, last_prev_alloc));
  PUT(HDRP(NEXT_BLKP(bp)), PACK_WITH_PREV(0, 1, 0));

  // printf("Epilogue header pointer=%p\n", HDRP(NEXT_BLKP(bp)));
  /* Coalesce if the previous block was free */
  // printf("Heap size=%li, Heap start=%p, Heap end=%p\n", mem_heapsize(),
  // mem_heap_lo(), mem_heap_hi());
  return coalesce(bp);
}

static void *find_fit(size_t asize) {
  /* First-fit search */

  void *bp;

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
      // printf("Find_fit success pointer=%p\n", bp);
      return bp;
    }
  }

  last_prev_alloc = GET_PREV_ALLOC(HDRP(bp));
  // printf("Find_fit fail. Last_prev_alloc=%li\n", last_prev_alloc);
  return NULL; /* No fit */
}

static void place(void *bp, size_t asize) {
  // printf("Place pointer=%p, asize=%li\n", bp, asize);
  size_t csize = GET_SIZE(HDRP(bp));

  if ((csize - asize) >= (ALIGNMENT)) {
    PUT(HDRP(bp), PACK_WITH_PREV(asize, 1, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK_WITH_PREV(csize - asize, 0, 1));
    PUT(FTRP(bp), PACK_WITH_PREV(csize - asize, 0, 1));
    // printf("Place with split, next bp=%p\n", bp);
  } else {
    PUT(HDRP(bp), PACK_WITH_PREV(csize, 1, 1));
    set_prev_alloc(NEXT_BLKP(bp), ALLOCATED);
    // printf("Place without split\n");
  }
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
  // printf("Init\n");

  last_prev_alloc = 1;
  /* Pad heap start so first payload is at ALIGNMENT. */
  if ((heap_listp = mem_sbrk(ALIGNMENT)) == (void *)-1)
    return -1;

  PUT(heap_listp, 0);                            /* Alignment padding */
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
  PUT(heap_listp + (3 * WSIZE), PACK_WITH_PREV(0, 1, 1)); /* Epilogue header */

  // printf("Init first 4 bytes=%i\n", GET_BYTES(heap_listp));
  // printf("Init second 4 bytes=%i\n", GET_BYTES(heap_listp + (1 * WSIZE)));
  // printf("Init third 4 bytes=%i\n", GET_BYTES(heap_listp + (2 * WSIZE)));
  // printf("Init fourth 4 bytes=%i\n", GET_BYTES(heap_listp + (3 * WSIZE)));
  heap_listp += (2 * WSIZE);

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    return -1;

  return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size) {
  // printf("Malloc size=%li\n", size);

  size_t asize;      /* Adjusted block size */
  size_t extendsize; /* Amount to extend heap if no fit */
  char *bp;

  /* Ignore spurious requests */
  if (size == 0)
    return NULL;

  /* Adjust block size to include overhead and alignment reqs. */
  if (size <= DSIZE)
    asize = ALIGNMENT;
  else
    asize = ALIGNMENT * (((size + WSIZE - 1) / ALIGNMENT) + 1);

  /* Search the free list for a fit */
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    return NULL;
  place(bp, asize);
  return bp;
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *bp) {
  // printf("Free pointer=%p\n", bp);

  if (bp == NULL)
    return;

  size_t size = GET_SIZE(HDRP(bp));

  size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
  PUT(HDRP(bp), PACK_WITH_PREV(size, 0, prev_alloc));
  PUT(FTRP(bp), PACK_WITH_PREV(size, 0, prev_alloc));
  coalesce(bp);
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.
 **/
void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */

  // printf("Realloc old_pointer=%p, size=%li\n", old_ptr, size);

  if (size == 0) {
    // printf("Realloc size=0\n");
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr) {
    // printf("Realloc !old_ptr\n");
    return malloc(size);
  }

  size_t asize;

  if (size <= DSIZE)
    asize = ALIGNMENT;
  else
    asize = ALIGNMENT * (((size + WSIZE - 1) / ALIGNMENT) + 1);

  size_t old_size = GET_SIZE(HDRP(old_ptr));

  /* If old_size is much bigger than current size we make a split */

  if (old_size >= ALIGNMENT + asize) {
    // printf("Realloc old_size - asize >= ALIGNMENT, asize=%li,
    // old_size=%li\n", asize, old_size);
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(old_ptr));
    PUT(HDRP(old_ptr), PACK_WITH_PREV(asize, ALLOCATED, prev_alloc));
    char *bp = NEXT_BLKP(old_ptr);
    PUT(HDRP(bp), PACK_WITH_PREV(old_size - asize, FREE, ALLOCATED));
    PUT(FTRP(bp), PACK_WITH_PREV(old_size - asize, FREE, ALLOCATED));
    coalesce(bp);
    return old_ptr;
  }

  /* If old_size is slightly bigger than current size we do nothing */
  else if (old_size >= asize) {
    // printf("Realloc old_size - asize >= 0\n");
    return old_ptr;
  }

  /* If new_size is bigger than old one we try to do a merge with next block */
  else if (GET_ALLOC(HDRP(NEXT_BLKP(old_ptr))) == FREE) {
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(old_ptr)));

    // printf("Realloc next block is FREE, next_size=%li\n", next_size);
    /* We do merge with split if possible */
    if (old_size + next_size >= ALIGNMENT + asize) {
      size_t prev_alloc = GET_PREV_ALLOC(HDRP(old_ptr));
      PUT(HDRP(old_ptr), PACK_WITH_PREV(asize, ALLOCATED, prev_alloc));
      // printf("Realloc split merge old_ptr=%p, asize=%li\n", old_ptr, asize);
      char *bp = NEXT_BLKP(old_ptr);
      // printf("Realloc split merge next_ptr=%p, size=%li\n", bp, old_size +
      // next_size - asize);
      PUT(HDRP(bp),
          PACK_WITH_PREV(old_size + next_size - asize, FREE, ALLOCATED));
      PUT(FTRP(bp),
          PACK_WITH_PREV(old_size + next_size - asize, FREE, ALLOCATED));
      return old_ptr;
    }

    /* Simple merge */
    else if (old_size + next_size >= asize) {
      // printf("Realloc simple merge\n");
      size_t prev_alloc = GET_PREV_ALLOC(HDRP(old_ptr));
      PUT(HDRP(old_ptr),
          PACK_WITH_PREV(old_size + next_size, ALLOCATED, prev_alloc));
      set_prev_alloc(NEXT_BLKP(old_ptr), ALLOCATED);
      return old_ptr;
    }
  }

  // printf("Realloc copy\n");
  /* If we cannot perform anything special we just make a alloc a new block and
   * copy data */
  void *new_ptr = malloc(size);

  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  memcpy(new_ptr, old_ptr, old_size);

  /* Free the old block. */
  free(old_ptr);

  return new_ptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

/*
 * mm_checkheap - So simple, it doesn't need a checker!
 */
void mm_checkheap(int verbose) {
  printf("Checkheap!\n");
  void *bp;
  int i = 0;

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    size_t hd_alloc = GET_ALLOC(HDRP(bp));
    size_t hd_prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    size_t ft_alloc = GET_ALLOC(FTRP(bp));
    size_t ft_prev_alloc = GET_PREV_ALLOC(FTRP(bp));

    char *s_hd_alloc = (hd_alloc) ? "ALLOC" : "FREE";
    char *s_ft_alloc = (ft_alloc) ? "ALLOC" : "FREE";
    char *s_hd_prev_alloc = (hd_prev_alloc) ? "PREV_ALLOC" : "PREV_FREE";
    char *s_ft_prev_alloc = (ft_prev_alloc) ? "PREV_ALLOC" : "PREV_FREE";

    if (hd_alloc == ALLOCATED) {
      printf("[%i] HEAD: %p size: %i %s %s\n", i, HDRP(bp), GET_SIZE(HDRP(bp)),
             s_hd_alloc, s_hd_prev_alloc);
      printf("[%i] DEAD FOOTER\n", i);
    }

    else if (hd_alloc == FREE) {
      printf("[%i] HEAD: %p size: %i %s %s\n", i, HDRP(bp), GET_SIZE(HDRP(bp)),
             s_hd_alloc, s_hd_prev_alloc);
      printf("[%i] FOOT: %p size: %i %s %s\n", i, FTRP(bp), GET_SIZE(FTRP(bp)),
             s_ft_alloc, s_ft_prev_alloc);
    }

    i++;
  }
  return;
}