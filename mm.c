/*
Wojciech Adamiec, 310064
I am the author of this code,
except for parts copied and modified from CSAPP.
Those parts inlude: Majority of macros, coalesce, malloc,
init, free, extend_heap, place, find_fit.
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
#define WSIZE 4            /* Word and header/footer size (bytes) */
#define DSIZE 8            /* Double word size (bytes) */
#define CHUNKSIZE (1 << 6) /* Extend heap by this amount (bytes) */

#define FREE 0
#define ALLOCATED 1

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_BYTES(p) (*(unsigned int *)(p))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PREV_ALLOC(p) ((GET(p) & 0x2) >> 1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of its next and prev pointers offsets */
#define NEXT_P(bp) ((char *)(bp))
#define PREV_P(bp) ((char *)(bp) + WSIZE)

/* Read and write pointers from free block */
#define GET_P(p) mem_heap_lo() + GET(p)
#define PUT_P(p, val) *(unsigned int *)(p) = val - mem_heap_lo()

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))


static void printf_heap();
static char *heap_listp;
static size_t last_prev_alloc = 1;
static void *sentinel_pointer;


// Given block ptr compute address of next free block in list
static inline void* get_next_free_blkp(void* bp){
  return GET_P(NEXT_P(bp));
}

// Given block ptr compute address of prev free block in list
static inline void* get_prev_free_blkp(void* bp){
  return GET_P(PREV_P(bp));
}

// Set next free blkp value in bp to value
static inline void set_next_free_blkp(void* bp, void* value){
  PUT_P(NEXT_P(bp), value);
}

// Set prev free blkp value in bp to value
static inline void set_prev_free_blkp(void* bp, void* value){
  PUT_P(PREV_P(bp), value);
}

// Pack a size and allocated bit into a word
static inline unsigned int pack(size_t size, size_t alloc, size_t prev_alloc) {
  return size | alloc | (prev_alloc << 1);
}

// Make a free block
static inline void make_free_block(void *address, size_t size, size_t prev_alloc){
  PUT(HDRP(address), pack(size, FREE, prev_alloc)); // Header
  PUT(FTRP(address), pack(size, FREE, prev_alloc)); // Footer
}

// Make an allocated block
static inline void make_allocated_block(void* address, size_t size, size_t prev_alloc){
  PUT(HDRP(address), pack(size, ALLOCATED, prev_alloc)); // Header
}

// Make a sentinel block
static inline void make_sentinel_block(void* address){
  PUT(HDRP(address), pack(4 * WSIZE, FREE, ALLOCATED));  // Sentinel header
  PUT_P(NEXT_P(address), address);                       // Sentinel next_ptr
  PUT_P(PREV_P(address), address);                       // Sentinel prev_ptr
  PUT(FTRP(address), pack(4 * WSIZE, FREE, ALLOCATED));  // Sentinel footer
}

// Make a prologue block
static inline void make_prologue_block(void* address){
  PUT(HDRP(address), pack(DSIZE, ALLOCATED, ALLOCATED));      // Prologue header
}

// Make an epilogue block
static inline void make_epilogue_block(void* address, size_t prev_alloc){
  PUT(HDRP(address), pack(0, ALLOCATED, prev_alloc));         // Epilogue header
}

// Set prev_alloc value a for given block
static inline void set_prev_alloc(void *bp, size_t prev_allloc) {
  size_t size = GET_SIZE(HDRP(bp));
  size_t alloc = GET_ALLOC(HDRP(bp));
  PUT(HDRP(bp), pack(size, alloc, prev_allloc));
}

// Check if given block is last in heap
static inline bool is_block_last(void *bp) {
  return GET_SIZE(HDRP(NEXT_BLKP(bp))) == 0;
}

// Get a proper size for heap extension
static inline size_t get_extendsize(size_t size) {
  return MAX(size, CHUNKSIZE) / WSIZE;
}

// Adjust block size to include overhead and alignment reqs
static inline size_t get_adjusted_size(size_t size) {
  size_t asize;
  if (size <= DSIZE)
    asize = ALIGNMENT;
  else
    asize = ALIGNMENT * (((size + WSIZE - 1) / ALIGNMENT) + 1);
  return asize;
}

// Add block to free block list
static inline void add_block_to_free_list(void* new){
  // printf("Adding block %p to free block list\n", new);
  set_next_free_blkp(new, get_next_free_blkp(sentinel_pointer));
  set_prev_free_blkp(new, sentinel_pointer);
  set_next_free_blkp(sentinel_pointer, new);
  set_prev_free_blkp(get_next_free_blkp(new), new);
  // printf("Adding ended!\n");
}

// Add block to free block list
static inline void remove_block_from_free_list(void* rem){
  // printf("Reming block %p from free block list\n", rem);
  set_next_free_blkp(get_prev_free_blkp(rem), get_next_free_blkp(rem));
  set_prev_free_blkp(get_next_free_blkp(rem), get_prev_free_blkp(rem));
  // printf("Removing ended!\n");
}

// Try to merge a given free block with adjacent ones
static void *coalesce(void *bp) {
  // printf("Coalesce pointer=%p\n", bp);

  size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  // No merge
  if (prev_alloc && next_alloc) {
    set_prev_alloc(NEXT_BLKP(bp), FREE);
    // printf("Coalesce without merge\n");
  }

  // Merge with next block
  else if (prev_alloc && !next_alloc) {
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    remove_block_from_free_list(NEXT_BLKP(bp));
    make_free_block(bp, size, prev_alloc);
    // printf("Coalesce with next merge\n");
  }

  // Merge with previous block
  else if (!prev_alloc && next_alloc) {
    set_prev_alloc(NEXT_BLKP(bp), FREE);
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    size_t prevblk_prev_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
    remove_block_from_free_list(PREV_BLKP(bp));
    make_free_block(PREV_BLKP(bp), size, prevblk_prev_alloc);
    bp = PREV_BLKP(bp);
    // printf("Coalesce with prev merge\n");
  }

  // Full merge
  else {
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    size_t prevblk_prev_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
    remove_block_from_free_list(PREV_BLKP(bp));
    remove_block_from_free_list(NEXT_BLKP(bp));
    make_free_block(PREV_BLKP(bp), size, prevblk_prev_alloc);
    bp = PREV_BLKP(bp);
    // printf("Coalesce with full merge\n");
  }
  add_block_to_free_list(bp);
  return bp;
}

// Make available heap segment bigger
static void *extend_heap(size_t words) {

  // printf("Extent_heap: words=%li\n", words);
  char *bp;
  size_t size;

  // Allocate an even number of words to maintain alignment
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  // printf("Extent_heap: bytes=%li\n", size);
  // printf("Heap size=%li, Heap start=%p, Heap end=%p\n", mem_heapsize(), mem_heap_lo(), mem_heap_hi());
  if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;

  // Initialize new free block header/footer and the epilogue header
  make_free_block(bp, size, last_prev_alloc);
  make_epilogue_block(NEXT_BLKP(bp), FREE);

  // printf("Epilogue header pointer=%p\n", HDRP(NEXT_BLKP(bp)));
  // printf("Heap size=%li, Heap start=%p, Heap end=%p\n", mem_heapsize(), mem_heap_lo(), mem_heap_hi());

  // Check for merge with adjacent blocks
  return coalesce(bp);
}

// Fint first valid free block in heap
static void *find_fit(size_t asize) {

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

// Place new allocated block at the place of a free one
static void place(void *bp, size_t asize) {
  // printf("Place pointer=%p, asize=%li\n", bp, asize);
  size_t csize = GET_SIZE(HDRP(bp));

  remove_block_from_free_list(bp);

  // If free block is big enough make a split
  if (csize >= ALIGNMENT + asize) {
    make_allocated_block(bp, asize, ALLOCATED);
    bp = NEXT_BLKP(bp);
    // printf("Placed with split, next bp=%p\n", bp);
    make_free_block(bp, csize - asize, ALLOCATED);
    add_block_to_free_list(bp);
  } else {
    // printf("Place without split\n");
    make_allocated_block(bp, csize, ALLOCATED);
    set_prev_alloc(NEXT_BLKP(bp), ALLOCATED);
  }
}

// mm_init - Called when a new trace starts.
int mm_init(void) {
  // printf("Init\n");

  last_prev_alloc = 1;  
  sentinel_pointer = mem_heap_lo() + 2 * WSIZE;

  if ((heap_listp = mem_sbrk(2 * ALIGNMENT)) == (void *)-1)
    return -1;

  PUT(heap_listp, 0);                                     // Alignment padding
  make_sentinel_block(heap_listp + 2 * WSIZE);            // Sentinel block
  make_prologue_block(heap_listp + 6 * WSIZE);            // Prologue header
  make_epilogue_block(heap_listp + 8 * WSIZE, ALLOCATED); // Epilogue header    

  heap_listp += (6 * WSIZE);

  // Extend the empty heap with a free block of CHUNKSIZE bytes
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    return -1;

  return 0;
}

// malloc - Allocate a block of a given size
void *malloc(size_t size) {
  // printf("Malloc size=%li\n", size);

  char *bp;

  // Ignore spurious requests
  if (size == 0)
    return NULL;

  // Adjust block size to include overhead and alignment reqs
  size_t asize = get_adjusted_size(size);

  // Search the free list for a fit
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  // No fit found. Get more memory and place the block */
  size_t extendsize = get_extendsize(asize);
  if ((bp = extend_heap(extendsize)) == NULL)
    return NULL;
  place(bp, asize);
  return bp;
}

// free - make block available for next allocations
void free(void *bp) {
  // printf("Free pointer=%p\n", bp);

  if (bp == NULL)
    return;

  size_t size = GET_SIZE(HDRP(bp));
  size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));

  // Make the block free
  make_free_block(bp, size, prev_alloc);

  // Check for merge with adjacent blocks
  coalesce(bp);
}

// realloc - Change the size of an allocated block
void *realloc(void *old_ptr, size_t size) {
  // printf("Realloc old_pointer=%p, size=%li\n", old_ptr, size);

  // If new size is 0 - just free block
  if (size == 0) {
    // printf("Realloc size=0\n");
    free(old_ptr);
    return NULL;
  }

  // If old_ptr is NULL, then this is just malloc
  if (!old_ptr) {
    // printf("Realloc !old_ptr\n");
    return malloc(size);
  }

  // Adjust block size to include overhead and alignment reqs
  size_t asize = get_adjusted_size(size);
  size_t old_size = GET_SIZE(HDRP(old_ptr));

  // If old_size is much bigger than current size we make a split
  if (old_size >= ALIGNMENT + asize) {
    // printf("Realloc old_size - asize >= ALIGNMENT, asize=%li, old_size=%li\n", asize, old_size);
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(old_ptr));
    make_allocated_block(old_ptr, asize, prev_alloc);
    char *bp = NEXT_BLKP(old_ptr);
    make_free_block(bp, old_size - asize, ALLOCATED);
    coalesce(bp);
    return old_ptr;
  }

  // If old_size is slightly bigger than current size we do nothing
  if (old_size >= asize) {
    // printf("Realloc old_size - asize >= 0\n");
    return old_ptr;
  }

  // If our block is last block in heap we make extend_heap */
  if (is_block_last(old_ptr)) {
    // printf("Realloc: Our block is last - we make extend_heap\n");
    size_t extendsize = get_extendsize(asize - old_size);
    last_prev_alloc = ALLOCATED;
    if (extend_heap(extendsize) == NULL)
      return NULL;
  }

  // If next block is FREE we try to use it
  if (GET_ALLOC(HDRP(NEXT_BLKP(old_ptr))) == FREE) {
    // printf("Realloc: Next block is FREE\n");
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(old_ptr)));

    // If next block (FREE one) is last in heap, but too small we extend it
    if (is_block_last(NEXT_BLKP(old_ptr)) && (old_size + next_size < asize)) {
      // printf("Realloc: Next block is to small - we make extend heap\n");
      size_t extendsize = get_extendsize(asize - old_size - next_size);
      last_prev_alloc = FREE;
      if (extend_heap(extendsize) == NULL)
        return NULL;
      next_size = GET_SIZE(HDRP(NEXT_BLKP(old_ptr)));
    }
    // printf("Realloc next block is FREE, next_size=%li\n", next_size);

    // We do merge with split if possible
    if (old_size + next_size >= ALIGNMENT + asize) {
      size_t prev_alloc = GET_PREV_ALLOC(HDRP(old_ptr));
      remove_block_from_free_list(NEXT_BLKP(old_ptr));
      make_allocated_block(old_ptr, asize, prev_alloc);
      // printf("Realloc split merge old_ptr=%p, asize=%li\n", old_ptr, asize);
      char *bp = NEXT_BLKP(old_ptr);
      // printf("Realloc split merge next_ptr=%p, size=%li\n", bp, old_size + next_size - asize);
      make_free_block(bp, old_size + next_size - asize, ALLOCATED);
      add_block_to_free_list(bp);
      return old_ptr;
    }

    // We merge without split
    if (old_size + next_size >= asize) {
      // printf("Realloc simple merge\n");
      size_t prev_alloc = GET_PREV_ALLOC(HDRP(old_ptr));
      remove_block_from_free_list(NEXT_BLKP(old_ptr));
      make_allocated_block(old_ptr, old_size + next_size, prev_alloc);
      set_prev_alloc(NEXT_BLKP(old_ptr), ALLOCATED);
      return old_ptr;
    }
  }

  // printf("Realloc copy\n");
  // If we cannot perform anything optimal we just make alloc a new block and
  // copy data
  void *new_ptr = malloc(size);

  // If malloc fails, the original block is left untouched
  if (!new_ptr)
    return NULL;

  memcpy(new_ptr, old_ptr, old_size);

  // Free the old block
  free(old_ptr);

  return new_ptr;
}

// calloc - Allocate the block and set it to zero
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  // If malloc fails, skip zeroing out the memory
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

// Print all blocks in heap
static void printf_heap(char* message){
  // printf("// printf HEAP: %s!\n", message);
  
  void *bp;
  int i = 0;

  // Print sentinel block
  printf("[SEN] BLKP: %p next: %p prev: %p size: %5i %5s %10s\n", 
    sentinel_pointer, 
    GET_P(NEXT_P(sentinel_pointer)), 
    GET_P(PREV_P(sentinel_pointer)), 
    GET_SIZE(HDRP(sentinel_pointer)), 
    "ALLOC", 
    "PREV_ALLOC");

  // We iterate through heap with boundary tags
  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    size_t hd_alloc = GET_ALLOC(HDRP(bp));
    size_t hd_prev_alloc = GET_PREV_ALLOC(HDRP(bp));
  
    char *s_hd_alloc = (hd_alloc) ? "ALLOC" : "FREE";
    char *s_hd_prev_alloc = (hd_prev_alloc) ? "PREV_ALLOC" : "PREV_FREE";
    void *next = GET_P(NEXT_P(bp));
    void *prev = GET_P(PREV_P(bp));

    if (i == 0){
      printf("[PRO] BLKP: %p next: %s prev: %s size: %5i %5s %10s\n",
           bp, "0x?????????", "0x?????????", GET_SIZE(HDRP(bp)), s_hd_alloc, s_hd_prev_alloc);
    }
    else if (hd_alloc == FREE){
      printf("[%3i] BLKP: %p next: %p prev: %p size: %5i %5s %10s\n",
           i, bp, next, prev, GET_SIZE(HDRP(bp)), s_hd_alloc, s_hd_prev_alloc);
    }
    else{
      printf("[%3i] BLKP: %p next: %s prev: %s size: %5i %5s %10s\n",
           i, bp, "0x?????????", "0x?????????", GET_SIZE(HDRP(bp)), s_hd_alloc, s_hd_prev_alloc);
    }
    i++;
  }

  bp = NEXT_BLKP(bp);
  size_t hd_prev_alloc = GET_PREV_ALLOC(HDRP(bp));
  char *s_hd_prev_alloc = (hd_prev_alloc) ? "PREV_ALLOC" : "PREV_FREE";

  // Print epilogue block
  printf("[EPI] BLKP: %p next: %s prev: %s size: %5i %5s %10s\n", 
    bp, 
    "0x?????????", 
    "0x?????????", 
    GET_SIZE(HDRP(bp)), 
    "ALLOC", 
    s_hd_prev_alloc);

  return;
}

// mm_checkheap - Check heap consistency
void mm_checkheap(int verbose) {
  if (verbose == 1)
    printf_heap("Checkheap");
  
  void *bp;
  int i = 0;

  size_t old_hd_alloc;

  // We iterate through heap with boundary tags
  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    size_t hd_alloc = GET_ALLOC(HDRP(bp));
    size_t hd_prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    size_t ft_alloc = GET_ALLOC(FTRP(bp));
    size_t ft_prev_alloc = GET_PREV_ALLOC(FTRP(bp));

    // Check header and footer equality
    if (hd_alloc == FREE){
      assert(hd_alloc == ft_alloc);
      assert(hd_prev_alloc == ft_prev_alloc);
    }

    if (bp != heap_listp){
      // Check that there are no two subsequent free blocks
      assert(old_hd_alloc != FREE || hd_alloc != FREE);

      // Check that prev_alloc field is same as previous block alloc field
      assert(old_hd_alloc == hd_prev_alloc);
    }
    
    old_hd_alloc = hd_alloc;
    i++;
  }

  // We iterate through heap with free list pointers
  for (bp = get_next_free_blkp(sentinel_pointer); bp != sentinel_pointer; bp = get_next_free_blkp(bp)) {
    size_t hd_alloc = GET_ALLOC(HDRP(bp));

    // Check if block is free
    assert(hd_alloc == FREE);

    // Check if block points to free blocks
    assert(GET_ALLOC(HDRP(get_next_free_blkp(bp))) == FREE);
    assert(GET_ALLOC(HDRP(get_prev_free_blkp(bp))) == FREE);

    // Check if blocks points to each other
    assert(get_next_free_blkp(get_prev_free_blkp(bp)) == bp);
    assert(get_prev_free_blkp(get_next_free_blkp(bp)) == bp);
  }
}