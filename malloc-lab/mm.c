/*
 * mm-naive.c - Evolving into an explicit free list implementation.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};


/* Basic constants and macros */
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */
// ⭐ 가용 블록에 필요한 최소 크기 (Header:4 + Footer:4 + NextPtr:8 + PrevPtr:8 = 24)
#define MIN_FREE_BLOCK_SIZE 24
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Free list pointers manipulation macros (assuming 64-bit pointers) */
// bp는 가용 블록의 payload 시작점을 가리킴
// Next 포인터는 payload 시작 위치(bp)에 저장
#define GET_NEXT_FREE(bp) (*(void **)(bp))
// ⭐ Prev 포인터는 Next 포인터 바로 뒤(bp + DSIZE)에 저장 (8바이트 오프셋)
#define GET_PREV_FREE(bp) (*(void **)((char *)(bp) + DSIZE))

#define SET_NEXT_FREE(bp, ptr) (GET_NEXT_FREE(bp) = (ptr))
// ⭐ Prev 포인터 설정 시에도 DSIZE 오프셋 사용
#define SET_PREV_FREE(bp, ptr) (GET_PREV_FREE(bp) = (ptr))


/* Global variables */
static char *heap_listp = NULL;     /* Pointer to first block */
static char *free_list_tail = NULL; /* Pointer to the tail of the free list (LIFO) */


/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void insert_free_block(void *bp);
static void remove_free_block(void *bp);

/* LIFO (Tail Insertion) Free List Insertion */
void insert_free_block(void *bp) {
    // bp becomes the new tail. Its 'next' should be NULL.
    SET_NEXT_FREE(bp, NULL);
    // bp's 'prev' should point to the old tail.
    SET_PREV_FREE(bp, free_list_tail);

    // If the list wasn't empty, the old tail's 'next' should point to bp.
    if (free_list_tail != NULL) {
        SET_NEXT_FREE(free_list_tail, bp);
    }
    // Update the global tail pointer
    free_list_tail = bp;
}

/* Standard Doubly Linked List Node Removal (Revised) */
void remove_free_block(void *bp) {
    void *prev = GET_PREV_FREE(bp);
    void *next = GET_NEXT_FREE(bp);

     // Debug print (optional)
    // printf("[DEBUG] remove_free_block: bp=%p, prev=%p, next=%p, tail=%p\n", bp, prev, next, free_list_tail);

    // Connect previous block to the next block
    if (prev != NULL) {
        // Check if next is valid before dereferencing (important!)
        // if (next == NULL && free_list_tail != bp ) { // Defensive check, might hide underlying issues
        //     printf("[WARNING] remove_free_block: bp=%p seems to be tail but tail pointer is %p\n", bp, free_list_tail);
        // }
        SET_NEXT_FREE(prev, next); // prev's next skips bp
    }

    // Connect next block to the previous block
    if (next != NULL) {
        // Check if prev is valid before dereferencing
        // if (prev == NULL /* && some_head_pointer != bp */ ) { // If using head pointer
        //     printf("[WARNING] remove_free_block: bp=%p seems to be head but prev is NULL\n", bp);
        // }
         SET_PREV_FREE(next, prev); // next's prev skips bp
    }

    // Update tail pointer *only* if bp was the tail
    // This is crucial for LIFO implementation with tail pointer
    if (free_list_tail == bp) {
         free_list_tail = prev; // The new tail is the block before bp
    }

    // Optional: Clear pointers in the removed block (good practice, helps debugging)
    // SET_NEXT_FREE(bp, NULL);
    // SET_PREV_FREE(bp, NULL);
}


/* Find the first fit in the free list (searching from tail backwards - LIFO friendly) */
static void *find_fit(size_t asize)
{
    void *bp;
    // Start from the tail and go backwards using PREV pointers
    for (bp = free_list_tail; bp != NULL; bp = GET_PREV_FREE(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp; // Found a fit
        }
    }
    return NULL; /* No fit found */
}

/* Place block of asize bytes at start of free block bp */
/* and split if remainder would be at least minimum block size */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    // void *prev_free = GET_PREV_FREE(bp); // Get free list pointers *before* removing
    // void *next_free = GET_NEXT_FREE(bp);

    //printf("[DEBUG] place: bp=%p, req_size=%lu, block_size=%lu\n", bp, asize, csize);

    // ⭐ Remove the block from free list *before* modifying it.
    // --- 수정 시작: Heuristic 검사 제거 ---
    bool removed_successfully = false;
    if (bp != NULL && ((uintptr_t)bp & 0x7) == 0) { // NULL 및 정렬만 확인
        // Optional: Add checks here if GET_PREV_FREE or GET_NEXT_FREE cause issues *inside* remove_free_block
        // printf("[DEBUG] Attempting remove_free_block for bp=%p\n", bp);
        remove_free_block(bp);
        removed_successfully = true; // Assume removal was okay if no crash here
        // printf("[DEBUG] Completed remove_free_block for bp=%p\n", bp);
    } //else {
    //     printf("[WARNING] place: Invalid bp=%p provided. Skipping remove.\n", bp);
    // }
    // --- 수정 끝 ---


    // Check if splitting is possible and worthwhile
    // ⭐ Only proceed with allocation if the block was successfully removed (or considered valid)
    if (removed_successfully) { // or if (!valid_free_list_block was based on better checks)
        if ((csize - asize) >= MIN_FREE_BLOCK_SIZE) {
            // Allocate the first part
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));

            // Get the pointer to the remaining part
            void *right_bp = NEXT_BLKP(bp);

            // Initialize the remaining part as a free block
            PUT(HDRP(right_bp), PACK(csize - asize, 0));
            PUT(FTRP(right_bp), PACK(csize - asize, 0));

            // Insert the new free block (remainder) into the free list
            insert_free_block(right_bp);
            // printf("[DEBUG] place: Split block. Allocated %lu at %p, New free block %lu at %p\n", asize, bp, (csize - asize), right_bp);

        } else {
            // Don't split, allocate the entire block
            PUT(HDRP(bp), PACK(csize, 1));
            PUT(FTRP(bp), PACK(csize, 1));
            // printf("[DEBUG] place: Allocated entire block %lu at %p\n", csize, bp);
        }
    } //else {
    //      printf("[ERROR] place: Did not proceed with allocation for bp=%p due to invalid state or failed removal.\n", bp);
    //      // Depending on requirements, you might want to signal an error differently
    //      // or attempt to recover, but for now, just logging is safer.
    // }
}


/* Coalesce free blocks */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // Case 1: Prev allocated, Next allocated -> No coalescing needed now
    // Just insert current block into free list
    if (prev_alloc && next_alloc) {
        insert_free_block(bp); // ⭐ Insert bp itself if no merge happens
        return bp;
    }

    // Case 2: Prev allocated, Next free
    else if (prev_alloc && !next_alloc) {
        remove_free_block(NEXT_BLKP(bp)); // Remove next block from free list
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0)); // Footer uses the same bp pointer but accesses end of block
    }

    // Case 3: Prev free, Next allocated
    else if (!prev_alloc && next_alloc) {
        remove_free_block(PREV_BLKP(bp)); // Remove prev block from free list
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0)); // Update footer of current block first
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // Update header of previous block
        bp = PREV_BLKP(bp); // Move bp to the beginning of the merged block
    }

    // Case 4: Prev free, Next free
    else {
        remove_free_block(PREV_BLKP(bp)); // Remove prev block
        remove_free_block(NEXT_BLKP(bp)); // Remove next block
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // FTRP(NEXT..) = HDRP(NEXT..)
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // Update header of prev block
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // Update footer of next block
        bp = PREV_BLKP(bp); // Move bp to the beginning of the merged block
    }

    // ⭐ Insert the final coalesced block into the free list
    insert_free_block(bp);
    // printf("[DEBUG] coalesce: Coalesced block at %p, size %lu\n", bp, size);

    return bp;
}


/* Extend heap with free block and return its block pointer */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL; /* Error */

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp); // Coalesce will handle insertion into free list
}

/* Initialize the memory manager */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE); // heap_listp points to payload of prologue block

    free_list_tail = NULL; // Initialize free list tail

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/* Allocate a block from the free list */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) // Payload size <= 8
        asize = MIN_FREE_BLOCK_SIZE; // Min block size is 24 (hdr+ftr+prev+next)
    else
        // Need space for header(4), footer(4), and payload (size)
        // Total required = size + DSIZE (for hdr/ftr)
        // Align this total size up to nearest DSIZE multiple
        asize = ALIGN(size + DSIZE);

     // Ensure asize is at least the minimum free block size needed for pointers later if freed
     asize = MAX(asize, MIN_FREE_BLOCK_SIZE);


    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL; /* Heap extension failed */
    place(bp, asize); // Place block in the newly extended heap space
    return bp;
}

/* Free a block and coalesce */
void mm_free(void *bp)
{
    if (bp == NULL) return; // Handle null pointer free

    size_t size = GET_SIZE(HDRP(bp));

    // Mark the block as free
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // Coalesce with neighbors and add to free list
    coalesce(bp);
}

/* Reallocate a block */
void *mm_realloc(void *ptr, size_t size)
{
    // If ptr is NULL, equivalent to mm_malloc(size)
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    // If size is 0, equivalent to mm_free(ptr) and return NULL
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    void *newptr;
    size_t oldSize = GET_SIZE(HDRP(ptr)); // Full block size
    size_t new_asize; // Adjusted size for the new block

    // Calculate adjusted size for the new allocation request
    if (size <= DSIZE)
        new_asize = MIN_FREE_BLOCK_SIZE;
    else
        new_asize = ALIGN(size + DSIZE);
    new_asize = MAX(new_asize, MIN_FREE_BLOCK_SIZE);


    // If new size is smaller or equal, we might be able to reuse the block (optional optimization)
    // For simplicity, we just allocate new block and copy data
    // (Could add optimization later: if new_asize <= oldSize, potentially shrink in place or just return ptr)

    // Allocate a new block
    newptr = mm_malloc(size); // mm_malloc handles adjusted size calculation internally
    if (newptr == NULL) {
        return NULL; // Allocation failed
    }

    // Copy data from the old block to the new block
    size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE; // Payload size of old block
    if (size < copySize) {
        copySize = size; // Only copy up to the new requested size
    }
    memcpy(newptr, ptr, copySize);

    // Free the old block
    mm_free(ptr);

    return newptr;
}