/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

#define WSIZE 8
#define DSIZE 16
#define CHUNKSIZE (1<< 12)
#define MAX(x, y) ((x) > (y) ? (x) : (y))


#define PACK(size, alloc) ((size) | (alloc))
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0xF) // F or 7
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 
////////
#define PRED_PTR(bp) ((char **)(bp))              // pred pointer 위치
#define SUCC_PTR(bp) ((char **)(bp + WSIZE))      // succ pointer 위치

#define PRED(bp) (*(char **)(bp))                 // pred 값 읽기
#define SUCC(bp) (*(char **)(bp + WSIZE))         // succ 값 읽기


static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static void insert_free_block(void *bp);
static void remove_free_block(void *bp);

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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 16 // 8 or 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0xF) // F or 7

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
 * mm_init - initialize the malloc package.
 */
static char *heap_listp;
static char *free_listp;

int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);

    free_listp = NULL;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));          
    PUT(FTRP(bp), PACK(size, 0));        
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  

    return coalesce(bp);
}

static void *find_fit(size_t asize) {
    void *bp;
    for (bp = free_listp; bp != NULL; bp = SUCC(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    return NULL;
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){
        insert_free_block(bp);
        return bp;
    }
    else if(prev_alloc && !next_alloc){
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if(!prev_alloc && next_alloc){
        remove_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else{
        remove_free_block(PREV_BLKP(bp));
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_free_block(bp);
    return bp;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    remove_free_block(bp);

    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    void *newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;

    size_t oldsize = GET_SIZE(HDRP(ptr));
    if (size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);
    mm_free(ptr);
    return newptr;
}

static void insert_free_block(void *bp)
{
    SUCC(bp) = free_listp;   
    PRED(bp) = NULL;         

    if (free_listp != NULL) 
        PRED(free_listp) = bp;

    free_listp = bp;         
}

static void remove_free_block(void *bp)
{
    if (PRED(bp))
        SUCC(PRED(bp)) = SUCC(bp);
    else
        free_listp = SUCC(bp); 
    if (SUCC(bp))
        PRED(SUCC(bp)) = PRED(bp);
}
