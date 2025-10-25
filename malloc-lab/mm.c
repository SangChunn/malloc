#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

#define WSIZE 8
#define DSIZE 16
#define CHUNKSIZE (1<<12)
#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))

#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PRED_PTR(bp) ((char **)(bp))
#define SUCC_PTR(bp) ((char **)(bp + WSIZE))
#define PRED(bp) (*(char **)(bp))
#define SUCC(bp) (*(char **)(bp + WSIZE))

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
    ""
};
/* ----------------------------------------------------------
   malloc size distribution setup (2의 거듭제곱 단위)
   ---------------------------------------------------------- */
static const size_t RANGES[] = {
    8, 16, 32, 64, 128, 256, 512,
    1024, 2048, 4096, 8192, 16384,
    32768, 65536, 131072, 262144,
    524288, 1048576, 2097152, 4194304
};
#define MAX_CLASS (sizeof(RANGES)/sizeof(RANGES[0]))

static unsigned long long count_table[MAX_CLASS];
static unsigned long long total_calls = 0;

/* ----------------------------------------------------------
   전역 변수
   ---------------------------------------------------------- */
static char *heap_listp;
static char *free_listp;
static int stats_registered = 0;

/* ----------------------------------------------------------
   통계 출력 함수
   ---------------------------------------------------------- */
static void print_malloc_stats(void) {
    printf("\n========== [ Malloc Size Distribution Summary ] ==========\n");
    if (total_calls == 0) {
        printf("No malloc calls recorded.\n");
        return;
    }

    double cumulative = 0.0;
    for (size_t i = 0; i < MAX_CLASS; i++) {
        if (count_table[i] == 0) continue;
        double percent = (100.0 * count_table[i]) / total_calls;
        cumulative += percent;
        printf("%8zuB ~ : %9llu calls  (%6.2f%%, cum %6.2f%%)\n",
               RANGES[i], count_table[i], percent, cumulative);
    }

    printf("----------------------------------------------------------\n");
    printf("Total malloc calls : %llu\n", total_calls);

    // 평균, 중앙값, 표준편차 계산
    double mean = 0.0;
    for (size_t i = 0; i < MAX_CLASS; i++)
        mean += RANGES[i] * count_table[i];
    mean /= total_calls;

    double var = 0.0;
    for (size_t i = 0; i < MAX_CLASS; i++) {
        double diff = RANGES[i] - mean;
        var += diff * diff * count_table[i];
    }
    var /= total_calls;

    // 중앙값
    unsigned long long acc = 0;
    double median = 0.0;
    for (size_t i = 0; i < MAX_CLASS; i++) {
        acc += count_table[i];
        if (acc >= total_calls / 2) {
            median = RANGES[i];
            break;
        }
    }

    printf("Average size        : %.2f bytes\n", mean);
    printf("Median size         : %.2f bytes\n", median);

    printf("==========================================================\n");
}

/* ----------------------------------------------------------
   mm_init
   ---------------------------------------------------------- */
int mm_init(void)
{
    if (!stats_registered) {
        memset(count_table, 0, sizeof(count_table));
        total_calls = 0;
        atexit(print_malloc_stats);
        stats_registered = 1;
    }

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);
    free_listp = NULL;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/* ----------------------------------------------------------
   extend_heap, coalesce, find_fit, place
   ---------------------------------------------------------- */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        insert_free_block(bp);
        return bp;
    } else if (prev_alloc && !next_alloc) {
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        remove_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
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

static void *find_fit(size_t asize) {
    for (void *bp = free_listp; bp != NULL; bp = SUCC(bp))
        if (asize <= GET_SIZE(HDRP(bp)))
            return bp;
    return NULL;
}

static void place(void *bp, size_t asize) {
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

/* ----------------------------------------------------------
   mm_malloc / mm_free / mm_realloc
   ---------------------------------------------------------- */
void *mm_malloc(size_t size)
{
    // size 통계 집계 (2의 거듭제곱 구간)
    for (size_t i = 0; i < MAX_CLASS; i++) {
        if (size <= RANGES[i]) {
            count_table[i]++;
            break;
        }
    }
    total_calls++;

    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) return NULL;
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

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

void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) return mm_malloc(size);
    if (size == 0) { mm_free(ptr); return NULL; }

    void *newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;

    size_t oldsize = GET_SIZE(HDRP(ptr));
    if (size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);
    mm_free(ptr);
    return newptr;
}

/* ----------------------------------------------------------
   Free list helpers
   ---------------------------------------------------------- */
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