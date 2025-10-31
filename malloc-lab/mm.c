
#include "mm.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team1",
    /* First member's full name */
    "Terry Ahn",
    /* First member's email address */
    "t3rryahn.dev@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define CHUNKSIZE (1 << 12)  
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define WSIZE 8
#define DSIZE 16
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(size_t *)(p))
#define PUT(p, val) (*(size_t *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0xF)
#define GET_ALLOC(p) (GET(p) & 0x1)  

// Given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


#define PREV_FREE_P(bp) (*(char **)(bp))
#define NEXT_FREE_P(bp) (*(char **)(bp + WSIZE))

// size list num
#define SIZE_NUM 10

// list
static char *heap_listp;  // 힙 포인터
void *seg_free_list[SIZE_NUM];

// function prototype
int mm_init(void);
void mm_free(void *bp);
void *mm_malloc(size_t size);
void *mm_realloc(void *bp, size_t size);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void add_block_to_freelist(void *bp);
static void remove_block(void *bp);

// static void *fast32_list = NULL;   // asize == 32인 블록들 (FREE 상태로 쌓여있음)
// static void *fast128_list = NULL;  // asize == 128인 블록들
// static void *try_fast_path(size_t size);

int find_list_index(size_t size);
int square_next(int x);

/* 
    mm_init
*/
int mm_init(void) {
    for (int i = 0; i < SIZE_NUM; i++) {
        seg_free_list[i] = NULL;
    }

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
        return -1;
    }
    PUT(heap_listp, 0);                            
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  // prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  // prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));      // epilogue header

    return 0;
}

/*
 * exxtend_heap 
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    bp = mem_sbrk(size);
    if (bp == (void *)-1) {
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}


// find list index 집어넣을 사이즈에 적합한 리스트 찾기
int find_list_index(size_t size) {
    int index = 0;
    size = (size > 4) ? size : 4;

    while ((1 << (index + 4)) < size && index < SIZE_NUM - 1) {
        index++;
    }

    return index;
}

/*
    coalesce
*/
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // 이전 블록 과 병합
    if (!prev_alloc) {
        remove_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // 다음 블록과 병합
    if (!next_alloc) {
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    add_block_to_freelist(bp);
    return bp;
}

// 가용리스트 추가 함수
static void add_block_to_freelist(void *bp) {
    int seg_list_index = find_list_index(GET_SIZE(HDRP(bp)));

    PREV_FREE_P(bp) = NULL;

    if (seg_free_list[seg_list_index] == NULL) {
        NEXT_FREE_P(bp) = NULL;
    } else {
        NEXT_FREE_P(bp) = seg_free_list[seg_list_index];
        PREV_FREE_P(seg_free_list[seg_list_index]) = bp;
    }

    seg_free_list[seg_list_index] = bp;
}

// block을 free 할때 가용리스트 업데이트
static void remove_block(void *bp) {
    int seg_list_index = find_list_index(GET_SIZE(HDRP(bp)));

    if (PREV_FREE_P(bp)) {
        NEXT_FREE_P(PREV_FREE_P(bp)) = NEXT_FREE_P(bp);
    } else {
        seg_free_list[seg_list_index] = NEXT_FREE_P(bp);
    }

    if (NEXT_FREE_P(bp)) {
        PREV_FREE_P(NEXT_FREE_P(bp)) = PREV_FREE_P(bp);
    }
}

/*
 * find fit 
 */
static void *find_fit(size_t asize) {
    void *bp = NULL;
    int index = find_list_index(asize);

    while (index < SIZE_NUM) {
        for (bp = seg_free_list[index]; bp != NULL; bp = NEXT_FREE_P(bp)) {
            size_t current_size = GET_SIZE(HDRP(bp));
            if (asize <= current_size) {
                return bp;
            }
        }
        index++;
    }

    return NULL;
}

/*
    place
 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    remove_block(bp);

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

// x 보다 한단계 더큰 2의 제곱수로 올림.
int square_next(int x) {
    if (x < 1) {
        return 1;
    }


    int power = 1;
    while (power < x) {
        power *= 2;
    }
    return power;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 */
void *mm_malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) return NULL;

    if (size <= CHUNKSIZE) {
        size = square_next(size);
    }

    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    if (asize <= 128) {
        extendsize = 256;      
    } else if (asize <= 256) {
        extendsize = 512;      
    } else if (asize <= 512) {
        extendsize = 1024;     
    } else if (asize <= 1024) {
        extendsize = 2048;     
    } else {
        extendsize = MAX(asize, CHUNKSIZE); // big stuff still gets 4096+
    }
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    }

    place(bp, asize);
    return bp;
}

/*
 * mm_free
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size) {
    size_t asize;

    if (size <= 0) {
        mm_free(bp);
        return 0;
    }
    if (bp == NULL) {
        return mm_malloc(size);
    }

    size_t oldsize = GET_SIZE(HDRP(bp));

    if (size <= DSIZE) {  
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    if (oldsize - DSIZE >= asize) {
        return bp;
    }

    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));

    if (!next_alloc && (oldsize + next_size >= asize)) {
        remove_block(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(oldsize + next_size, 1));
        PUT(FTRP(bp), PACK(oldsize + next_size, 1));
        return bp;
    }

    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));

    if (!prev_alloc && (oldsize + prev_size >= asize)) {
        remove_block(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);
        memmove(bp, NEXT_BLKP(bp), asize);
        PUT(HDRP(bp), PACK(oldsize + prev_size, 1));
        PUT(FTRP(bp), PACK(oldsize + prev_size, 1));
        return bp;
    }

    oldsize -= DSIZE;

    void *newp = mm_malloc(size);
    if (newp == NULL) {
        return 0;
    }

    memcpy(newp, bp, oldsize);
    mm_free(bp);
    return newp;
}

// LIFO push: bp를 리스트 앞으로 붙인다
// static inline void fast_push(void **list_head, void *bp) {
//     // bp의 payload 첫 8바이트에 next를 저장
//     *(void **)bp = *list_head;
//     *list_head = bp;
// }

// // LIFO pop: 리스트 머리에서 하나 꺼낸다
// static inline void *fast_pop(void **list_head) {
//     void *bp = *list_head;
//     if (bp != NULL) {
//         *list_head = *(void **)bp;
//     }
//     return bp;
// }

// static inline void mark_allocated(void *bp, size_t block_size) {
//     PUT(HDRP(bp), PACK(block_size, 1));
//     PUT(FTRP(bp), PACK(block_size, 1));
// }

// static void refill_fast_class(void **list_head,
//                               size_t block_size,
//                               size_t batch_bytes)
// {
//     // sanity: block_size는 반드시 16바이트 정렬돼 있어야 하고,
//     // batch_bytes는 block_size의 배수여야 한다고 가정한다.

//     // 우리가 실제로 sbrk 할 크기:
//     //   [batch_bytes of usable blocks] + [WSIZE for a new epilogue header]
//     size_t total_request = batch_bytes + WSIZE;

//     char *chunk = mem_sbrk(total_request);
//     if (chunk == (void *)-1) {
//         // 힙 확장 실패 -> 그냥 아무 것도 안 쌓는다.
//         return;
//     }

//     // chunk 영역은 이렇게 쓸 거다:
//     // [ block0 | block1 | ... | block(n-1) | epilogue_header(8B) ]
//     //
//     // block i 의 레이아웃 (총 block_size bytes):
//     //   [header(8)][payload...][footer(8)]
//     //
//     // bp(payload 시작)는 (block_base + WSIZE)

//     size_t num_blocks = batch_bytes / block_size;
//     char *cursor = chunk;

//     for (size_t i = 0; i < num_blocks; i++) {
//         // payload 시작 주소(bp)
//         void *bp = (void *)(cursor + WSIZE);

//         // free block으로 초기화 (alloc = 0)
//         PUT(HDRP(bp), PACK(block_size, 0));
//         PUT(FTRP(bp), PACK(block_size, 0));

//         // fast list에 push
//         fast_push(list_head, bp);

//         // 다음 블록 위치로 이동
//         cursor += block_size;
//     }

//     // cursor는 이제 chunk + batch_bytes 를 가리킨다.
//     // 여기에 새 에필로그 헤더를 박는다.
//     // 에필로그는 size=0, alloc=1
//     PUT(cursor, PACK(0, 1));
// }

// /* ------------------ fast path 사용 예시 (malloc 앞부분) ------------------ */
// /*
//  * 이건 mm_malloc 안에 들어갈 "앞부분" 예시야.
//  * 너는 mm_malloc 맨 위에서 이걸 쓰고,
//  * 안 잡히면 기존 로직(find_next_power -> asize -> find_fit ...)으로 가면 된다.
//  *
//  * 핵심 포인트:
//  *   - fast path는 find_next_power 하기 전에 돌아야 함.
//  *   - trace8에서 자주 나오는 요청 크기를 기준으로 분기한다.
//  *     여기서는 예시로
//  *       size <= 16   -> asize = 32 class
//  *       size <= 112  -> asize = 128 class
//  */

// void *try_fast_path(size_t size) {
//     // class 1: 매우 작은 요청 (예: trace8에서 존나 반복되는 16B 수준)
//     if (size <= 16) {
//         if (fast32_list == NULL) {
//             // 예: 32바이트짜리 블록 8개 -> 총 256바이트
//             refill_fast_class(&fast32_list, 32 /*block_size*/, 256 /*batch_bytes*/);
//         }

//         void *bp = fast_pop(&fast32_list);
//         if (bp != NULL) {
//             mark_allocated(bp, 32);
//             return bp;
//         }
//         // 못 뽑았으면 NULL 리턴해서 일반 경로 타게 한다
//     }

//     // class 2: 중간 소형 요청 (trace8에서 반복되는 ~112B 정도)
//     if (size <= 112) {
//         if (fast128_list == NULL) {
//             // 128바이트짜리 블록 8개 -> 총 1024바이트
//             refill_fast_class(&fast128_list, 128 /*block_size*/, 1024 /*batch_bytes*/);
//         }

//         void *bp = fast_pop(&fast128_list);
//         if (bp != NULL) {
//             mark_allocated(bp, 128);
//             return bp;
//         }
//     }

//     // fast path에 해당 안 되거나 못 뽑았으면 일반 경로로 가야 하므로 NULL
//     return NULL;
// }
