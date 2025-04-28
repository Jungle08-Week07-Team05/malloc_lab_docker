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


/* 기본 상수 및 매크로 */
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4             // Word 크기 (헤더/풋터)
#define DSIZE 8             // Double word 크기
#define CHUNKSIZE (1 << 12) // 힙 확장 시 기본 단위 (4096바이트)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 여부 비트 합침

#define GET(p) (*(unsigned int *)(p))              // 주소 p에서 값 읽기
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 주소 p에 값 저장

#define GET_SIZE(p) (GET(p) & ~0x7) // 헤더에서 블록 크기 추출
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당 여부 추출

#define HDRP(bp) ((char *)(bp) - WSIZE)                      // 블록 포인터로 헤더 주소 계산
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 풋터 주소 계산

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))               // 다음 블록
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록

/* 전역 변수: 힙 시작 포인터 */
static char *heap_listp = 0;

static void *find_fit(size_t asize)
{
    /* First-fit search */
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }
    return NULL; /* No fit */
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // Case 1: 양 옆 모두 할당 → 그대로
    if (prev_alloc && next_alloc)
    {
        return bp;
    }

    // Case 2: 다음 블록만 가용
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // Case 3: 이전 블록만 가용
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // Case 4: 양 옆 모두 가용
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

/* 힙 확장 함수: 새 가용 블록 생성 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 정렬을 위해 words 수를 짝수로 맞춰서 WSIZE 곱
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    // 새로 확장한 블록의 헤더/풋터/에필로그 설정
    PUT(HDRP(bp), PACK(size, 0));         // Free block header
    PUT(FTRP(bp), PACK(size, 0));         // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header

    // 앞 블록과 병합 (coalesce)
    return coalesce(bp);
}

/* 힙 초기화 함수 */
int mm_init(void)
{
    // 초기 힙 생성: padding + prologue header/footer + epilogue header
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                            // Padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // Prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // Prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // Epilogue header
    heap_listp += (2 * WSIZE);                     // 유저 블록 시작 위치 설정

    // 힙을 CHUNKSIZE만큼 확장하고 free 블록 생성
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/* 블록 반환 함수 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0)); // 헤더 할당 해제
    PUT(FTRP(bp), PACK(size, 0)); // 풋터 할당 해제
    coalesce(bp);                 // 인접 가용 블록과 병합
}

/* 가용 블록 병합 함수 */

/* 블록 할당 함수 */
void *mm_malloc(size_t size)
{
    size_t asize;      // 정렬 + 오버헤드 적용된 크기
    size_t extendsize; // fit 실패 시 확장할 크기
    char *bp;

    // 0바이트 요청 무시
    if (size == 0)
        return NULL;

    // 최소 블록 크기 맞추기 (DSIZE 이상, header + footer 포함)
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // 프리 리스트에서 적합한 블록 탐색
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize); // 블록 할당 및 나머지 나누기
        return bp;
    }

    // 적당한 블록이 없으면 힙 확장
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/* realloc 함수: 기존 블록 복사 후 해제 */
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *newptr;
//     size_t copySize;

//     if ((newptr = mm_malloc(size)) == NULL)
//         return NULL;

//     copySize = GET_SIZE(HDRP(ptr)) - DSIZE; // payload 크기
//     if (size < copySize)
//         copySize = size;

//     memcpy(newptr, ptr, copySize); // 내용 복사
//     mm_free(ptr);                  // 기존 블록 반환
//     return newptr;
// }

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}