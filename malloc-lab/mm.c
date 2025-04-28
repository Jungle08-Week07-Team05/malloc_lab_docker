/*
 * mm-explicit.c - 명시적 가용 리스트(Explicit Free List)를 이용한 malloc 구현.
 *
 * 가용 블록 구조:
 * 헤더(4바이트) | Prev 포인터(8바이트) | Next 포인터(8바이트) | 풋터(4바이트)
 * 최소 블록 크기는 24바이트이다.
 *
 * 할당된 블록 구조:
 * 헤더(4바이트) | 유저 데이터(payload, 8바이트 정렬) | 풋터(4바이트)
 *
 * 가용 리스트 관리:
 * - 명시적 이중 연결 리스트 사용.
 * - free_listp가 가용 리스트의 첫 번째 블록을 가리킨다.
 * - 삽입은 항상 LIFO(최근 삽입) 방식으로 수행한다.
 * - 병합(Coalescing) 시 인접한 가용 블록을 합치고, 가용 리스트를 갱신한다.
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
    "Explicit Free List Team",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

#define ALIGNMENT 8                 // 8바이트 정렬을 위한 크기
#define WSIZE 4                     // 워드 크기 및 헤더/풋터 크기 (4바이트)
#define DSIZE 8                     // 더블 워드 크기 (8바이트)
#define MIN_BLOCK_SIZE 24           // 최소 블록 크기 (헤더+포인터2개+풋터 = 24바이트)
#define CHUNKSIZE (1 << 12)         // 힙 확장 기본 크기 (4096바이트)

#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // 8바이트 정렬에 맞게 size를 올림
#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 두 값 중 큰 값을 반환
#define PACK(size, alloc) ((size) | (alloc)) // 블록 크기와 할당 여부를 합쳐 저장

#define GET(p) (*(unsigned int *)(p)) // 주소 p에 저장된 값을 읽음
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 주소 p에 val을 저장

#define GET_SIZE(p) (GET(p) & ~0x7) // 헤더나 풋터에서 블록 크기를 추출
#define GET_ALLOC(p) (GET(p) & 0x1) // 헤더나 풋터에서 할당 여부를 추출

#define HDRP(bp) ((char *)(bp) - WSIZE) // 블록 포인터 bp로부터 헤더 주소 계산
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록 포인터 bp로부터 풋터 주소 계산
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp))) // 다음 블록의 포인터 계산
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 포인터 계산

#define NEXT_FREE_PTR(bp) (*(void **)(bp)) // 가용 블록의 next 포인터를 읽음
#define PREV_FREE_PTR(bp) (*(void **)((char *)(bp) + DSIZE)) // 가용 블록의 prev 포인터를 읽음
#define SET_NEXT_FREE(bp, ptr) (NEXT_FREE_PTR(bp) = (ptr)) // 가용 블록의 next 포인터를 설정
#define SET_PREV_FREE(bp, ptr) (PREV_FREE_PTR(bp) = (ptr)) // 가용 블록의 prev 포인터를 설정

static char *heap_listp = 0; // 힙의 시작 포인터
static void *free_listp = NULL; // 명시적 가용 리스트의 첫 번째 블록 포인터

static void *extend_heap(size_t words); // 힙을 확장하는 함수
static void *coalesce(void *bp); // 인접 가용 블록들과 병합하는 함수
static void *find_fit(size_t asize); // 주어진 크기에 맞는 가용 블록을 찾는 함수
static void place(void *bp, size_t asize); // 가용 블록에 메모리를 배치하는 함수
static void insert_free_block(void *bp); // 가용 리스트에 블록을 삽입하는 함수
static void remove_free_block(void *bp); // 가용 리스트에서 블록을 제거하는 함수


int mm_init(void)
{
    // 힙의 초기 공간 4워드 할당 (패딩 + 프롤로그 블록 + 에필로그 블록)
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                            // 패딩 워드
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 풋터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 에필로그 헤더
    heap_listp += (2 * WSIZE);                     // heap_listp를 프롤로그 payload로 이동

    free_listp = NULL; // 가용 리스트 포인터 초기화

    // 초기 힙 공간을 CHUNKSIZE만큼 확장
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}


static void insert_free_block(void *bp)
{
    // 현재 가용 블록의 next를 기존 free_listp로 설정
    SET_NEXT_FREE(bp, free_listp);
    // 현재 가용 블록의 prev를 NULL로 설정 (가용 리스트 맨 앞이므로)
    SET_PREV_FREE(bp, NULL);

    // 기존 free_listp가 존재하면, 그 블록의 prev를 현재 bp로 설정
    if (free_listp != NULL)
        SET_PREV_FREE(free_listp, bp);

    // free_listp를 현재 bp로 갱신
    free_listp = bp;
}


static void remove_free_block(void *bp)
{
    void* prev_free = PREV_FREE_PTR(bp);
    void* next_free = NEXT_FREE_PTR(bp);

    // 이전 블록이 있으면, 이전 블록의 next를 현재 bp의 next로 설정
    if (prev_free)
         SET_NEXT_FREE(prev_free, next_free);
    else
         free_listp = next_free; // prev가 없으면 free_listp를 next로 갱신

    // 다음 블록이 있으면, 다음 블록의 prev를 현재 bp의 prev로 설정
    if (next_free)
         SET_PREV_FREE(next_free, prev_free);
}



static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // words 수를 짝수로 맞춰서 8바이트 정렬 유지
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         // 새로 확장된 블록 헤더 설정
    PUT(FTRP(bp), PACK(size, 0));         // 새로 확장된 블록 풋터 설정
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새로운 에필로그 블록 설정

    return coalesce(bp); // 확장된 블록을 병합하여 반환
}


void mm_free(void *bp)
{
    if (bp == 0) return; // NULL 포인터 무시

    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0)); // 헤더에 가용 표시
    PUT(FTRP(bp), PACK(size, 0)); // 풋터에 가용 표시

    coalesce(bp); // 인접 블록들과 병합
}


static void *coalesce(void *bp)
{
    // 이전 블록과 다음 블록의 할당 상태를 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // 병합 전 이웃 블록들의 원래 포인터를 저장 (나중에 제거할 때 사용)
    void *original_prev_bp = NULL;
    void *original_next_bp = NULL;

    if (!prev_alloc) {
        original_prev_bp = PREV_BLKP(bp); // 이전 블록이 가용이면 저장
    }
    if (!next_alloc) {
        original_next_bp = NEXT_BLKP(bp); // 다음 블록이 가용이면 저장
    }

    if (prev_alloc && next_alloc) { // Case 1: 앞뒤 모두 할당됨
        insert_free_block(bp); // 현재 블록만 가용 리스트에 삽입
        return bp;
    }
    else if (prev_alloc && !next_alloc) { // Case 2: 다음 블록만 가용
        remove_free_block(original_next_bp); // 다음 블록을 가용 리스트에서 제거
        size += GET_SIZE(HDRP(original_next_bp)); // 크기 합치기
        PUT(HDRP(bp), PACK(size, 0)); // 새 크기로 헤더 갱신
        PUT(FTRP(bp), PACK(size, 0)); // 새 크기로 풋터 갱신
    }
    else if (!prev_alloc && next_alloc) { // Case 3: 이전 블록만 가용
        remove_free_block(original_prev_bp); // 이전 블록을 가용 리스트에서 제거
        size += GET_SIZE(HDRP(original_prev_bp)); // 크기 합치기
        PUT(HDRP(original_prev_bp), PACK(size, 0)); // 이전 블록 헤더 갱신
        PUT(FTRP(bp), PACK(size, 0)); // 현재 블록 풋터 갱신
        bp = original_prev_bp; // 병합 결과 포인터를 이전 블록으로 변경
    }
    else { // Case 4: 앞뒤 모두 가용
        remove_free_block(original_prev_bp); // 이전 블록 제거
        remove_free_block(original_next_bp); // 다음 블록 제거
        size += GET_SIZE(HDRP(original_prev_bp)) + GET_SIZE(HDRP(original_next_bp)); // 세 블록 크기 합치기
        PUT(HDRP(original_prev_bp), PACK(size, 0)); // 합친 크기로 헤더 갱신
        PUT(FTRP(original_next_bp), PACK(size, 0)); // 합친 크기로 풋터 갱신
        bp = original_prev_bp; // 병합 결과 포인터를 이전 블록으로 변경
    }

    insert_free_block(bp); // 병합 결과 블록을 가용 리스트에 삽입
    return bp;
}


void *mm_malloc(size_t size)
{
    size_t asize;      // 정렬 및 오버헤드 포함 조정된 블록 크기
    size_t extendsize; // 힙을 확장할 크기
    char *bp;

    if (size == 0)
        return NULL; // 요청 크기가 0이면 무시

    if (size <= DSIZE * 2)
        asize = MIN_BLOCK_SIZE; // 최소 블록 크기 (24바이트)
    else
        asize = ALIGN(size + DSIZE); // 요청 크기 + 헤더/풋터 오버헤드 추가 후 정렬

    // 가용 리스트에서 적절한 블록을 찾기
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize); // 찾은 블록에 배치
        return bp;
    }

    // 적절한 블록이 없다면 힙 확장
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL; // 확장 실패 시 NULL 반환

    place(bp, asize); // 확장된 블록에 배치
    return bp;
}

static void *find_fit(size_t asize)
{
    void *bp;

    // 가용 리스트를 순차 탐색하여 첫 번째로 맞는 블록을 찾음
    for (bp = free_listp; bp != NULL; bp = NEXT_FREE_PTR(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp; // 크기가 충분한 블록을 찾으면 반환
        }
    }
    return NULL; // 맞는 블록이 없으면 NULL 반환
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 가용 블록 크기

    remove_free_block(bp); // 가용 리스트에서 현재 블록 제거

    if ((csize - asize) >= MIN_BLOCK_SIZE) { // 분할할 수 있는 경우
        PUT(HDRP(bp), PACK(asize, 1)); // 요청 크기로 헤더 설정 (할당 표시)
        PUT(FTRP(bp), PACK(asize, 1)); // 요청 크기로 풋터 설정 (할당 표시)

        // 남은 부분을 새 가용 블록으로 설정
        void* next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(csize - asize, 0));
        PUT(FTRP(next_bp), PACK(csize - asize, 0));

        coalesce(next_bp); // 남은 가용 블록 병합 및 삽입
    }
    else { // 블록 전체를 할당
        PUT(HDRP(bp), PACK(csize, 1)); // 전체 크기로 헤더 설정
        PUT(FTRP(bp), PACK(csize, 1)); // 전체 크기로 풋터 설정
    }
}


void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size); // NULL 포인터면 malloc과 동일

    if (size == 0) {
        mm_free(ptr); // 크기가 0이면 블록 해제
        return NULL;
    }

    void *newptr;
    size_t oldSize;

    newptr = mm_malloc(size); // 새 블록 요청
    if (newptr == NULL) {
        return NULL; // 실패 시 NULL 반환
    }

    oldSize = GET_SIZE(HDRP(ptr)) - DSIZE; // 기존 블록의 payload 크기
    size_t copySize = size;
    if (oldSize < size) {
        copySize = oldSize; // 실제 복사 크기를 결정
    }

    memcpy(newptr, ptr, copySize); // 데이터를 새 블록으로 복사
    mm_free(ptr); // 기존 블록 해제

    return newptr;
}
