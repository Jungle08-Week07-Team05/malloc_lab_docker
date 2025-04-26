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
//  double word 크기 선언해놓기
#define ALIGNMENT 8
//블록 크기만 뱉어내게 관리하기
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
//size_t로 정의된 크기의 값을 매크로 ALIGN에 집어넣겠다는 의미
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4             // Word 크기 (헤더/풋터)
#define DSIZE 8             // Double word 크기
#define CHUNKSIZE (1 << 12) // 힙 확장 시 기본 단위 (4096바이트)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
//헤더와 푸터에 저장할 형태. 크기와 할당 유무를 판별해주는 값을 뱉는다.
#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 여부 비트 합침

// 이거 그냥 MAKE하니까 오류생김. 이유는 포인터 값을 함부로 정수로 바꾼다고 미쳤냐고 물어봄. 죄송합니다.
// unsigned int는 부호 없는 32비트 짜리 정수크기임. 그 말인 즉슨 4바이트 즉 헤더를 나타내는 4바이트를 다 데려오겠다 이 소리임 ㄹㅇ 반박불가;;;;
#define GET(p) (*(unsigned int *)(p))              // 주소 p에서 값 읽기

//형태가 중요함 핵심은 4바이트 짜리 포인터 변수가 가리키는 메모리 주소에 내가 집어넣을 val값이 들어간다는 사실만 중요함. 반박시 c알못
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 주소 p에 값 저장


//헤더의 4바이트를 받아와서 1111 1000을 계산하면 뭐가 남겠습니까? 당연히 3이상의 비트중 1이 있는 것만 남겠죠. 이것은 전체 블록의 크기를 지칭합니다.
#define GET_SIZE(p) (GET(p) & ~0x7) // 헤더에서 블록 크기 추출
//이거는 헤더 전체와 0x1즉 0000 0001을 and연산 한다는 소리인데 이게 1이 나오면 이 놈은 할당되어있는 임자있는 사람이란 뜻입니다. 휴
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당 여부 추출

//블록 포인터랑 헤더를 지나고 payload가 시작되는 곳을 칭한다. 해당위치에서 WSIZE 즉 4바이트를 뒤로 간다는 것은 헤더의 시작지점으로 가겠다는 의미이다. 알겠는가? 네! 
#define HDRP(bp) ((char *)(bp) - WSIZE)                      // 블록 포인터로 헤더 주소 계산

//가만 생각해보면 (char*)(bp)는 주소이다. 주소의 위치는 블록의 시작지점에서 4바이트 멀어져있는데 이곳에 블록 전체를 더하면 블록 사이즈에서도 4바이트 더 나아간 값이된다. 여기에 8바이트
//를 뺀다는 것은 푸터의 시작점으로 보내달라고 하는 것이다. 두둥!
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 풋터 주소 계산

//bp는 헤더를 지난  payload의 시작점 여기에 size를 더하면 다음 블록의 payload까지갈 수 있다. 
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))               // 다음 블록
//(char*)(bp) - DSIZE == 현재 블록의 바로 앞블록의 푸터위치
//GET_SIZE == 그 풋터에 저장된 이전 블록의 크기 
//(char*)(bp) -> 이전 블록의 시작위치(헤더주소)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록

/* 전역 변수: 힙 시작 포인터 */
static char *heap_listp = 0;

static void *find_fit(size_t asize)
{
    /* First-fit search */
    void *bp;
    //지역 포인터 변수 bp에 현시점에서 잡고있는 포인터 변수 할당
    //bp를 이용해 사이즈가 각각 0 이상인지 검사한다. 그러면서 한번씩 다음으로 이동하며 다시금 공간이 있는지 조사한다.
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        //할당이 되어있는지 조사하고 && 할당된 사이즈가 비어있는 사이즈 보다 작거나 같은지 검사한다. 그렇다면 bp를 반환 만약 없다면 null이 반환된다.
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }
    return NULL; /* No fit */
}


//만약 find_fit 함수를 통과하면 place함수에 도달하게된다. 
static void place(void *bp, size_t asize)
{   //asize는 할당하고싶은 크기
    //csize 할당을 받으려고 하는 장소의 크기 
    size_t csize = GET_SIZE(HDRP(bp));
    //해당 if문은 csize에 asize의 크기만큼을 하고 남는 공간의 크기가 2*Dize 즉 16바이트라면?  아래를 수행하라는 문장이다. 
    if ((csize - asize) >= (2 * DSIZE))
    {

        //HDRP는 헤더의 시작점 반환 PACK는 할당 유무를 변경
        //그렇다면 해당줄을 헤더의 시작점에 asize를 할당된 형태로 바꾼 16진수를 넣겠다는 소리
        PUT(HDRP(bp), PACK(asize, 1));

        //FTRP는 푸터의 주소를 반환 //PACK는 할당 유무를 변견
        //그렇다면 해당줄은 푸터의 자리에 aize를 할당된 형태로 집어넣는다.
        //왜 이런 행동을 하시죠? => 헤더와 푸터에 저장하는거임 할당 정보를
        //대답이 되었나여? 넵!
        PUT(FTRP(bp), PACK(asize, 1));

        //다음 블록의 payload로 이동
        bp = NEXT_BLKP(bp);

        //HDRP는 헤더의 시작점 반환 PACK는 할당 유무를 변경
        // 아래 두줄은 가용 블럭 상태로 만들어주고 앞과 뒤에 나 지금 텅빈 가용블럭입니다!
        //이렇게 소리지르고 선언한 것임 
        //예시로 csize가 72고 할당하고 싶은 크기가 16임 그러면 56이 남는데 이거 앞뒤로 4바이트씩 때서
        //헤더 푸터 붙이고 이놈은 사용블록입니다. 다음에 필요하시면 찾아주세요 이렇게 적어놓는거임. 반박불가 ㅋ;
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }  else{
        //이것은 할당하려고 하는 블록이 16이고 csize가 26임. 그러면 남겨둬도 어차피 못쓰니까 기냥 
        //안 헷갈리게 끝까지 연결해두는거임. ㅋ;
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }
}

static void *coalesce(void *bp)
{
    //문장으로 정리하자면 이것은 이전 블록의 푸터로 가서 할당이 되어있는지 아닌지 판단한다
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
   //이것은 다음 블록의 헤더로 향하여 할당 여부를 판단한다, 
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // 현재 나의 블록의 사이즈를 판단한다.
    size_t size = GET_SIZE(HDRP(bp));

    // Case 1: 양 옆 모두 할당 → 그대로
    if (prev_alloc && next_alloc)
    {
        return bp;
    }

    // Case 2: 다음 블록만 가용
    else if (prev_alloc && !next_alloc)
    {

        //다음 블록의 헤더로 가서 블록의 크기를 받아오고 이를 size에 더한다.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        //앞 헤더와 뒤 푸터를 가용상태로 변경한다. 
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // Case 3: 이전 블록만 가용
    else if (!prev_alloc && next_alloc)
    {   //이전 값을 받아서 size에 더한다 같이
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        //푸터부터 먼저 가용상태로 변경
        PUT(FTRP(bp), PACK(size, 0));
        //이전 블록의 헤더로 이동해서 해당 위치를 가용상태로 변경
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        //이전 블록을 bp포인터로 잡는다. 
        bp = PREV_BLKP(bp);
    }

    // Case 4: 양 옆 모두 가용
    else
    {

        //앞뒤 크기를 size에 더함. 
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        //이전 블록의 헤더 위치로 이동 가용상태로 변경
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        //다음 블록의 푸터로 이동 가용상태로 변경
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        //이전블록을 bp포인터로 잡는다. 
        bp = PREV_BLKP(bp);
    }

    return bp;
}

/* 힙 확장 함수: 새 가용 블록 생성 */
static void *extend_heap(size_t words)
{
    char *bp;
    //size_t는 그냥 c에서 선언된 표준 자료형인 것 같은 32에서는 unsigned int
    //64에서는 unsign long
    size_t size;

    // 정렬을 위해 words 수를 짝수로 맞춰서 WSIZE 곱
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    //4096바이트를 필드로 아까 mm_init에서 했던 짓 반복.
    // 새로 확장한 블록의 헤더/풋터/에필로그 설정
    PUT(HDRP(bp), PACK(size, 0));         // Free block header
    PUT(FTRP(bp), PACK(size, 0));         // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header

    // 앞 블록과 병합 (coalesce)
    //너는 조금 이따보자
    return coalesce(bp);
}

/* 힙 초기화 함수 */

//16바이트의 힙을 만들고 0-3패딩 4-7 항시할당 헤더 8-11 항시할당 푸터 12-15 마무리 에필로그 라인
//이후 4096바이트 할당함수 extend_heap으로 이동  
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
//malloc에서 초기에 asize에 할당할 크기를 정한다. 
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
    //각 각 함수에 설명 쫙 적어놓음. (읽음 == 이해)  수준임.
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
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    size_t copySize;

    if ((newptr = mm_malloc(size)) == NULL)
        return NULL;

    copySize = GET_SIZE(HDRP(ptr)) - DSIZE; // payload 크기
    if (size < copySize)
        copySize = size;

    memcpy(newptr, ptr, copySize); // 내용 복사
    mm_free(ptr);                  // 기존 블록 반환
    return newptr;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr;
//     void *newptr;
//     size_t copySize;

//     newptr = mm_malloc(size);
//     if (newptr == NULL)
//         return NULL;
//     copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
//     if (size < copySize)
//         copySize = size;
//     memcpy(newptr, oldptr, copySize);
//     mm_free(oldptr);
//     return newptr;
// }