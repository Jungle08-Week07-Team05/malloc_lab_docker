
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"
team_t team = {
    /* Team name */
    "sibal",
    /* First member's full name */
    "Harry Potter",
    /* First member's email address */
    "fuchyou@csapp.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};
#define ALIGNMENT 8 //8바이트씩 정렬할거야
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) //size를 8의 배수로 올림
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))//다시한번 8의 배수로 맞춰줌
#define WSIZE 4 // 헤더와 풋터는 항상 4byte크기로 저장
#define DSIZE 8// 더블워드 크기 - 8byte 정렬단위를 맞추기 위한 기본단위
#define CHUNKSIZE (1<<12) //힙을 확장할때 한번에 늘리는 크기 4096바이트

#define MIN_PAYLOAD 16
#define MIN_BLOCK_SIZE (DSIZE + MIN_PAYLOAD)

#define MAX(x,y) ((x )>(y)?(x):(y)) //두 숫자중 큰 값을 택하는 매크로
#define PACK(size, alloc) ((size) | (alloc)) // 여기선 size는 8의 배수라 하위비트 3이 안쓰임 alloc은 할당됬는지 안됬는지 최하위비트를 0과 1로 구분하기 때문에 or 연산으로 합쳐도 문제가없음
#define GET(p) (*(unsigned int *)(p)) //헤더 or 풋터가 4바이트라 이것들을 읽기위해 4byte인 int형(양수라 unsigned) 포인터로 바꿔주고 그 포인터가 가르키는 메모리 값을 읽어오는 매크로
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 주소 p에 4바이트짜리 값을 val로 저장하는 매크로
#define GET_SIZE(p) (GET(p) & ~0x7) // p가 가리키는 헤더나 풋터에서 '블록 크기만' 뽑아오는 매크로 (하위 3비트는 할당정보니 0으로 무시하고 크기만 읽음)
#define GET_ALLOC(p) (GET(p) & 0x1) // "주소 p에 있는 4바이트 값 중, '할당 여부(alloc bit)'만 추출하는 매크로"
#define HDRP(bp) ((char *)(bp) - WSIZE)   // 블록 포인터는 헤더보다 4byte 뒤에 있다.
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // char로 1바이트씩 움직이게 해놓고 주소를 풋터주소로 바꾸는 메크로
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp))) // 현재 블록(bp) 기준으로, 다음 블록(next block)의 payload 시작 주소를 계산하는 매크로
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 과거 블록의 크기는 현재 블록이 아니라 과거 풋터에 기록돼 있다 이전풋터기록에서 이전블록의 사이즈를 가져온 것.

#define NEXT_FREE(bp) (*(void **)(bp)) //bp를 형변환 한거야 이중연결리스트로 그래서 bp가 가르키는 메모리공간에 다른블록을 가르키는 포인터가 생겨버리는거지 그걸 역참조해서 NEXT_FREE(bp)는 bp안에 다른블록을 가르키는 포인터의 값을 나타내는 아이가 된거야.
#define PREV_FREE(bp) (*(void **)((char *)(bp) + DSIZE))// 그럼이것도 NEXT_FREE와 비슷하지만 한가지 다른게 bp의 시작주소 payload가 가르키는 메모리공간이 아니라 payload에다 4를 더한 주소에 prev_free를 저장하거나 읽는거야
#define SET_NEXT_FREE(bp, ptr) (NEXT_FREE(bp) = (ptr))//그럼 이건 위에는 포인터주소에 역참조한 상황이니까 거기에다가 ptr이라는 주소값을 넣은거지 즉 next인 주소를 넣은거지
#define SET_PREV_FREE(bp, ptr) (PREV_FREE(bp) = (ptr))//현재 가르키는 블록의 payload+wsize 위치에 이전 free블록의 주소를 저장하는거지
static char *heap_listp = NULL;
static void *free_listp; //free 첫 포인터주소 선언.

static void insert_freelist(void *bp);
static void remove_freelist(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);

int mm_init(void)
{
    if((heap_listp=mem_sbrk(4*WSIZE))==(void *)-1) return -1;
    PUT(heap_listp, 0);                            // Padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // Prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // Prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // Epilogue header
    heap_listp += (2 * WSIZE);                     // 유저 블록 시작 위치 설정
    // 힙을 CHUNKSIZE만큼 확장하고 free 블록 생
    free_listp=NULL;
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

static void insert_freelist(void *bp){//free 할때.
    SET_NEXT_FREE(bp,free_listp); // free가 되었으니 payload공간에 freelist의 next를 bp로 써 LIFO(후입선출)개념으로 만든다
    SET_PREV_FREE(bp,NULL);//현재 블록의 prev_free를 NULL로 설정. 첫프리니까가 아니라 나 이제 앞이 null이에요 freelist, 나데려가세요 하는 것
    if(free_listp!=NULL){//free_listp가 값이 있다면 이전 free 됬던 블록의 prev값을 현재 free한 블록으로 바꿔줘야 하기 때문에 free_listp의 prevfree를 bp로 설정해준것
        // free_listp가 NULL이 아니라면 (즉, free list에 기존 블록이 존재한다면),
        // 기존 free_listp 블록의 prev 포인터를
        // 새로 free된 블록(bp)로 설정해 연결을 유지해준다.
        SET_PREV_FREE(free_listp,bp);
    }
    free_listp = bp;
}
static void remove_freelist(void *bp){
    void *prev_bp = PREV_FREE(bp);
    void *next_bp = NEXT_FREE(bp);//포인터 변수 설정
    if (prev_bp!=NULL){    //이전 블록이 null이 아닐때 즉 freelist의 중간에 있는 부분일때
        SET_NEXT_FREE(prev_bp,next_bp);
    }else{
        free_listp=next_bp;
    }
    if (next_bp!=NULL){
        SET_PREV_FREE(next_bp,prev_bp);
    }
}
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));//prev블록의 할당여부 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));//next블록의 할당여부 확인
    size_t size = GET_SIZE(HDRP(bp));//현재 블록의 사이즈를 가져온다
    // Case 1: 양 옆 모두 할당 → 그대로
    if (prev_alloc && next_alloc)//둘다 할당이 되어있다면
    {
        insert_freelist(bp);
        return bp;//현재 bp를 리턴
    }
    // Case 2: 다음 블록만 가용
    else if (prev_alloc && !next_alloc)//오른쪽이 free된 상태라면
    {
        void *next_bp=NEXT_BLKP(bp);//포인터변수 선언 다음블록의 포인터
        remove_freelist(next_bp);//next블록을 freelist에서 제거를 해야지
        size += GET_SIZE(HDRP(next_bp));//오른쪽 블럭의 사이즈를 가져와서 기존 bp size에 추가한다
        PUT(HDRP(bp), PACK(size, 0));//합쳐진 블록헤더를 새 크기와 free상태로 설정
        PUT(FTRP(bp), PACK(size, 0));//풋터도 동일 합쳐진 블록헤더를 새 크기와 free상태로 설정
        insert_freelist(bp);//병합된 bp를 다시 freelist에 넣기
        return bp;
    }
    // Case 3: 이전 블록만 가용
    else if (!prev_alloc && next_alloc)//왼쪽이 free된 상태
    {
        void *prev_bp=PREV_BLKP(bp);
        remove_freelist(prev_bp);
        size += GET_SIZE(HDRP(prev_bp));//사이즈를 늘려준다 헤더의 사이즈를 가져와서 -> 왼쪽 블록 크기를 가져와서 현재 bp 크기에 추가
        PUT(FTRP(bp), PACK(size, 0));//합쳐진  블록의 풋터를 새로운 크기와 free상태로 설정 -> 병합된 전체 블록의 풋터를 새 크기, free 상태로 설정
        PUT(HDRP(prev_bp), PACK(size, 0));//전꺼의 헤더에 사이즈를 갱신해야해서 이렇게 쓰인거지? 풋터는 그냥 덮어씌우면 되니까 상관없는거고? -> 왼쪽 블록의 헤더를 새 크기, free 상태로 설정
        bp = prev_bp;//이전블록을 합친것이기 때문에 이전블록을 현재 bp로 갱신해줬다 ->  병합된 새 블록의 시작 주소를 prev로 갱신
        insert_freelist(bp);
        return bp;
    }
    // Case 4: 양 옆 모두 가용
    else
    {
        void *prev_bp = PREV_BLKP(bp);
        void *next_bp = NEXT_BLKP(bp);
        remove_freelist(prev_bp);
        remove_freelist(next_bp);
        size += GET_SIZE(HDRP(prev_bp)) + GET_SIZE(FTRP(next_bp));//둘다 가져와서 사이즈를 늘려버려
        PUT(HDRP(prev_bp), PACK(size, 0));//아예 이전의 헤더로 가서 새 크기로 설정하고 free해준거구나
        PUT(FTRP(next_bp), PACK(size, 0));//이건 다음의 풋터로 가서 새 크기로 설정하고 free해준거구나
        bp = prev_bp;//그리고 병합된 블록의 시작은 이전일거니까 새블록의 시작주소를 prev로 갱신해준거고?
        insert_freelist(bp);
        return bp;
    }
}
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
 void mm_free(void *bp) {
    if (bp==NULL) return;
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0)); // 헤더 할당 해제
    PUT(FTRP(bp), PACK(size, 0)); // 풋터 할당 해제
    coalesce(bp);                // 병합할때의 함수도 수정을 해줘야겠지?
    //insert_freelist(bp);//병합한 걸 다시 프리리스트에 넣어준다.
}
 static void *find_fit(size_t asize)
 {
     void *bp;
     //for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
     for(bp=free_listp;bp!=NULL;bp=NEXT_FREE(bp))//free_list를 순회하는 조건으로 수정
     {
         //if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
         if(GET_SIZE(HDRP(bp))>=asize)
         {
             return bp;
         }
     }
     return NULL; /* No fit */
 }
 static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    remove_freelist(bp);/////////////////////////////////
    if ((csize - asize) >= MIN_BLOCK_SIZE)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(csize - asize, 0));
        PUT(FTRP(next_bp), PACK(csize - asize, 0));
        insert_freelist(next_bp);
    }
    else{
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }
}
void *mm_malloc(size_t size)
{
    size_t asize;      // 정렬 + 오버헤드 적용된 크기
    size_t extendsize; // fit 실패 시 확장할 크기
    char *bp;
    // 0바이트 요청 무시
    if (size == 0)
        return NULL;
    // 최소 블록 크기 맞추기 (DSIZE 이상, header + footer 포함)
    if (size <= MIN_PAYLOAD)
        asize = 3 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // 프리 리스트에서 적합한 블록 탐색
    if ((bp=find_fit(asize))!=NULL){
        place(bp,asize);
        return bp;
    }
    // 적당한 블록이 없으면 힙 확장
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    //remove_freelist(bp);//////////////////////////////////
    place(bp, asize);
    return bp;
}


void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) return mm_malloc(size); //기존블럭이 없다 -> 새로 malloc할당
        
    if (size == 0) { // 사이즈가 0이다 -> malloc free(ptr)하고 NULL반환 , 0byte크기 블록을 유지할 이유가 없다.
        mm_free(ptr);
        return NULL;
    }

    size_t oldsize = GET_SIZE(HDRP(ptr));//ptr블럭의 크기
    size_t old_payload = oldsize - DSIZE; // Original payload size
    size_t need_payload=ALIGN(size);//요청한 payload를 8의 배수로 설정
    size_t need_size=MAX(need_payload+DSIZE,MIN_BLOCK_SIZE);//만약 최소블록크기보다 작으면 payload에 포인터변수가 못들어가기 때문 작은데 들어가면 -> 구조깨짐
    size_t copySize = (size < old_payload) ? size : old_payload;

    if(need_size<=oldsize){
        size_t remainder_size = oldsize-need_size;
        if(remainder_size>=MIN_BLOCK_SIZE){
            PUT(HDRP(ptr),PACK(need_size,1));
            PUT(FTRP(ptr),PACK(need_size,1));
            void *remainder_bp = NEXT_BLKP(ptr);
            PUT(HDRP(remainder_bp),PACK(remainder_size,0));
            PUT(FTRP(remainder_bp),PACK(remainder_size,0));
            insert_freelist(remainder_bp);
        }
        return ptr;
    }




// // 힙 앞 경계 넘지 않게 보호
//     if ((char *)ptr - DSIZE >= (char *)mem_heap_lo() + 2 * WSIZE) {
//         prev_bp = PREV_BLKP(ptr);
//         prev_alloc = GET_ALLOC(FTRP(prev_bp));
//         prev_size = GET_SIZE(HDRP(prev_bp));
//     }
//     //void *prev_bp=PREV_BLKP(ptr);
//     void *next_bp=NEXT_BLKP(ptr);
//     size_t next_alloc = 1;
//     size_t next_size = 0;
//     if ((char *)next_bp < (char *)mem_heap_hi()) {
//         next_alloc = GET_ALLOC(HDRP(next_bp));
//         next_size = GET_SIZE(HDRP(next_bp));
//     }
    //size_t prev_alloc = GET_ALLOC(FTRP(prev_bp));//여기서 header를 참조하지 않는 이유는 계산단계가 더 많아지기때문. bp -> prev_size -> prev_bp -> hdr
    //next_alloc = GET_ALLOC(HDRP(next_bp));//다음 블록의할당여부(헤더 기준)
    //size_t prev_size = GET_SIZE(HDRP(prev_bp));//이전블록 크기
    //next_size = GET_SIZE(HDRP(next_bp));//다음블록 크기
    void *next_bp = NEXT_BLKP(ptr);
    size_t next_alloc = GET_ALLOC(HDRP(next_bp));
    size_t next_size = GET_SIZE(HDRP(next_bp));

    void *prev_bp = NULL;
    size_t prev_alloc = 1;
    size_t prev_size = 0;

    void *prev_footer_addr = (char *)ptr - DSIZE;
    if (prev_footer_addr >= (char *)mem_heap_lo() + DSIZE) { // Check if address is valid within heap bounds
        prev_alloc = GET_ALLOC(prev_footer_addr);
        if (!prev_alloc) {
            prev_size = GET_SIZE(prev_footer_addr);
            prev_bp = (char *)ptr - prev_size; // Calculate prev_bp only if free
             // Optional: Add assertion: assert(prev_bp >= mem_heap_lo());
        }
    }

    if (!next_alloc && (oldsize + next_size)>=need_size){//다음블록이 가용가능블록이고 현재블록과 필요한 사이즈가 필요한 사이즈보다 크거나 같을때
        remove_freelist(next_bp);//합칠거니까 다음블록은 freelist에서 해제
        size_t total = oldsize + next_size;//합쳐지는 사이즈는 total
        size_t remainder_size = total - need_size;
        PUT(HDRP(ptr),PACK(need_size,1));//현재 블록의 헤더에 새 사이즈와 할당여부 설정
        PUT(FTRP(ptr),PACK(need_size,1));//현재 블록의 풋터에 새 사이즈와 할당여부 설정

        if((remainder_size)>=MIN_BLOCK_SIZE){//남은 블록이 가용가능블록이 될수있을때
            void *remainder = NEXT_BLKP(ptr);//위에서 새 할당을 지정하면 자투리블록이 생기고 그건 NEXT_BLKP로 접근할 수 있다
            PUT(HDRP(remainder),PACK(remainder_size,0));//자투리 블록 헤더
            PUT(FTRP(remainder),PACK(remainder_size,0));//자투리 풋터 헤더
            insert_freelist(remainder);//freelist에 추가
        }else {//////////?
            // Not enough space for remainder, allocate the whole combined block
           PUT(HDRP(ptr), PACK(total, 1));
           PUT(FTRP(ptr), PACK(total, 1));
       }
        return ptr;//제자리에서 확장해서 주소 그대로
    }
    if(!prev_alloc&&(oldsize+prev_size)>=need_size){
        remove_freelist(prev_bp);//이전꺼 freelist에서 해제
        size_t total = prev_size+oldsize;//합쳐지는 사이즈 total
        size_t remainder_size = total - need_size;
        memmove(prev_bp,ptr,copySize);//데이터를 앞으로 복사(overlap 가능해 memmove사용)**********잘 이해안됨
        PUT(HDRP(prev_bp),PACK(need_size,1));
        PUT(FTRP(prev_bp),PACK(need_size,1));
        if((remainder_size)>=MIN_BLOCK_SIZE){
            void *remainder=NEXT_BLKP(prev_bp);
            PUT(HDRP(remainder),PACK(remainder_size,0));
            PUT(FTRP(remainder),PACK(remainder_size,0));
            insert_freelist(remainder);
         }else {//////////?
            // Not enough space for remainder, allocate the whole combined block
           PUT(HDRP(prev_bp), PACK(total, 1));
           PUT(FTRP(prev_bp), PACK(total, 1));
       }
        return prev_bp;
    }
    if(!prev_alloc && !next_alloc && (prev_size+oldsize+next_size)>=need_size){
        remove_freelist(prev_bp);
        remove_freelist(next_bp);
        size_t total=prev_size+oldsize+next_size;
        size_t remainder_size = total - need_size;
        memmove(prev_bp,ptr,copySize);
        PUT(HDRP(prev_bp),PACK(need_size,1));
        PUT(FTRP(prev_bp),PACK(need_size,1));
        if((remainder_size)>=MIN_BLOCK_SIZE){
            void *remainder=NEXT_BLKP(prev_bp);
            PUT(HDRP(remainder),PACK(remainder_size,0));
            PUT(FTRP(remainder),PACK(remainder_size,0));
            insert_freelist(remainder);
         }else{//////////?
            // Not enough space for remainder, allocate the whole combined block
           PUT(HDRP(prev_bp), PACK(total, 1));
           PUT(FTRP(prev_bp), PACK(total, 1));
       }
        return prev_bp;
    }
    void *newptr = mm_malloc(size);//새롭게 할당될 아이?
    if (newptr == NULL)
        return NULL;

    //size_t old_payload = oldsize - DSIZE; // 기존 블록의 payload 크기
    //size_t copySize = (size < old_payload) ? size : old_payload; // 복사할 바이트 수 결정
    memcpy(newptr, ptr, copySize); // 기존 내용 복사
    mm_free(ptr); // 기존 블록 해제
    return newptr; // 새 블록 반환
}






