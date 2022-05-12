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

// explicit 추가
#include <sys/mman.h>
#include <errno.h>

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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 // 0000 1000

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
//               (size_t의 크기 + 8-1) & 1111 1001

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) 

// 기본 상수와 매크로
#define WSIZE 4     // 워드 사이즈
#define DSIZE 8     // 더블워드 사이즈
#define CHUNKSIZE (1<<12)   // 

#define MAX(x, y) ((x)>(y) ? (x) : (y))     // x, y 중에 큰 값을 반환

#define PACK(size, alloc) ((size)|(alloc))

#define GET(p) (*(unsigned int *)(p))               // 포인터 p의 값
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // p에 val을 대입

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// #define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp))) 이거랑 같?
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
// #define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(FTRP(bp))) 이거랑 같?

// explicit 추가
// #define PRVP(bp) ((char *)(bp))         // 블록의 prev(이전가용블록의 bp)
// #define NXTP(bp) ((char *)(bp) + WSIZE) // 블록의 next(다음가용블록의 bp)

#define PREV_FREEP(bp) (*(void **)(bp))
#define NEXT_FREEP(bp) (*(void **)(bp + WSIZE))

// #define PREV_PRVP(bp) ((char *)PREV_BLKP(bp))
// #define PREV_NXTP(bp) ((char *)PREV_BLKP(bp) + DSIZE)

// #define NEXT_PRVP(bp) ((char *)NEXT_BLKP(bp))
// #define NEXT_NXTP(bp) ((char *)NEXT_BLKP(bp) + DSIZE)

static void *heap_listp;
static void *last_listp;
static void *free_listp;
static void *start_free;
static void *end_free;
static int cnt = 0;


/* 
 * mm_init - initialize the malloc package.
 */
static void *extend_heap(size_t);
static void *coalesce(void*);
static void *find_fit(size_t asize);
static void *next_fit(size_t asize);
static void place(void *bp, size_t asize);
void delete_free(void *bp);
void insert_free(void *bp);

int mm_init(void)
{
    if((heap_listp = mem_sbrk(6*WSIZE)) == (void*)-1){
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp+(1*WSIZE), PACK(DSIZE*2, 1));    // 프롤로그 header 
    PUT(heap_listp+(2*WSIZE), NULL);                // 프롤로그 prev
    PUT(heap_listp+(3*WSIZE), NULL);                // 프롤로그 next
    PUT(heap_listp+(4*WSIZE), PACK(DSIZE*2, 1));    // 프롤로그 footer
    PUT(heap_listp+(5*WSIZE), PACK(0, 1));          // 에필로그 header
    heap_listp += (2*WSIZE);                        // payload 시작점
    // last_listp = heap_listp;                        // next_fit 필요할까?
    // free_listp = heap_listp + DSIZE;                // 프롤로그의 footer가 가용리스트의 마지막에 오도록
    start_free = end_free = heap_listp;    // 프롤로그 header
    // end_free = heap_listp + (3*WSIZE);  // 에필로그 header
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){   // 힙 확장
        return -1;
    }
    
    return 0;
}

static void *extend_heap(size_t words){
    printf("extend \n");

    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if(((long)(bp = mem_sbrk(size))) == -1){
        return NULL;
    }
    printf("extend bp_d : %d\n", bp);
    printf("extend bp_p : %p\n", bp);

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp){
    printf("coalesce 시작\n");

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 가용여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 가용여부
    size_t size = GET_SIZE(HDRP(bp));

    // if(prev_alloc && next_alloc){       // 둘 다 안됨
    //     // return bp;
    // }
    if(prev_alloc && !next_alloc){ // 현재 + 다음
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        printf("case2\n");
        delete_free(NEXT_BLKP(bp));
    }
    else if(!prev_alloc && next_alloc){ // 이전 + 현재
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        printf("case3\n");
        // printf("%d %d\n", GET(PRVP(PREV_BLKP(bp))), GET(NXTP(PREV_BLKP(bp))));
        delete_free(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);
    }
    else if(!prev_alloc && !next_alloc){                               // 둘 다 가용
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        printf("case4\n");
        delete_free(PREV_BLKP(bp));
        delete_free(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
    }

    // if(HDRP(bp)<last_listp<FTRP(bp))
    //         last_listp = bp;
    insert_free(bp);
    printf("coalesce 끝\n");

    return bp;

}
void delete_free(void *bp){
    printf("delete_free\n");

    // 가용 블록 리스트에서 bp제거하고
    // bp의 prev와 next를 연결

    // 이전 가용 블록의 next에 나를 넣고
    // 다음 가용 블록의 prev에 나를 넣고
    // 내 next에 다음 가용
    // 내 prev에 이전 가용
    // 은 넣는거고

    // 이전 가용 블록의 next에 다음가용 넣고
    // 다음 가용 블록의 prev에 이전가용 넣고
    cnt ++;
    printf("****************cnt : %d\n", cnt);

    // void ** prev_nxtp = NXTP(PREV_FREEP(bp)); // 이전가용의 next포인터 // bp의 prev값 저장 // GET(PRVP(bp))
    // void ** next_prvp = PRVP(NEXT_FREEP(bp)); // 다음가용의 prev포인터 // bp의 next값 저장 // GET(NXTP(bp))
    // printf("bp_get : %p, %p\n", GET(PRVP(bp)), GET(NXTP(bp)));
    // printf("bp_free : %p, %p\n", PREV_FREEP(bp), NEXT_FREEP(bp));
    // printf("bp : %p, %p\n", PRVP(bp), NXTP(bp));
    // printf("** %p %p\n", prev_nxtp, next_prvp);
    // // printf("* %p %p\n", GET(prev_nxtp), GET(next_prvp));
    // printf("D start : %p, end : %p\n", GET(start_free), GET(end_free));
    // printf("P start : %p, end : %p\n", start_free, end_free);
    // PUT(NXTP(PREV_FREEP(bp)), GET(NXTP(bp)));    // 이전 가용블록의 next에 다음 가용블록을.
    if(NEXT_FREEP(bp)!=end_free){    //이전가용이 end를 가리킬때 빼고
        // PUT(NXTP(PREV_FREEP(bp)), NEXT_FREEP(bp)); 
        NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp);
    }
    else{
        // PUT(NXTP(PREV_FREEP(bp)), end_free); 
        NEXT_FREEP(PREV_FREEP(bp)) = end_free;
    }
    // printf("prev_free한테 next주고\n");
    // PUT(PRVP(NEXT_FREEP(bp)), GET(PRVP(bp)));    // 다음 가용블록의 prev에 이전 가용블록을.
    if(PREV_FREEP(bp)!=start_free){
        // PUT(PRVP(NEXT_FREEP(bp)), PREV_FREEP(bp));        
        PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);
    }
    else{
        // PUT(PRVP(NEXT_FREEP(bp)), start_free);         
        PREV_FREEP(NEXT_FREEP(bp)) = start_free; 
    }
    // else{
    //     PUT(next_prvp)
    // }
    // printf("next_free한테 prev주고\n");
}

void insert_free(void *bp){
    // 가장 가까운 가용 노드를 찾아서 비집고 들어가야함
    // void * left_free = 
    printf("insert_free\n");
    if(NEXT_FREEP(start_free)!=end_free){
        void *f = bp;
        while(GET_ALLOC(HDRP(f)) && f!=start_free){
            f = PREV_BLKP(f);
            if(!GET_ALLOC(HDRP(f))){
                PUT(NEXT_FREEP(bp), NEXT_FREEP(f));
                PUT(PREV_FREEP(bp), (char*)f);
                PUT(PREV_FREEP(NEXT_FREEP(f)), (char*)bp);
                PUT(NEXT_FREEP(f), (char*)bp);
                return;
            }
        }
        f = end_free;
        while(GET_ALLOC(HDRP(f)) && f>bp){
            f = PREV_BLKP(f);
            if(!GET_ALLOC(HDRP(f)) && f!=start_free){
                PUT(NEXT_FREEP(bp), NEXT_FREEP(f));
                PUT(PREV_FREEP(bp), (char*)f);
                PUT(PREV_FREEP(NEXT_FREEP(f)), (char*)bp);
                PUT(NEXT_FREEP(f), (char*)bp);
                return;
            }
        }
        // for(void *f = bp; GET_ALLOC(HDRP(f))!=0; f=PREV_BLKP(f)){
        //     // 찾다가
        //     printf("반복문\n");
        //     if(!GET_ALLOC(HDRP(f))){
        //         printf("조건문\n");
        //         PUT(PRVP(NEXT_FREEP(f)), (char*)bp);
        //         PUT(NXTP(bp), NEXT_FREEP(f));
        //         PUT(NXTP(f), (char*)bp);
        //         PUT(PRVP(bp), (char*)f);
        //         return;
        //     }
        // }

    }

    // 첫블록
    printf("첫블록\n");
    PUT(PREV_FREEP(bp), (char*)start_free);   // get으로 호출하면 나오는 값
    PUT(NEXT_FREEP(start_free), (char*)bp);
    PUT(NEXT_FREEP(bp), (char*)end_free);
    PUT(PREV_FREEP(end_free), (char*)bp);
    // printf("bp_get : %p, %p\n", PREV_FREEP(bp), NEXT_FREEP(bp));
    // printf("bp의 prvp, nxtp : %p, %p\n", PREV_FREEP(bp), NEXT_FREEP(bp));
    // printf("start : %p, end : %p\n", GET(start_free), GET(end_free));
    // printf("넣고나서 end의 prev에 : %p\n", GET(PREV_FREEP(end_free)));

    return;
 
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size)
{  printf("malloc 시작\n");
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0) return NULL;    

    if(size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }
        printf("find fit 찾으러가요\n");
    if((bp = find_fit(asize)) != NULL){
        printf("find fit 찾고왔어요\n");
        place(bp, asize);
        return bp;
    }
    printf("시러요\n");

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    printf("malloc 잘 끝남\n");
    return bp;

}

static void *find_fit(size_t asize){

    void *bp;
    
    for(bp = start_free; bp != end_free; bp = NEXT_FREEP(bp)){
        printf("find_fit for 들어옴\n");
        // start_free 부터 alloc이 0인 동안 다음 가용블록으로 업데이트하며 검색
        if(asize <= GET_SIZE(HDRP(bp))){
            printf("find_fit if 들어옴\n");
            // bp의 alloc이 0이고, 찾는 사이즈보다 bp사이즈가 크거나 같으면 가능
            return bp;
        }
    }
    
    // GET_ALLOC(HDRP(bp))
    printf("find_fit NULL\n");
    return NULL;
    // #endif
}

static void *next_fit(size_t asize){
    void *bp;

    for(bp=NEXT_BLKP(last_listp); GET_SIZE(HDRP(bp))!=0; bp=NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            last_listp = bp;
            return bp;
        }
    }

    for(bp=heap_listp; bp <= last_listp; bp=NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            last_listp = bp;
            return bp;
        } 
    }
    
    return NULL;
}

static void place(void *bp, size_t asize){
    printf("place 시작\n");

    size_t csize = GET_SIZE(HDRP(bp));
    printf("place size : %d\n", csize);
    delete_free(bp);    // 가용 블록 리스트에서 제거
    printf("place delete 하고옴\n");
    // 할당
    if((csize - asize) >= (2*DSIZE)){
        printf("place 너무큰가\n");
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        printf("place 자른거 insert\n");
        insert_free(bp);    // 가용 블록 리스트에 삽입
    }
    else{
        printf("place 딱맞음\n");
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }

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
    if(size<=0){
        mm_free(ptr);
        return 0;
    }
    if(ptr==NULL){
        return mm_malloc(size);
    }

    void *newptr = mm_malloc(size);    
    if (newptr == NULL)
      return 0;

    size_t copySize = GET_SIZE(HDRP(ptr));
    // 이 문장 안됨
    // copySize = *(size_t *)((char *)ptr - SIZE_T_SIZE);
    
    if (size < copySize)
      copySize = size;
      
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}

// void *mm_realloc(void *bp, size_t size)
// {
//     if (size <= 0)
//     {
//         mm_free(bp);
//         return 0;
//     }
//     if (bp == NULL)
//     {
//         return mm_malloc(size);
//     }
//     void *newp = mm_malloc(size);
//     if (newp == NULL)
//     {
//         return 0;
//     }
//     size_t oldsize = GET_SIZE(HDRP(bp));
//     if (size < oldsize)
//     {
//         oldsize = size;
//     }
//     memcpy(newp, bp, oldsize);
//     mm_free(bp);
//     return newp;
// }




