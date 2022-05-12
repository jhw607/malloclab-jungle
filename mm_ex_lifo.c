/*
---_explicit_lifo---

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
#define PUT_ADDR(p, val) (*(void **)(p) = (val))  // p에 val을 대입

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
    printf("init\n");
    if((heap_listp = mem_sbrk(6*WSIZE)) == (void*)-1){
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp+(1*WSIZE), PACK(DSIZE*2, 1));    // 프롤로그 header 
    PUT_ADDR(heap_listp+(2*WSIZE), NULL);                // 프롤로그 prev
    PUT_ADDR(heap_listp+(3*WSIZE), NULL);                // 프롤로그 next
    PUT(heap_listp+(4*WSIZE), PACK(DSIZE*2, 1));    // 프롤로그 footer
    PUT(heap_listp+(5*WSIZE), PACK(0, 1));          // 에필로그 header
    heap_listp += (2*WSIZE);                        // payload 시작점
    last_listp = heap_listp;                        // next_fit 필요할까?
    free_listp = heap_listp;                // 프롤로그의 footer가 가용리스트의 마지막에 오도록
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){   // 힙 확장
        return -1;
    }
    
    return 0;
}

static void *extend_heap(size_t words){
    printf("extend / size : %d\n", words);

    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if(((long)(bp = mem_sbrk(size))) == -1){
        return NULL;
    }
    printf("extend bp_p : %p\n", bp);

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp){
    printf("coalesce 시작 / bp : %p\n", bp);

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 가용여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 가용여부
    size_t size = GET_SIZE(HDRP(bp));

    // if(prev_alloc && next_alloc){       // 둘 다 안됨
    //     // return bp;
    // }
    if(prev_alloc && !next_alloc){ // 현재 + 다음
        delete_free(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        printf("case2\n");
    }
    else if(!prev_alloc && next_alloc){ // 이전 + 현재
        delete_free(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        printf("case3\n");
        // printf("%d %d\n", GET(PRVP(PREV_BLKP(bp))), GET(NXTP(PREV_BLKP(bp))));
        bp = PREV_BLKP(bp);
    }
    else if(!prev_alloc && !next_alloc){                               // 둘 다 가용
        delete_free(PREV_BLKP(bp));
        delete_free(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        printf("case4\n");
        bp = PREV_BLKP(bp);
    }

    if(HDRP(bp) < (char *)last_listp && (char *)last_listp < FTRP(bp))
            last_listp = bp;
    insert_free(bp);
    printf("coalesce 끝\n");

    return bp;

}
void delete_free(void *bp){
    printf("delete_free / bp : %p\n", bp);

    // 가용 블록 리스트에서 bp제거하고
    // bp의 prev와 next를 연결


    // root의 next에 다음가용 넣고
    // 다음 가용 블록의 prev에 root 넣고
    printf("next free : %p\n", NEXT_FREEP(bp));
    printf("prev free : %p\n", PREV_FREEP(bp));

    if(NEXT_FREEP(bp)){  // bp 다음이 있을 때
        if(PREV_FREEP(bp)){    // bp 이전이 있을 때
            // PUT(NXTP(PREV_FREEP(bp)), NEXT_FREEP(bp)); 
            printf("1next free : %p\n", NEXT_FREEP(bp));
            printf("1prev free : %p\n", PREV_FREEP(bp));
            NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp);
            PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);
        }
        else{                        // bp 이전이 없을 때 -> 루트
            printf("2next free : %p\n", NEXT_FREEP(bp));
            printf("2prev free : %p\n", PREV_FREEP(bp));
            // PUT(NXTP(PREV_FREEP(bp)), end_free); 
            NEXT_FREEP(free_listp) = NEXT_FREEP(bp);
            PREV_FREEP(NEXT_FREEP(bp)) = NULL;
        }
    }
    else{                            // bp 다음이 없을 때 
        if(PREV_FREEP(bp)){             // 이전이 있음
            printf("3next free : %p\n", NEXT_FREEP(bp));
            printf("3prev free : %p\n", PREV_FREEP(bp));
            NEXT_FREEP(PREV_FREEP(bp)) = NULL;
        }
        else{                           // 이전이 없을때
            printf("4next free : %p\n", NEXT_FREEP(bp));
            printf("4prev free : %p\n", PREV_FREEP(bp));
            NEXT_FREEP(free_listp) = NULL;
            return;
        }
    }
    printf("#### bp : %p\n",bp);
    
}

void insert_free(void *bp){
    // 이전 가용 블록의 next에 나를 넣고
    // 다음 가용 블록의 prev에 나를 넣고
    // 내 next에 다음 가용
    // 내 prev에 이전 가용
    // 은 넣는거고

    printf("insert_free / bp : %p\n", bp);
    if(NEXT_FREEP(free_listp)){       // 가용블록이 이미 있을때
        NEXT_FREEP(bp) = NEXT_FREEP(free_listp);
        PREV_FREEP(NEXT_FREEP(free_listp)) = bp;
        NEXT_FREEP(free_listp) = bp;
        PREV_FREEP(bp) = NULL;
        printf("insert_1 - next free : %p\n", NEXT_FREEP(bp));
        printf("insert_1 - prev free : %p\n", PREV_FREEP(bp));
    }
    else{                                   // 가용리스트가 비어있을 때
        NEXT_FREEP(bp) = NULL;
        NEXT_FREEP(free_listp) = bp;
        PREV_FREEP(bp) = NULL;
        printf("insert_2 - next free : %p\n", NEXT_FREEP(bp));
        printf("insert_2 - prev free : %p\n", PREV_FREEP(bp));
    }


    return;
 
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size)
{  printf("malloc 시작\n");
    cnt ++;
    printf("****************cnt : %d\n", cnt);
    
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
    printf("start find_fit / size : %d\n", asize);

    void *bp;
    
    for(bp = free_listp; bp != NULL; bp = NEXT_FREEP(bp)){
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

    // void *bp;
    // printf("last : %p\n", last_listp);
    // printf("prev : %p\n", PREV_FREEP(last_listp));
    // printf("next : %p\n", NEXT_FREEP(last_listp));
    // for(bp=last_listp; !GET_ALLOC(HDRP(bp)); bp=NEXT_FREEP(bp)){
    //     if(bp && (asize <= GET_SIZE(HDRP(bp)))){
    //         last_listp = bp;
    //         return bp;
    //     }
    // }

    // for(bp=NEXT_FREEP(free_listp); bp <= last_listp; bp=NEXT_FREEP(bp)){
    //     if(bp && (asize <= GET_SIZE(HDRP(bp)))){
    //         last_listp = NEXT_FREEP(bp);
    //         return bp;
    //     } 
    // }
    // printf("end find_fit / return NULL \n");
    // return NULL;    

    // #endif
}

static void *next_fit(size_t asize){
    void *bp;

    for(bp=NEXT_FREEP(last_listp); GET_SIZE(HDRP(bp))!=0; bp=NEXT_FREEP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            last_listp = bp;
            return bp;
        }
    }

    for(bp=heap_listp; bp <= last_listp; bp=NEXT_FREEP(bp)){
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
    printf("free / bp : %p\n", bp);
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