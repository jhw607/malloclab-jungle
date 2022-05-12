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
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) 

// 기본 상수와 매크로

#define WSIZE 4     // 워드 사이즈
#define DSIZE 8     // 더블워드 사이즈
#define CHUNKSIZE (1<<12)   // malloc이 기본적으로 할당해주는 크기

#define MAX(x, y) ((x)>(y) ? (x) : (y))
// x, y 중에 큰 값을 반환

#define PACK(size, alloc) ((size)|(alloc))
// size(뒤에서 세자리부터 000), alloc(001 or 000) 의 & 연산
// header, footer에 넣어주기 위한 값의 형태로 포장(pack)

#define GET(p) (*(unsigned int *)(p)) 
// p가 가리키는 값을 불러옴
#define PUT(p, val) (*(unsigned int *)(p) = (val))
// val의 값을 p가 가리키는 곳에 넣어줌

#define GET_SIZE(p) (GET(p) & ~0x7)
// p의 값을 불러와서 1111 1001 이랑 & 연산
// 할당여부랑? 크기값 부분에 대해 원래값만 살아남음
#define GET_ALLOC(p) (GET(p) & 0x1)
// p의 값을 불러와서 1 이랑 & 연산
// 할당여부 비트만 남음

// bp : payload직전 = header다음 = 블록 포인터

#define HDRP(bp) ((char *)(bp) - WSIZE)
// bp - 4 : header의 위치
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
// (bp의 header위치에서 가져온 크기) + bp - 8 : 다음 블록의 bp - 8 : 나의 footer위치

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// #define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp))) 이거랑 같?
// bp-4에서 가져온 나의 크기 + 원래 bp // 다음 bp의 위치
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
// #define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(FTRP(bp))) 이거랑 같?
// bp-8에서 가져온 크기 : 이전 노드의 크기
// 이전노드의 크기만큼 bp에서 빼면 -> 이전 블록의 bp

// 전역변수 선언
static void *heap_listp;            // 힙의 시작위치(헤더 footer의 다음 값)
static void *last_listp;            // next_fit을 위한 마지막 검색 위치

// 호출되는 함수
static void *extend_heap(size_t);
static void *coalesce(void*);
static void *find_fit(size_t asize);
static void *next_fit(size_t asize);
static void place(void *bp, size_t asize);

int mm_init(void){   // malloc 패키지 초기화

    if((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1){      // heap_listp에 4워드 메모리 할당 후 조건문 확인
        return -1;                                          // mem_sbrk()에서 할당 실패 시 여기서도 -1 반환
    }

    PUT(heap_listp, 0);                                     // 0으로 초기화 // PUT(p,val) : *p = val
    PUT(heap_listp+(1*WSIZE), PACK(DSIZE, 1));              // 1워드(4byte) 더한 값에 pack값(size 8, alloc 1) 넣음 -> 프롤로그 헤더
    PUT(heap_listp+(2*WSIZE), PACK(DSIZE, 1));              // 2워드 더한 값에 pack값(size 8, alloc 1) 넣음 -> 프롤로그 푸터
    PUT(heap_listp+(3*WSIZE), PACK(0, 1));                  // 3워드 더한 값에 pack값(size 0, alloc 1) 넣음 -> 에필로그 헤더
    heap_listp += (2*WSIZE);                                // heap_listp를 2워드 더한 위치로 이동 -> 8 -> 프롤로그 footer를 가리킴
    last_listp = heap_listp;

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){               // 힙 확장 - 초기화할때 해줘버림
        return -1;                                          // chunksize / wsize 로 보내고 함수 안에서 다시 wsize 곱해줌
    }                                                       // 무튼 확장하고 반환된 값이 시원찮으면 -1 반환
    
    return 0;                                               // 다 잘되고 무사히 끝나면 0 반환
}

static void *extend_heap(size_t words){                     // words*4 만큼 힙을 확장하는 함수

    char *bp;                                               // bp 포인터변수 선언
    size_t size;                                            // size 변수 선언
 
    size = (words%2) ? (words+1) * WSIZE : words * WSIZE;   // 들어온 워드값이 짝수면 그대로, 홀수면 1을 더해서 wsize(4)를 곱해줌
                                                            // 블록 사이즈는 8의 배수단위로 끊어져야 하고, 
                                                            // 4로 나눠서 짝수인지 확인하고 다시 곱해주는 게 
                                                            // 구현하기도 쉽고 커지는 부분도 최소화 할 수 있는 거 같음
    if(((long)(bp = mem_sbrk(size))) == -1){                // 그렇게 담은 size로 mem_sbrk호출해서 메모리 확보 mem_sbrk는 정상적으로 동작했을때, 
                                                            // size만큼 힙을 확장하고(mem_brk가 그 마지막을 가리킴) 
                                                            // 확장하기전의 주소값을 돌려줌
        return NULL;                                        // 실패하면 NULL 반환
    }                                                       // 

    PUT(HDRP(bp), PACK(size, 0));                           // bp의 header에 (size:확장할 크기, alloc:0)를 pack해서 담음
    PUT(FTRP(bp), PACK(size, 0));                           // 같은 걸 footer 에도 담음 
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));                   // 에필로그 header를 새로 지정해줌

    return coalesce(bp);                                    // 앞뒤로 가용블록있으면 연결해줘야하니까
}                                                           // return으로 coalesce 함수 호출

static void *coalesce(void *bp){

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));     // 
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));     // 
    size_t size = GET_SIZE(HDRP(bp));                       // 

    if(prev_alloc && next_alloc){                           // 둘 다 안됨
        // return bp;                                       // 여기 없어도됨 마지막꺼 else if로 바꿔주면.
    }
    else if(prev_alloc && !next_alloc){                     // 현재 + 다음
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));              // 
        PUT(HDRP(bp), PACK(size, 0));                       // 
        PUT(FTRP(bp), PACK(size, 0));                       // 
    }
    else if(!prev_alloc && next_alloc){                     // 이전 + 현재
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));              // 
        PUT(FTRP(bp), PACK(size, 0));                       // 
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));            // 
        bp = PREV_BLKP(bp);                                 // 
    }
    else{                                                   // 둘 다 가용
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));            // 
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));            // 
        bp = PREV_BLKP(bp);                                 // 
    }

    if(HDRP(bp)<last_listp<FTRP(bp))
        last_listp = bp;                                        // 연결되면 마지막 검색위치 업데이트

    return bp;                                              // 

}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size){
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    size_t asize;                                           // 
    size_t extendsize;                                      // 
    char *bp;                                               // 

    if(size == 0) return NULL;                              // 

    if(size <= DSIZE){                                      // 
        asize = 2*DSIZE;                                    // 
    }
    else{                                                   // 
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }                                                       // 

    if((bp = next_fit(asize)) != NULL){                     // 
        place(bp, asize);                                   // 
        return bp;                                          // 
    }

    extendsize = MAX(asize, CHUNKSIZE);                     // 
    if((bp = extend_heap(extendsize/WSIZE)) == NULL){       // 
        return NULL;                                        // 
    }
    place(bp, asize);                                       // 
    return bp;                                              // 

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

static void place(void *bp, size_t asize){                  // 
    
    size_t csize = GET_SIZE(HDRP(bp));                      // 
    
    if((csize - asize) >= (2*DSIZE)){                       // 
        PUT(HDRP(bp), PACK(asize, 1));                      // 
        PUT(FTRP(bp), PACK(asize, 1));                      // 
        bp = NEXT_BLKP(bp);                                 // 
        PUT(HDRP(bp), PACK(csize-asize, 0));                // 
        PUT(FTRP(bp), PACK(csize-asize, 0));                // 
    }
    else{                                                   // 
        PUT(HDRP(bp), PACK(csize, 1));                      // 
        PUT(FTRP(bp), PACK(csize, 1));                      // 
    }

}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));                       // 

    PUT(HDRP(bp), PACK(size, 0));                           // 
    PUT(FTRP(bp), PACK(size, 0));                           // 
    coalesce(bp);                                           // 
    
}


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
