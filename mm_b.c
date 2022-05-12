/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing 
 * the brk pointer. A block is pure payload. There are no headers or 
 * footers. Blocks are never coalesced or reused. Realloc is 
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
    "team 8", 
    /* First member's full name */ 
    "D_corn", 
    /* First member's email address */ 
    "dcron@jungle.com", 
    /* Second member's full name (leave blank if none) */ 
    "", 
    /* Second member's email address (leave blank if none) */ 
    ""}; 

/* single word (4) or double word (8) alignment */ 
#define ALIGNMENT 8 

/* rounds up to the nearest multiple of ALIGNMENT */ 
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) 

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) 

// Basic constants and macros 
#define WSIZE 4             // 워드 = 헤더 = 풋터 사이즈(bytes) 
#define DSIZE 8             // 더블워드 사이즈(bytes) 
#define CHUNKSIZE (1<<12)   // heap을 이정도 늘린다(bytes) 
#define LISTLIMIT 20        //list의 limit 값을 설정해준다. CHUNKSIZE에 비해 충분히 큰 값을 준 것 같다(정확한 이유 모르겠음) 

#define MAX(x, y) ((x) > (y)? (x):(y)) 
// pack a size and allocated bit into a word 
#define PACK(size, alloc) ((size) | (alloc)) 

// Read and wirte a word at address p 
//p는 (void*)포인터이며, 이것은 직접 역참조할 수 없다. 
#define GET(p) (*(unsigned int *)(p))               //p가 가리키는 놈의 값을 가져온다 
#define PUT(p,val) (*(unsigned int *)(p) = (val))   //p가 가리키는 포인터에 val을 넣는다 
#define PUT_P(p,val) (*(void **)(p) = (val))        //p가 가리키는 포인터에 val을 넣는다 

// Read the size and allocated fields from address p 
#define GET_SIZE(p) (GET(p) & ~0x7)                 // ~0x00000111 -> 0x11111000(얘와 and연산하면 size나옴) 
#define GET_ALLOC(p) (GET(p) & 0x1)                 // 할당이면 1, 가용이면 0 

// Given block ptr bp, compute address of its header and footer 
#define HDRP(bp) ((char *)(bp) - WSIZE) 
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //헤더+데이터+풋터 -(헤더+풋터) 

// Given block ptr bp, compute address of next and previous blocks 
// 현재 bp에서 WSIZE를 빼서 header를 가리키게 하고, header에서 get size를 한다. 
// 그럼 현재 블록 크기를 return하고(헤더+데이터+풋터), 그걸 현재 bp에 더하면 next_bp나옴 
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

#define PRED_FREE(bp) (*(void**)(bp)) 
#define SUCC_FREE(bp) (*(void**)(bp + WSIZE)) 


static void *heap_listp; 
static void *segregation_list[LISTLIMIT]; 

static void *extend_heap(size_t words); 
static void *coalesce(void *bp); 
static void *find_fit(size_t asize); 
static void place(void *bp, size_t asize); 
static void remove_block(void *bp); 
static void insert_block(void *bp, size_t size);  

/* 
 * mm_init - initialize the malloc package. 
 */ 
int mm_init(void){ 
    
    int list; 
    
    for (list = 0; list < LISTLIMIT; list++) { 
        segregation_list[list] = NULL;              // segregation_list를 NULL로 초기화 
    }                                               // 나중에 그 list에는 값이 없음을 표시할 수 있도록. 
    
    /* Create the initial empty heap */ 
    if ((heap_listp = mem_sbrk(24 * WSIZE)) == (void *)-1) {    // 패딩 + 헤더 + 20개 + 푸터 + 헤더
        return -1; 
    } 
    PUT(heap_listp, 0);                             // Unused padding 
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE*11, 1));  // 프롤로그 헤더 8/1 

    PUT_P(heap_listp + (2 * WSIZE), NULL);   // free list [0]
    PUT_P(heap_listp + (3 * WSIZE), NULL);   // free list [1]
    PUT_P(heap_listp + (4 * WSIZE), NULL);   // free list [2]
    PUT_P(heap_listp + (5 * WSIZE), NULL);   // free list [3]
    PUT_P(heap_listp + (6 * WSIZE), NULL);   // free list [4]
    PUT_P(heap_listp + (7 * WSIZE), NULL);   // free list [5]
    PUT_P(heap_listp + (8 * WSIZE), NULL);   // free list [6]
    PUT_P(heap_listp + (9 * WSIZE), NULL);   // free list [7]
    PUT_P(heap_listp + (10 * WSIZE), NULL);  // free list [8]
    PUT_P(heap_listp + (11 * WSIZE), NULL);  // free list [9]
    PUT_P(heap_listp + (12 * WSIZE), NULL);  // free list [10]
    PUT_P(heap_listp + (13 * WSIZE), NULL);  // free list [11]
    PUT_P(heap_listp + (14 * WSIZE), NULL);  // free list [12]
    PUT_P(heap_listp + (15 * WSIZE), NULL);  // free list [13]
    PUT_P(heap_listp + (16 * WSIZE), NULL);  // free list [14]
    PUT_P(heap_listp + (17 * WSIZE), NULL);  // free list [15]
    PUT_P(heap_listp + (18 * WSIZE), NULL);  // free list [16]
    PUT_P(heap_listp + (19 * WSIZE), NULL);  // free list [17]
    PUT_P(heap_listp + (20 * WSIZE), NULL);  // free list [18]
    PUT_P(heap_listp + (21 * WSIZE), NULL);  // free list [19]

    PUT(heap_listp + (22 * WSIZE), PACK(DSIZE*11, 1));  // 프롤로그 풋터 8/1 
    PUT(heap_listp + (23 * WSIZE), PACK(0, 1));      // 에필로그 헤더 0/1 

    heap_listp += 2*WSIZE;            
    
    /* Extended the empty heap with a free block of CHUNKSIZE bytes */ 
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) { 
        return -1; 
    } 
    return 0; 
} 


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer. 
 * Always allocate a block whose size is a multiple of the alignment. 
 */ 
void *mm_malloc(size_t size) { 
    int asize = ALIGN(size + SIZE_T_SIZE); 
    
    // size_t asize;        /* Adjusted block size */ 
    size_t extendsize;      /* Amount to extend heap if no fit */ 
    char *bp; 

    /* Search the free list for a fit */ 
    if ((bp = find_fit(asize)) != NULL) {   // 가용 블록을 찾을 수 있다면     
        place(bp, asize);                   // place 함수를 실행시킴 
        return bp; 
    } 

    /* No fit found. Get more memory and place the block */ 
    extendsize = MAX(asize, CHUNKSIZE); 
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) { 
        return NULL; 
    } 

    place(bp, asize); 
    return bp; 
} 


/* 
 * mm_free - Freeing a block does nothing.
 */ 
void mm_free(void *ptr) { 
    size_t size = GET_SIZE(HDRP(ptr)); 

    PUT(HDRP(ptr), PACK(size, 0)); 
    PUT(FTRP(ptr), PACK(size, 0)); 

    coalesce(ptr); 
} 


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */ 
void *mm_realloc(void *ptr, size_t size) { 
    void *oldptr = ptr; 
    void *newptr; 
    size_t copySize; 
    
    newptr = mm_malloc(size); 
    if (newptr == NULL) 
        return NULL; 
    copySize = GET_SIZE(HDRP(oldptr)); 
    if (size < copySize) 
        copySize = size; 

    memcpy(newptr, oldptr, copySize); 
    mm_free(oldptr); 
    return newptr; 
} 

static void *extend_heap(size_t words) { 
    char *bp; 
    size_t size; 

    /* Allocate an even number of words to maintain alignment */ 
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1) { 
        return NULL; 
    } 

    /* Initialize free block header/footer and the epilogue header */ 
    PUT(HDRP(bp), PACK(size, 0));           /* free block header */ 
    PUT(FTRP(bp), PACK(size, 0));           /* free block footer */ 
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue */ 
   
    /* Coalesce if the previous block was free */ 
    return coalesce(bp); 
} 

static void *coalesce(void *bp) { 

    //coalesce는 succ, pred를 보는 것이 아니라 인접한 prev, next 블록을 보는 것을 주의!!!!!!!!!! 
    //전 블록 가용한지 
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); 
    //다음 블록 가용한지 
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); 
    size_t size = GET_SIZE(HDRP(bp)); 

    if (prev_alloc && next_alloc){                  // 둘다 할당 상태 -> 연결할 거 없음
        insert_block(bp,size);                      // 여기서 insert하고 바로 bp 반환
        return bp; 
    } 
    else if (prev_alloc && !next_alloc) {           // 현재 + 다음  
        
        remove_block(NEXT_BLKP(bp));                // 다음 블록 가용리스트에서 삭제 
        
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));      // 연결된 블록 사이즈 
        PUT(HDRP(bp), PACK(size, 0));               // 헤더 갱신
        PUT(FTRP(bp), PACK(size, 0));               // 푸터 갱신
    } 
    else if (!prev_alloc && next_alloc) {           // 이전 + 현재

        remove_block(PREV_BLKP(bp));                // 이전 블록 가용리스트에서 삭제
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));      // 연결된 블록 사이즈
        PUT(FTRP(bp), PACK(size, 0));               // 푸터 갱신
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    // 헤더 갱신
        bp = PREV_BLKP(bp);                         // 앞으로 bp 옮겨줘야함 
    } 
    else if (!prev_alloc && !next_alloc) {          // 이전 + 현재 + 다음  
        remove_block(PREV_BLKP(bp));                // 이전 블록 가용리스트에서 삭제
        remove_block(NEXT_BLKP(bp));                // 다음 블록 가용리스트에서 삭제
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))       // 연결된 블록 사이즈
        + GET_SIZE(FTRP(NEXT_BLKP(bp))); 
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    // 헤더 갱신 
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));    // 푸터 갱신 
        bp = PREV_BLKP(bp);                         // 앞으로 bp 옮겨줘야함 
    } 

    insert_block(bp, size);                         // 연결된 블록 가용리스트 삽입 (coalesce를 하면 무조건 insert가 실행됨) 
    return bp;                                      // bp 반환
} 

static void place(void *bp, size_t asize) { 
    size_t csize = GET_SIZE(HDRP(bp)); 
    // allocate된 블록은 freelist에서 지운다. 
    remove_block(bp); 
    
    // 필요한 블록 이외에 남는게 16바이트 이상이면 - (header,pred,succ,footer 각각 16byte필요) 
    if ((csize - asize) >= (2 * DSIZE)) {       //분할을 진행한다.  
        // 일단 할당블록 처리 
        PUT(HDRP(bp), PACK(asize, 1)); 
        PUT(FTRP(bp), PACK(asize, 1)); 
        bp = NEXT_BLKP(bp);                     //bp를 다음 블록으로 옮김 
        
        // 나머지 사이즈를 free시킨다. 
        PUT(HDRP(bp), PACK(csize - asize, 0)); 
        PUT(FTRP(bp), PACK(csize - asize, 0)); 
        coalesce(bp);                           // 이때 연결되어 있는 게 있을 수 있으므로 coalesce진행 
    }                                           // coalesce 함수에 들어가면 무조건 insert를 하게 됨 
    else { 
        PUT(HDRP(bp), PACK(csize, 1)); 
        PUT(FTRP(bp), PACK(csize, 1)); 
    } 
} 

static void *find_fit(size_t asize) { 
    /* First-fit search */ 

    void *bp;
    int list = 0;
    size_t search = asize;
    
    // 크기에 맞는 클래스부터 찾아야함

    while(list<LISTLIMIT){

        // 다돌았으면 19에는 들어가야하고, 1이나 0이 됐을때 리스트에 블록이 있다면 들어가야함
        if((list==LISTLIMIT-1) || (search<=1) && (segregation_list[list]!=NULL)){ 
            bp = segregation_list[list];                      
            while(bp!=NULL && GET_SIZE(HDRP(bp))<asize){    // 찾는 크기보다 크거나 같은 블록앞에서 멈춤
                bp=SUCC_FREE(bp);                           // 그때까지 next로 갱신
            }
            if(bp!=NULL){                                   // 비었는지 확인
                return bp;
            }            
        }
        // 0 or 1이 될때까지 2로 나누고 list를 ++하면 가용블록리스트의 인덱스를 구할 수 있음
        list++; 
        search >>= 1; 
    }
    return NULL;
} 

static void remove_block(void *bp){ 
    
    size_t search = GET_SIZE(HDRP(bp));
    int list = 0;

    //지우고자 하는 list idx 찾아들어감 
    while((list<LISTLIMIT-1) && (search>1)){
        list++;
        search >>= 1;
    }
    // 끝나면 list가 인덱스
    

    if(PRED_FREE(bp) && SUCC_FREE(bp)){ // 중간에 있을 때
        SUCC_FREE(PRED_FREE(bp)) = SUCC_FREE(bp);
        PRED_FREE(SUCC_FREE(bp)) = PRED_FREE(bp);
    }
    else if(PRED_FREE(bp) && !SUCC_FREE(bp)){   // 마지막일 때
        SUCC_FREE(PRED_FREE(bp)) = NULL;
    }
    else if(!PRED_FREE(bp) && SUCC_FREE(bp)){   // 처음일 때
        PRED_FREE(SUCC_FREE(bp)) = NULL;
        segregation_list[list] = SUCC_FREE(bp);
    }else{
        segregation_list[list] = NULL;
    }

    // 근데 이러면 조건을 3번다 검사해야되네
    // succ부터 검사해서 케이스 나누는게 더 좋은듯

    return;

} 

static void insert_block(void *bp, size_t size){ 
    
    //search_ptr의 값을 저장해놓는 용도(insert_ptr의 부모같음) 
    void *search_ptr;
    void *insert_ptr = NULL;
    size_t search = size;
    int list = 0;

    //segregation_list의 idx를 찾는 과정 
    while((list<LISTLIMIT-1) && (search>1)){
        list++;
        search >>= 1;
    }
    search_ptr = segregation_list[list];
    while (search_ptr!=NULL && GET_SIZE(HDRP(search_ptr))<size)
    {
        insert_ptr = search_ptr;
        search_ptr = SUCC_FREE(search_ptr);
    }
    // 멈추면 작은수(insert) 지나고 같거나 큰수(search) 앞에서 멈춤

    if(insert_ptr){                     // while 돌았음 -> 블록이 있음
                                        // 이전 블록이 있을 때
        if(search_ptr){                     // 다음 블록이 있음 -> 중간                
            SUCC_FREE(insert_ptr) = bp;     // insert와 search사이에 삽입
            PRED_FREE(search_ptr) = bp;
            SUCC_FREE(bp) = search_ptr;
            PRED_FREE(bp) = insert_ptr;
        }
        else{                               // 다음 블록이 없음 -> 마지막
            SUCC_FREE(insert_ptr) = bp;     // insert 다음에 삽입
            PRED_FREE(bp) = insert_ptr;
            SUCC_FREE(bp) = NULL;
        }
    }
    else{                               // 이전 블록이 없을 때
        if(search_ptr){                     // 다음 블록이 있음 -> 루트
            segregation_list[list] = bp;    // search 이전에 삽입
            PRED_FREE(search_ptr) = bp;     // 리스트가 가리키는 루트가 됨
            SUCC_FREE(bp) = search_ptr;
            PRED_FREE(bp) = NULL;
        }
        else{                               // 다음 블록이 없음 -> 빈 리스트
            segregation_list[list] = bp;    // 루트로 설정
            PRED_FREE(bp) = NULL;
            SUCC_FREE(bp) = NULL;
        }
    }
    
    return;

}
