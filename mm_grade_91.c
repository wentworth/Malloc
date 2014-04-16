/*
 * mm.c
 * _______________________________________________________________
 * Dynamically allocate Memory with approaches:
 * 1. Segregated Free list.
 * 2. FILO inserting method.
 * 3. First-fit searching method.
 *
 * Heap structure:
 * ----------------------------------------------------------------
 * |   <1>   |<2>|<3>|                  <4>                   |<5>|
 * ----------------------------------------------------------------
 *               ^
 *               | <-heap_listp always points to here
 *
 * Zone <1>: maintains an area that stores addresses of free list headers
 *           including necessary paddings.
 * Zone <2>: Prologue header - length: WSIZE
 * Zone <3>: Prologue footer - length: WSIZE
 * Zone <4>: Blocks (including necessary paddings)
 * Zone <5>: Epilogue header - length: WSIZE
 *
 *
 * Free Block structure:
 *
 * -----------------------------------------------------------------
 * |header|   Prev-pointer |  Next-pointer |                |footer|
 * -----------------------------------------------------------------
 * header:       4 bytes
 * footer:       4 bytes
 *               header and footer have the same structure with examples
 *               in chapter 9.9 in CSAPP textbook.
 * Prev-Pointer: 8-bytes, used to store the previous free block address
 * Next-Pointer: 8-bytes, used to store the next free block address
 *
 *
 * Principles:
 *
 *        Each blocks shall have a header and a footer which has
 *        the same structure with examples in chapter 9.9 in CSAPP
 *        textbook. All blocks shall be aligned to 8 bytes, and the
 *        minimum size of Block is 3*DSIZE. Free blocks are linked with
 *        each other in multiple free lists, where each list holds roughly
 *        the same size.
 *
 *
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */
/*define if user wants to enter debug mode*/
#define Debugx
/*define if user wants to enter verbose mode (1-verbose output;0-not)*/
#define Verbose     0
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))
/* Define the MAX memory the heap can have*/
#define MAXHEAP (1<<32)
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  168      /* Extend heap by this amount (bytes) */
#define MAXFREESIZE 20      /* max number of freelists*/
#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)        (*(unsigned int *)(p))
#define PUT(p, val)   (*(unsigned int *)(p) = (val))
/* Read and write a 8-bytes pointer to address p*/
#define PUTLP(p, val) (*(void **)(p) =(void *)(val) )
#define GETLP(p)      (*(void **)(p))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
#define NEXT_FREE(bp)  ((void *) (*(unsigned int **)((char*)bp+DSIZE)))
#define PREV_FREE(bp)  ((void *) (*(unsigned int **)(bp)))
/* $end mallocmacros */
/* Free the block header and footer*/
#define FREE_SIZE(bp)  (GET(bp) & ~0x1)
/* Define the free block size (DSIZE) each free list has*/
#define LIST1    3
#define LIST2    4
#define LIST3    5
#define LIST4    6
#define LIST5    7
#define LIST6    8
#define LIST7    9
#define LIST8    10
#define LIST9    12
#define LIST10   16
#define LIST11   32
#define LIST12   64
#define LIST13   128
#define LIST14   256
#define LIST15   512
#define LIST16   1024
#define LIST17   2048



/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
void *freelisthead = 0;       /*Pointer to free list head*/
void *freelisttablehead = 0 ;/*Pointer to free list table head*/


/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);
static int choosefreetable(void *bp);
static int choosefreetable_bysize(int freeblksize);

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    /* Create the initial empty heap */
    size_t freeslistnum;
    int i;
    freeslistnum = DSIZE*((MAXFREESIZE*DSIZE + DSIZE + DSIZE -1)/DSIZE);
    freelisttablehead = (char*)mem_sbrk(freeslistnum)+DSIZE;
    PUT(HDRP(freelisttablehead),PACK(freeslistnum,1));
    PUT(FTRP(freelisttablehead),PACK(freeslistnum,1));
    for (i = 0;i<MAXFREESIZE;i++)
    {
        PUTLP(((char*)freelisttablehead+i*DSIZE),NULL);
    }

    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
	    return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
	    return -1;

    return 0;
}


/*
 * malloc- Allocate memory large enough to store size bytes
 *         align the size inside this function to make sure:
 *         1-at least 3* DSIZE bytes for each block
 *         2- Align to DSIZE bytes
 */
void *malloc (size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    if (heap_listp == 0){
	    mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
	    return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
	    asize = 3*DSIZE; //at least 3*DSIZE for each block
    else
	    asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
	    // Size Adjust

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
	    place(bp, asize);
	    return bp;
    }
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
	    return NULL;
    place(bp, asize);
    #ifdef Debug
    if (Verbose) mm_checkheap(1);
    else mm_checkheap(0);
    #endif
    return bp;

}


/*
 * Insert free list head function
 */
static inline void insertFree(void * bp)
{
    int FreetableN = choosefreetable(bp);
    freelisthead = (void *)GETLP((char*)freelisttablehead +
                                 DSIZE * (FreetableN-1));

    if(bp == freelisthead)
    {   // do nothing, if this is already the first node of free list
        return;
    }
    else if (freelisthead!=NULL) //normal node of free list
    {
        PUTLP(freelisthead,bp);
        PUTLP(((char*)bp+DSIZE),freelisthead);
        freelisthead = bp;
        PUTLP(freelisthead,NULL);
        PUTLP((char*)freelisttablehead + DSIZE * (FreetableN-1),freelisthead);
    }
    else // this is the new first node of free list
    {
        freelisthead = bp;
        PUTLP(freelisthead, NULL);
        PUTLP(((char*)freelisthead+DSIZE),NULL);
        PUTLP((char*)freelisttablehead + DSIZE * (FreetableN-1),freelisthead);
    }
}

/*
 *  choosefreetable:
 *  Choose the most appropriate table number
 *  based on the block pointer as argument
 */

static inline int choosefreetable(void * bp)
{
    int freeblksize;
    int numresult;
    freeblksize = (int)GET_SIZE(HDRP(bp));
    numresult = choosefreetable_bysize(freeblksize);
    return numresult;

}

/*
 *  choosefreetable_bysize:
 *  Choose the most appropriate table number
 *  based on the block size as argument
 */
static inline int choosefreetable_bysize(int freeblksize)
{
    int numresult;
    int temp = freeblksize/DSIZE;
    if (temp<=LIST1)  numresult = 1;
    else if (temp <=LIST2) numresult = 2;
    else if (temp <=LIST3) numresult = 3;
    else if (temp <=LIST4) numresult = 4;
    else if (temp <=LIST5) numresult = 5;
    else if (temp <=LIST6) numresult = 6;
    else if (temp <=LIST7) numresult = 7;
    else if (temp <=LIST8) numresult = 8;
    else if (temp <=LIST9) numresult = 9;
    else if (temp <=LIST10) numresult = 10;
    else if (temp <=LIST11) numresult = 11;
    else if (temp <=LIST12) numresult = 12;
    else if (temp <=LIST13) numresult = 13;
    else if (temp <=LIST14) numresult = 14;
    else if (temp <=LIST15) numresult = 15;
    else if (temp <=LIST16) numresult = 16;
    else if (temp <=LIST17) numresult = 17;

    else numresult =18;
    return numresult;
}

/*
 * deleteFree:
 * Delete one node from the free list
 * and link the pre to next.
 */

static inline void deleteFree(void *bp)
{
    void * pre_f;
    void * next_f;
    int FreetableN = choosefreetable(bp);
    freelisthead = (void *)GETLP((char*)freelisttablehead
                                 + DSIZE * (FreetableN-1));


    pre_f = PREV_FREE(bp);
    next_f= NEXT_FREE(bp);
    if (pre_f!=NULL)
    {
        PUTLP(((char*)pre_f+DSIZE),next_f);
    }
    else
    {
        PUTLP((char*)freelisttablehead + DSIZE * (FreetableN-1),next_f);
    }
    if (next_f!=NULL) PUTLP((next_f),pre_f);
}


/*
 * free---To free a block with necessary inserting & coalescing action
 */
void free (void *ptr) {

	void * new_ptr;
	if (ptr != NULL)
	{
	    size_t fsize = GET_SIZE(HDRP(ptr));

	    PUT(HDRP(ptr), PACK(fsize,0));
            PUT(FTRP(ptr), PACK(fsize,0));
            new_ptr = coalesce(ptr);
            #ifdef Debug
            if (Verbose) mm_checkheap(1);
            else mm_checkheap(0);
            #endif
    	}
    else
    {
        return;
    }
}



/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0)
    {
        free(oldptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL)
    {
        return malloc(size);
    }

       /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(oldptr));
    if (size <= DSIZE)
        size = 3*DSIZE; //size adjust
    else
        size = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);


    if(size <= oldsize)
    {
        return oldptr;
    }
    else
    {
        newptr = malloc(size);
    /* If realloc() fails the original block is left untouched  */
        if(!newptr)
        {
            return 0;
        }
        memcpy(newptr, oldptr, oldsize);
        /* Free the old block. */
        free(oldptr);
        return newptr;
    }

}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */

static void place(void *bp, size_t asize)

{

    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (3*DSIZE)) {
	deleteFree(bp);
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));

	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
	coalesce(bp);

    }
    else {
	deleteFree(bp);
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));

    }
}

/*
 * extend_heap: to extend the heap by 'words' size
 */

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
	return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */

    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
	insertFree(bp);
	return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */

	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	deleteFree(NEXT_BLKP(bp));
    PUT(HDRP(bp), PACK(size,0));
	PUT(FTRP(bp), PACK(size,0));
	insertFree(bp);
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));
	deleteFree(PREV_BLKP(bp));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);
	insertFree(bp);
    }

    else {                                     /* Case 4 */
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
	    GET_SIZE(FTRP(NEXT_BLKP(bp)));
	deleteFree(PREV_BLKP(bp));
	deleteFree(NEXT_BLKP(bp));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);
	insertFree(bp);
    }

    return bp;
}



/*
 * find_fit - Find a fit for a block with asize bytes
 */

static void *find_fit(size_t asize)
{

    /* First fit search */
    void *bp;
    int FreetableN = choosefreetable_bysize((int)asize);
    int i;
    for  (i = FreetableN; i<MAXFREESIZE ;i++ )
     {
         freelisthead = (void *)GETLP((char*)freelisttablehead + DSIZE * (i-1));
         for (bp =freelisthead;
              bp!=NULL && GET_SIZE(HDRP(bp)) > 0;
              bp = NEXT_FREE(bp))
         {

	          if  ( !GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
              {
	              return bp;
	          }

          }
     }
    return NULL; /* No fit */

}
/*
 * printblock - Used for checking only, to print block information
 */

static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;
    mm_checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
       printf("%p: EOL\n", bp);
       return;
    }

}
/*
 * in_heap: used for checking only
 *          Return whether the pointer is in the heap.
 *
 */


static int in_heap(const void *p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}


/*
 * checkFreeBlock: used for checking free blocks only
 *                 print out error information if anything wrong.
 *
 */
static void checkFreeBlock(void *bp)
{

    /*check 5.1: if all the free blocks are freed*/
    if (GET_ALLOC(HDRP(bp)))
        printf("Error: free block %p has not been freed!\n,",bp);

    if (PREV_FREE(bp)!=NULL  && NEXT_FREE(bp)!=NULL )
    {
        /*check 5.2: if all the pointer is within boundary*/
        if ((!in_heap(PREV_FREE(bp))) || (!in_heap(NEXT_FREE(bp))))
        printf("Error: free block pointer %p out of boundary\n",bp);

        /*check 5.3 : if each pointer of free block is correct*/
        if ( NEXT_FREE(PREV_FREE(bp))!=bp || PREV_FREE(NEXT_FREE(bp))!=bp )
            printf("Error:free list is not linked correctly @%p\n",bp);

        if ( NEXT_FREE(bp)==bp || PREV_FREE(bp)==bp  )
            printf("Error:free list is dead-lock(self) linked @%p\n",bp);


    }
}

/*
 * checkblock - Used for checking only, to check block alignment
 *              as well as the header and footer, and boundaries.
 */

static void checkblock(void *bp)
{
    if (!in_heap(bp) )
        printf("Error: %p is out of boundary\n",bp);
    if (GET_SIZE(HDRP(bp)) <3*DSIZE && bp != heap_listp )
        printf("Error: %p has a wrong size\n",bp);
    if ((size_t)bp % DSIZE)
	    printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	    printf("Error: header does not match footer\n");
}

/*
 * mm_checkheap--to chech if the freeblock list and heap structure is OK
 */
int mm_checkheap(int verbose) {
    char *bp = heap_listp;
    void *fp;  /*free block pointer*/
    int index; /*index in the free list*/
    int fblocknumbynormal=0; /*count the free blocks by iteration*/
    int fblocknumbyfreelist=0;/*count the free blocks by list pointer*/

    /*check1:  Prologue block*/
    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) ||
         !GET_ALLOC(HDRP(heap_listp)))
	printf("Bad prologue header\n");

    checkblock(heap_listp);


    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
	     if (verbose)
             printblock(bp);
         /*check2:  If there is consecutive free block*/
	     if (GET_SIZE(HDRP(NEXT_BLKP(bp)))>0 &&
            !GET_ALLOC(HDRP(bp)) && !GET_ALLOC(HDRP(NEXT_BLKP(bp))))
            printf("consecutive free block! @,(%p)",bp);
	     /*check3:  every block's alignment & header-footer & boundaries*/
	     checkblock(bp);
	     if (!GET_ALLOC(HDRP(bp)))
         {
             fblocknumbynormal++;

         }
    }


    if (verbose)
	printblock(bp);
	/*check4:  Epilogue block*/
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	printf("Bad epilogue header\n");

    /*check5: every free block is correct*/
    for  (index = 1; index<MAXFREESIZE ;index++ )
    {
         for (fp = (void *)GETLP((char*)freelisttablehead + DSIZE * (index-1));
              fp!= NULL && GET_SIZE(HDRP(fp)) > 0;
              fp = NEXT_FREE(fp))
         {
            checkFreeBlock(fp);
            fblocknumbyfreelist++;
            /*check 5.4 : if each free block is in the correct free list*/
            if (choosefreetable(fp)!=index)
                printf("The free block %p is in the wrong free list\n",fp);


         }
    }

    /*check 5.5: if freelist is correctly counted by both way*/
    if (fblocknumbyfreelist!=fblocknumbynormal)
    {
        printf("Error: Free blocks counted by iteration does not match");
        printf("those counted by free list pointers\n");
        printf("normal  iteration gives: %d free blocks\n",
                fblocknumbynormal);
        printf("free list pointer gives: %d free blocks\n",
                fblocknumbyfreelist);
    }
    return 0;

}


