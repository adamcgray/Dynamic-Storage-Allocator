/*
 * mm.c
 * yzhi - Yiting Zhi
 *
 * Segregated fit method is used to do the dynamic memory allocation.
 * The allocator maintains an array of free lists. Each free list is 
 * associated with a size class (bin).
 *
 * < Bin Layout >
 * 16 24 32 40 48 64 ... 248 256   		-- 31 fixed size bins 
 * 256 512 1024 2048 4096 8192 16384    -- 7 unfixed size bins
 *
 * < Free Block Layout > (min size: 16 byte)
 * - - - - H H H H  4 byte header with prev_alloc and alloc bit
 * N N N N P P P P  4 byte next pointer offset, 4 byte prev pointer offset
 * F F F F - - - -  4 byte footer with prev_alloc and alloc bit
 * 
 * < Allocated Block Layout >
 * - - - - H H H H
 * X X X X X X X X
 * X X X X - - - -  no need to maintain a footer
 *
 * < Allocation >
 * Determine the bin according to the size of request and do a best-fit
 * search in the free list. The free list is sorted in decreasing order
 * so the best-fit search can be better than O(n).
 *
 * < Free >
 * Put the pointer back to the free list by determine the size and insert
 * the pointer in a decreasing order. Coalesce afterwards.
 *
 * < Realloc >
 * Determine if the physical next block is free. If so, calculate if merging
 * two blocks can hold the given size.
 *
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

#define WSIZE 8
#define DSIZE 16
#define HSIZE 4
#define CHUNKSIZE (1<<8)
#define BIN 38
#define MSIZE 256
#define MINSIZE 12


/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

/* first block in heap */
static char* heap_listp;
/* start of the heap */
static char* heap_head;
/* bin array of linked lists*/
static void** bin;


/*
 *  Helper functions
 *  ----------------
 */

// Align p to a multiple of w bytes
static inline void* align(const void const* p, unsigned char w) {
    return (void*)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

// Check if the given pointer is 8-byte aligned
static inline int aligned(const void const* p) {
    return align(p, 8) == p;
}

// Return whether the pointer is in the heap.
static int in_heap(const void* p) {
    return p <= (void *)((char *)mem_heap_hi() + 1) && p >= mem_heap_lo();
}

/*
 *  Block Functions
 */

/* Calculate the bigger value of two values */
static inline size_t max(size_t x, size_t y) {
    return x > y ? x : y;
}

/* calculate the smaller value of two values */
static inline size_t min(size_t x, size_t y) {
	return x > y ? y : x;
}

/* Pack size, previous alloc bit and alloc bit into a word */
static inline size_t pack(size_t size, size_t prev_alloc, size_t alloc) {
    return size | (prev_alloc << 1) | alloc;
}

/* Read a word at address block */
static inline unsigned int get(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
    return *(unsigned int*)block;
}

/* Put a 4 byte header at address block aligned with 4*/
static inline void put(void* block, size_t val) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	(*(unsigned int *)block) = (unsigned int)val;
}

/* Read the size of header at address block */
static inline unsigned int get_size(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return get(block) & ~0x7;
}

/* Read the alloc bit at address block */
static inline size_t get_alloc(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
    return (get(block) & 0x1);
}

/* Read the previous alloc bit at address block */
static inline size_t get_prev_alloc(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return ((get(block) & 0x2) >> 1);
}

/* Given block pointer, compute address of its header */
static inline void* header_pointer(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return (char *)block - HSIZE;
}

/* Given block pointer, compute address of its footer */
static inline void* footer_pointer(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return (char *)block + get_size(header_pointer(block)) - WSIZE;
}

/* Given block pointer, compute the address of its next physical block */
static inline void* next_block(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return (char *)block + get_size(header_pointer(block));
}

/* Given block pointer, compute the address of its previous physical block */
static inline void* prev_block(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return (char *)block - get_size((char *)block - WSIZE);
}

/* Put the 4 byte next pointer offset value at address block */
static inline void put_next_ptr(void* block, void* ptr) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	*(unsigned int *)block = (unsigned int)((size_t)ptr - (size_t)heap_head);
}

/* Put the 4 byte previous pointer offset value at address block */
static inline void put_prev_ptr(void* block, void* ptr) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	*(unsigned int *)((char *)block + HSIZE) = (size_t)ptr - (size_t)heap_head;
}

/* Get the next block in linked list */
static inline void* next(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return (void *)(*(unsigned int *)block + (size_t)heap_head);
}

/* Get the previous block in linked list */
static inline void* prev(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return (void *)(*(unsigned int *)((char *)block + HSIZE) + (size_t)heap_head);
}

/* Helper functions*/
static void insert(void*);
static void delete(void*);
static void *extend_heap(size_t);
static void *coalesce(void*);
static void *find_fit(size_t);
static void place(void*, size_t);

/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
	/* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(DSIZE + BIN * WSIZE)) == (void *)-1) {
        return -1;
    }
    /* Put the bin list pointer onto the heap */
    bin = (void **)heap_listp;
    heap_head = mem_heap_lo(); /* Maintain the heap start address */
    /* Initialize the bin list pointers */
    for (int i = 0; i < BIN; i++) {
    	bin[i] = heap_head;
    }
    heap_listp += BIN * WSIZE;
    put(heap_listp, 0); /* Alignment Padding */
    put(heap_listp + 1 * HSIZE, pack(WSIZE, 1, 1)); /* Prologue header */
    put(heap_listp + 2 * HSIZE, pack(WSIZE, 1, 1)); /* Prodogue header */
    put(heap_listp + 3 * HSIZE, pack(0, 1, 1));		/* Epilogue header */
    heap_listp += WSIZE;
    /* Extend the empty head with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

static void *extend_heap(size_t words) {
    size_t size;
    char *bp;
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }
    /* Initialze free block header/footer and the epilogue header */
    /* Free block header */
    put(header_pointer(bp), pack(size, get_prev_alloc(header_pointer(bp)), 0));
    /* Free block footer */
    put(footer_pointer(bp), pack(size, get_prev_alloc(header_pointer(bp)), 0));
    /* New epilogue header */
    put(header_pointer(next_block(bp)), pack(0, 0, 1));

    /* Coalesce if the previous block was free */
    return coalesce(bp);
    
}

static void *coalesce(void *bp) {
	size_t size = get_size(header_pointer(bp));
	size_t prev_alloc = get_prev_alloc(header_pointer(bp));
	size_t next_alloc = get_alloc(header_pointer(next_block(bp)));
	if (prev_alloc && next_alloc) {			/* Case 1 */
		insert(bp);
		return bp;
	}

	if (prev_alloc && !next_alloc) {		/* Case 2 */
		delete(next_block(bp));
		size += get_size(header_pointer(next_block(bp)));
		put(header_pointer(bp), pack(size, get_prev_alloc(header_pointer(bp)), 0));
		put(footer_pointer(bp), pack(size, get_prev_alloc(header_pointer(bp)), 0));
	}

	else if (!prev_alloc && next_alloc) {	/* Case 3 */
		delete(prev_block(bp));
		size += get_size(header_pointer(prev_block(bp)));
		bp = prev_block(bp);
		put(header_pointer(bp), pack(size, get_prev_alloc(header_pointer(bp)), 0));
		put(footer_pointer(bp), pack(size, get_prev_alloc(header_pointer(bp)), 0));
		
	}

	else {									/* Case 4 */
		delete(next_block(bp));
		delete(prev_block(bp));
		size += get_size(header_pointer(prev_block(bp))) + get_size(header_pointer(next_block(bp)));
		bp = prev_block(bp);
		put(header_pointer(bp), pack(size, get_prev_alloc(header_pointer(bp)), 0));
		put(footer_pointer(bp), pack(size, get_prev_alloc(header_pointer(bp)), 0));
	}
	insert(bp);
	return bp;
}

/* Insert the pointer into a specific bin */
static void insert(void* bp) {
	size_t asize = get_size(header_pointer(bp));
	size_t size = asize;
	void *bin_pointer = heap_head;
	void *insert_pointer = heap_head;
	int i = 0;
	/* Determine a correct bin */
	if (size <= MSIZE) {
		i = (size - DSIZE) / WSIZE;
		bin_pointer = bin[i];
	}
	else {
		i = (MSIZE - DSIZE) / WSIZE;
		while (i < BIN - 1 && size > MSIZE) {
			size /= 2;
			i++;
		}
		bin_pointer = bin[i];
		/* Find a proper location for insertion */
		while (bin_pointer != heap_head && asize > get_size(header_pointer(bin_pointer))) {
			insert_pointer = bin_pointer;
			bin_pointer = next(bin_pointer);
		}
	}
	if (bin_pointer != heap_head) {
		/* Insert a pointer between two pointers */
		if (insert_pointer != heap_head) {
			put_next_ptr(bp, bin_pointer);
			put_prev_ptr(bin_pointer, bp);
			put_prev_ptr(bp, insert_pointer);
			put_next_ptr(insert_pointer, bp);
		}
		/* Insert a pointer after bin pointer */
		else {
			put_next_ptr(bp, bin_pointer);
			put_prev_ptr(bin_pointer, bp);
			put_prev_ptr(bp, heap_head);
			bin[i] = bp;
		}
	}
	else {
		/* Insert a pointer before a pointer */
		if (insert_pointer != heap_head) {
			put_next_ptr(bp, heap_head);
			put_prev_ptr(bp, insert_pointer);
			put_next_ptr(insert_pointer, bp);
		}
		/* Insert a pointer to the bin */
		else {
			put_next_ptr(bp, heap_head);
			put_prev_ptr(bp, heap_head);
			bin[i] = bp;
		}
	}
}

/* Delete a pointer in the bin */
static void delete(void* bp) {
	size_t size = get_size(header_pointer(bp));
	int i = 0;
	/* Determine a correct bin */
	if (size <= MSIZE) {
		i = (size - DSIZE) / WSIZE;
	}
	else {
		i = (MSIZE - DSIZE) / WSIZE;
		while (i < BIN - 1 && size > MSIZE) {
			size /= 2;
			i++;
		}
	}
	if (next(bp) != heap_head) {
		if (prev(bp) != heap_head) {
			put_prev_ptr(next(bp), prev(bp));
			put_next_ptr(prev(bp), next(bp));
		}
		else {
			put_prev_ptr(next(bp), heap_head);
			bin[i] = next(bp);
		}
	}
	else {
		if (prev(bp) != heap_head) {
			put_next_ptr(prev(bp), heap_head);
		}
		else {
			bin[i] = heap_head;
		}
	}
}
/*
 * malloc
 */

void *malloc (size_t size) {
    //checkheap(1);
    size_t asize;		/* Adjusted block size */
    size_t extendsize;	/* Amount to extend heap if no fit */
    void *bp;
    /* Ignore spurious requests */
    if (size <= 0) {
    	return NULL;
    }
    /* Adjust block size to include overhead and alignment reqs */
    if (size <= MINSIZE) {
    	asize = DSIZE;
    }
    else {
    	asize = WSIZE * ((size + HSIZE + WSIZE - 1) / WSIZE);
    }
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) == NULL) {
    	/* No fit found. Get more memory and place the block */
    	extendsize = max(asize, CHUNKSIZE);
    	if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
    		return NULL;
    	}
    }
    place(bp, asize);
    return bp;
}

void *find_fit(size_t asize) {
	int i = 0;
	size_t size = asize;
	void *bp = heap_head;
	/* Find appropiate bin for the size */
	if (size <= MSIZE) {
		i = (size - DSIZE) / WSIZE;
	}
	else {
		i = (MSIZE - DSIZE) / WSIZE;
		while (i < BIN - 1 && size > MSIZE) {
			size /= 2;
			i++;
		}
	}
	/* Find the best-fit in the free list */
	while (i < BIN) {
		if (bin[i] != heap_head) {
			bp = bin[i];
			while (bp != heap_head && asize > get_size(header_pointer(bp))) {
				bp = next(bp);
			}
			if (bp != heap_head) {
				return bp;
			}
		}
		i++;
	}
	return NULL;
}

void place(void *bp, size_t asize) {
	size_t size, oldsize;
	oldsize = get_size(header_pointer(bp));
	size = oldsize - asize;
	delete(bp);
	/* If a free list can be splited, split the list and insert it back */
	if (size >= DSIZE) {
		put(header_pointer(bp), pack(asize, get_prev_alloc(header_pointer(bp)), 1));
		put(header_pointer(next_block(bp)), pack(size, 1, 0));
		put(footer_pointer(next_block(bp)), pack(size, 1, 0));		
		insert(next_block(bp));
	}
	else {
		put(header_pointer(bp), pack(oldsize, get_prev_alloc(header_pointer(bp)), 1));
		put(header_pointer(next_block(bp)), pack(get_size(header_pointer(next_block(bp))), 1, get_alloc(header_pointer(next_block(bp)))));
	}
}


/*
 * free
 */
void free (void *ptr) {
	/* Determine if the pointer is null */
	if (ptr == 0) {
		return;
	}
	/* Determine if the pointer is in heap */
	if (!in_heap(ptr)) {
		return;
	}
	/* Determine if the pointer is aligned */
	if (!aligned(ptr)) {
		return;
	}
	/* Determine if the pointer can be freed */
	else if (!get_alloc(header_pointer(ptr))) {
		return;
	}
   size_t size = get_size(header_pointer(ptr));
   /* Set the alloc block */
   put(header_pointer(ptr), pack(size, get_prev_alloc(header_pointer(ptr)), 0));
   put(footer_pointer(ptr), pack(size, get_prev_alloc(header_pointer(ptr)), 0));
   /* Set the next block's prev alloc block */
   if (next_block(ptr) != (char *)mem_heap_hi() + WSIZE) {
   	put(header_pointer(next_block(ptr)), pack(get_size(header_pointer(next_block(ptr))), 0, get_alloc(header_pointer(next_block(ptr)))));
   }
   coalesce(ptr);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
	if (heap_listp == 0) {
		mm_init();
	}
    size_t oldsize, remain, asize;
    void *newptr;
    /* If size is 0, free the pointer */
    if (size == 0) {
    	free(oldptr);
    	return 0;
    }
    /* If pointer is NULL, allocate the block */
    if (oldptr == NULL) {
    	return malloc(size);
    }
    if (!aligned(oldptr)) {
		return 0;
	}
	if (!in_heap(oldptr)) {
		return 0;
	}
	/* Resize the size to aligned block */
	if (size <= MINSIZE) {
    	size = DSIZE;
    }
    else {
    	size = WSIZE * ((size + HSIZE + WSIZE - 1) / WSIZE);
    }
    /* Get the size of the free list */
	oldsize = get_size(header_pointer(oldptr));
	/* If the free block can fit the allocated bits */
	if (size <= oldsize) {
		remain = oldsize - size;
		/* If the block can be splited */
		if (remain >= DSIZE) {
			put(header_pointer(oldptr), pack(size, get_prev_alloc(header_pointer(oldptr)), 1));
			put(header_pointer(next_block(oldptr)), pack(remain, 1, 0));
			put(footer_pointer(next_block(oldptr)), pack(remain, 1, 0));
			char *p = next_block(oldptr);
			/* Set the next block's prev alloc bit */
			if (p != (char *)mem_heap_hi() + WSIZE) {
				put(header_pointer(next_block(p)), pack(get_size(header_pointer(next_block(p))), 0, get_alloc(header_pointer(next_block(p)))));
			}
			insert(next_block(oldptr));
		}
		else {
			put(header_pointer(oldptr), pack(oldsize, get_prev_alloc(header_pointer(oldptr)), 1));
			put(header_pointer(next_block(oldptr)), pack(get_size(header_pointer(next_block(oldptr))), 1, get_alloc(header_pointer(next_block(oldptr)))));
		}
		return oldptr;
	}
	/* Check if coalesce with next block, the block can fit */
	else {
		void* nextblock = next_block(oldptr);
		/* Check if next block is free */
		if(!get_alloc(header_pointer(nextblock))) {
			remain = size - oldsize;
			asize = get_size(header_pointer(nextblock));
			remain -= asize;
			/* If the size is enough */
			if ((signed long)remain < 0) {
				delete(nextblock);
				asize += oldsize;
				remain = asize - size;
				/* If the block can be splited */
				if (remain >= DSIZE) {
					put(header_pointer(oldptr), pack(size, get_prev_alloc(header_pointer(oldptr)), 1));
					put(header_pointer(next_block(oldptr)), pack(remain, 1, 0));
					put(footer_pointer(next_block(oldptr)), pack(remain, 1, 0));
					insert(next_block(oldptr));
				}
				else {
					put(header_pointer(oldptr), pack(asize, get_prev_alloc(header_pointer(oldptr)), 1));
					put(header_pointer(next_block(oldptr)), pack(get_size(header_pointer(next_block(oldptr))), 1, get_alloc(header_pointer(next_block(oldptr)))));
				}
				return oldptr;
			}
		}
	}
	/* Allocate a new block for it */
	newptr = malloc(size);
	if (!newptr) {
		return 0;
	}
	/* Copy the data to the new pointer */
	memcpy(newptr, oldptr, oldsize);
	/* Free the old pointer */
	free(oldptr);
	return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;
    newptr = malloc(bytes);
    memset(newptr, 0, bytes);
    return newptr;
}

/* Returns 0 if no errors were found, otherwise returns the error */
int mm_checkheap(int verbose) {
	if (verbose) {
	  	void *ptr = heap_listp;
	  	int cnt = 0;
	  	/* Check prologue block */
	  	if (get((char *)ptr - HSIZE) != pack(WSIZE, 1, 1)) {
	  		printf("Prologue block corrupted!, %u\n", get((char *)ptr + HSIZE));
	  		exit(1);
	  	}
	  	/* Check the heap */
	  	while (get_size(header_pointer(ptr)) > 0) {
	  		/* Check if the pointer is aligned */
	  		if (!aligned(ptr)) {
	  			printf("Pointer not aligned: %ld\n", (long)ptr);
	  			exit(1);
	  		}
	  		/* Check alloc bit is consistent */
	  		if (!get_alloc(header_pointer(ptr))) {
	  			cnt ++;
	  			if (get_prev_alloc(header_pointer(next_block(ptr)))) {
	  				printf("Prev alloc error\n");
		  			printf("free heap: %p size=%u\n", ptr, get_size(header_pointer(ptr)));
	  				exit(1);
	  			}
	  		}
	  		/* Check prev alloc bit is consistent */
	  		else {
	  			if (!get_prev_alloc(header_pointer(next_block(ptr)))) {
	  				printf("Prev alloc error. Should be allocated.\n");
	  				printf("%p next=%p prev_alloc=%lu size=%u\n", ptr, next_block(ptr), get_prev_alloc(header_pointer(next_block(ptr))),
	  					get_size(header_pointer(next_block(ptr))));
	  				exit(1);
	  			}
	  		}
	  		ptr = next_block(ptr);
	  	}
	  	/* Check epilogue block */
	  	if (get_size(header_pointer(ptr)) != 0) {
	  		printf("Epilogue block corrupted!\n");
	  		exit(1);
	  	}
	  	/* Check the free list */
	  	for (int i = 0; i < BIN; i++) {
	  		ptr = bin[i];
	  		while(ptr != heap_head) {
	  			cnt --;
	  			if (next(ptr) != heap_head) {
	  				/* Check next/previous pointers are consistent */
	  				if (ptr != (void *)(*(unsigned int *)((char *)next(ptr) + HSIZE) + (size_t)heap_head)) {
	  					printf("Next pointers are not consistent: %p\n", ptr);
	  					exit(1);
	  				}
	  			}
	  			if (prev(ptr) != heap_head) {
	  				if (ptr != (void *)(*(unsigned int *)prev(ptr) + (size_t)heap_head)) {
	  					printf("Prev pointers are not consistent: %p\n", ptr);
	  					exit(1);
	  				}
	  			}
	  			/* Check the size of pointer in a same bin */
	  			if (next(ptr) != heap_head && i < 31) {
	  				if (get_size(header_pointer(ptr)) != get_size(header_pointer(next(ptr)))) {
	  					printf("Free block in same bin size doesn't match, %u, %u\n", get_size(header_pointer(ptr)), get_size(header_pointer(next(ptr))));
	  					exit(1);
	  				}
	  			}
	  			ptr = next(ptr);
	  		}
	  	}
	  	/* Count free blocks if they match */
	  	if (cnt != 0) {
	  		printf("Free block number error!\n");
	  		exit(1);
	  	}
  }
  return 0;
}