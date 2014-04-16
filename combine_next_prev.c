/*
 * mm.c
 * yzhi - Yiting Zhi
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
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

#define WSIZE 8
#define DSIZE 16
#define CHUNKSIZE (1<<8)
#define BIN 36
#define MSIZE 256

#define verbose 0

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

static char* heap_listp;
static char* heap_head;
static char* tail_block;
static void* bin[BIN];


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
    return p <= (void *)((char *)mem_heap_hi() + WSIZE) && p >= mem_heap_lo();
}

/*
 *  Block Functions
 *  ---------------
 *  TODO: Add your comment describing block functions here.
 *  The functions below act similar to the macros in the book, but calculate
 *  size in multiples of 4 bytes.
 */

static inline size_t max(size_t x, size_t y) {
    return x > y ? x : y;
}

static inline size_t min(size_t x, size_t y) {
	return x > y ? y : x;
}

static inline size_t pack(size_t size, size_t prev_alloc, size_t alloc) {
    return size | (prev_alloc << 1) | alloc;
}

static inline size_t get(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
    return *(size_t *)block;
}

static inline void put(void* block, size_t val) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
    (*(size_t *)block) = val;
}

static inline size_t get_size(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return (get(block) & (~0x7));
}

static inline size_t get_alloc(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
    return (get(block) & 0x1);
}

static inline size_t get_prev_alloc(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return ((get(block) & 0x2) >> 1);
}

static inline void* header_pointer(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return (char *)block - WSIZE;
}

static inline void* footer_pointer(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return (char *)block + get_size(header_pointer(block)) - DSIZE;
}

static inline void* next_block(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return (char *)block + get_size((char *)block - WSIZE);
}

static inline void* prev_block(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return (char *)block - get_size((char *)block - DSIZE);
}

static inline void put_next_ptr(void* block, void* ptr) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	*(size_t *)block = (((*(size_t *)block) >> 32) << 32) | ((size_t)ptr - (size_t)heap_head);
}

static inline void put_prev_ptr(void* block, void* ptr) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	*(size_t *)block = (((*(size_t *)block) << 32) >> 32) | (((size_t)ptr - (size_t)heap_head) << 32);
}

static inline void* next(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return (void *)(((get(block) << 32) >> 32) + (size_t)heap_head);
}

static inline void* prev(void* block) {
	REQUIRES(block != NULL);
	REQUIRES(in_heap(block));
	return (void *)((get(block) >> 32) + (size_t)heap_head);
}

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

 /* bin layout */
 /* 32 40 48 64 ... 248   -- 28 bins */
 /* 256 512 1024 2048 4096 8192 16384    -- 7 bins */

int mm_init(void) {
	if (verbose) printf("init\n");
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) {
        return -1;
    }
    put(heap_listp, 0);
    put(heap_listp + WSIZE, pack(DSIZE, 1, 1));
    put(heap_listp + 2 * WSIZE, pack(DSIZE, 1, 1));
    put(heap_listp + 3 * WSIZE, pack(0, 1, 1));
    heap_head = mem_heap_lo();
    heap_listp += DSIZE;
    tail_block = heap_listp;
    for (int i = 0; i < BIN; i++) {
    	bin[i] = heap_head;
    }
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

static void *extend_heap(size_t words) {
    size_t size;
    char *bp;
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if (verbose) printf("extending... size %ld\n", size);
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }
    put(header_pointer(bp), pack(size, get_alloc(header_pointer(tail_block)), 0));
    put(footer_pointer(bp), pack(size, get_alloc(header_pointer(tail_block)), 0));
    put(header_pointer(next_block(bp)), pack(0, 1, 1));
    tail_block = bp;
    return coalesce(bp);
    
}

static void *coalesce(void *bp) {
	if (verbose) printf("coalescing\n");
	size_t size = get_size(header_pointer(bp));
	size_t prev_alloc = get_prev_alloc(header_pointer(bp));
	size_t next_alloc = get_alloc(header_pointer(next_block(bp)));
	if (prev_alloc && next_alloc) {
		insert(bp);
		return bp;
	}

	if (prev_alloc && !next_alloc) {
		delete(next_block(bp));
		if (tail_block == next_block(bp)) {
			tail_block = bp;
		}
		size += get_size(header_pointer(next_block(bp)));
		put(header_pointer(bp), pack(size, get_prev_alloc(header_pointer(bp)), 0));
		put(footer_pointer(bp), pack(size, get_prev_alloc(header_pointer(bp)), 0));
	}

	else if (!prev_alloc && next_alloc) {
		delete(prev_block(bp));
		if (tail_block == bp) {
			tail_block = prev_block(bp);
		}

		size += get_size(header_pointer(prev_block(bp)));
		bp = prev_block(bp);
		put(header_pointer(bp), pack(size, get_prev_alloc(header_pointer(bp)), 0));
		put(footer_pointer(bp), pack(size, get_prev_alloc(header_pointer(bp)), 0));
		
	}

	else {
		delete(next_block(bp));
		delete(prev_block(bp));
		if (tail_block == bp || tail_block == next_block(bp)) {
			tail_block = prev_block(bp);
		}
		size += get_size(header_pointer(prev_block(bp))) + get_size(header_pointer(next_block(bp)));
		bp = prev_block(bp);
		put(header_pointer(bp), pack(size, get_prev_alloc(header_pointer(bp)), 0));
		put(footer_pointer(bp), pack(size, get_prev_alloc(header_pointer(bp)), 0));
	}
	insert(bp);
	return bp;
}

static void insert(void* bp) {
	size_t asize = get_size(header_pointer(bp));
	size_t size = asize;
	void *bin_pointer = heap_head;
	void *insert_pointer = heap_head;
	int i = 0;
	if (size <= MSIZE) {
		i = (size - 3 * WSIZE) / WSIZE;
		bin_pointer = bin[i];
	}
	else {
		i = (MSIZE - 3 * WSIZE) / WSIZE;
		while (i < BIN - 1 && size > MSIZE) {
			size /= 2;
			i++;
		}
		bin_pointer = bin[i];
		while (bin_pointer != heap_head && asize > get_size(header_pointer(bin_pointer))) {
			insert_pointer = bin_pointer;
			bin_pointer = next(bin_pointer);
		}
	}

	if(verbose) printf("Inserting size: %ld, bin No. %d\n", get_size(header_pointer(bp)), i);
	if (bin_pointer != heap_head) {
		if (insert_pointer != heap_head) {
			put_next_ptr(bp, bin_pointer);
			put_prev_ptr(bin_pointer, bp);
			put_prev_ptr(bp, insert_pointer);
			put_next_ptr(insert_pointer, bp);
		}
		else {
			put_next_ptr(bp, bin_pointer);
			put_prev_ptr(bin_pointer, bp);
			put_prev_ptr(bp, heap_head);
			bin[i] = bp;
		}
	}
	else {
		if (insert_pointer != heap_head) {
			put_next_ptr(bp, heap_head);
			put_prev_ptr(bp, insert_pointer);
			put_next_ptr(insert_pointer, bp);
		}
		else {
			put_next_ptr(bp, heap_head);
			put_prev_ptr(bp, heap_head);
			bin[i] = bp;
		}
	}
}

static void delete(void* bp) {
	if(verbose) printf("Deleting size: %p  %ld\n", bp, get_size(header_pointer(bp)));
	size_t size = get_size(header_pointer(bp));
	int i = 0;
	if (size <= MSIZE) {
		i = (size - 3 * WSIZE) / WSIZE;
	}
	else {
		i = (MSIZE - 3 * WSIZE) / WSIZE;
		while (i < BIN - 1 && size > MSIZE) {
			size /= 2;
			i++;
		}
	}
	if (verbose) printf("next block: %p; previous block: %p\n", next(bp), prev(bp));
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
	if (verbose) {
		printf("----------------------\n");
    	printf("malloc: size = %ld\n", size);
    //checkheap(1);  // Let's make sure the heap is ok!
	    for (int i = 0; i < BIN; i++) {
	    	if (bin[i] != heap_head)
	    		printf("i: %d,  %p,  size: %ld\n", i, bin[i], get_size(header_pointer((void *)bin[i])));
	    }
	}

    //size = size;
    size_t asize;
    size_t extendsize;
    void *bp;

    if (size <= 0) {
    	return NULL;
    }

    if (size <= DSIZE) {
    	asize = 3 * WSIZE;
    }
    else {
    	asize = WSIZE * ((size + WSIZE + WSIZE - 1) / WSIZE);
    }
    if ((bp = find_fit(asize)) == NULL) {
    	extendsize = max(asize, CHUNKSIZE);
    	if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
    		return NULL;
    	}
    }
    place(bp, asize);
    return bp;
}

void *find_fit(size_t asize) {
	if (verbose) printf("find fit size %ld....", asize);
	int i = 0;
	size_t size = asize;
	void *bp = heap_head;
	if (size <= MSIZE) {
		i = (size - 3 * WSIZE) / WSIZE;
	}
	else {
		i = (MSIZE - 3 * WSIZE) / WSIZE;
		while (i < BIN - 1 && size > MSIZE) {
			size /= 2;
			i++;
		}
	}
	while (i < BIN) {
		if (bin[i] != heap_head) {
			bp = bin[i];
			while (bp != heap_head && asize > get_size(header_pointer(bp))) {
				bp = next(bp);
			}
			if (bp != heap_head) {
				if (verbose) printf("found bin No. %d\n", i);
				return bp;
			}
		}
		i++;
	}
	if (verbose) printf("not found\n");
	return NULL;
}

void place(void *bp, size_t asize) {
	if (verbose) printf("place size %ld\n", asize);
	size_t size, oldsize;
	oldsize = get_size(header_pointer(bp));
	size = oldsize - asize;
	delete(bp);
	if (size >= 3 * WSIZE) {
		put(header_pointer(bp), pack(asize, get_prev_alloc(header_pointer(bp)), 1));
		put(header_pointer(next_block(bp)), pack(size, 1, 0));
		put(footer_pointer(next_block(bp)), pack(size, 1, 0));
		insert(next_block(bp));
		if (bp == tail_block) {
			tail_block = next_block(bp);
		}
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
	if (ptr == 0) {
		return;
	}
	if (!in_heap(ptr)) {
		//if (verbose) printf("free a pointer not in heap\n");
		return;
	}
	if (!aligned(ptr)) {
		//if (verbose) printf("free pointer is not aligned\n");
		return;
	}
	else if (!get_alloc(header_pointer(ptr))) {
		//if (verbose) printf("Block is not allocated\n");
		return;
	}
	if (verbose) {
		printf("---------------\n");
		printf("free: %ld\n", get_size(header_pointer(ptr)));
		for (int i = 0; i < BIN; i++) {
	    	if (bin[i] != heap_head)
	    		printf("i: %d,  %p,  size: %ld\n", i, bin[i], get_size(header_pointer(bin[i])));
	    }
	}

   size_t size = get_size(header_pointer(ptr));

   put(header_pointer(ptr), pack(size, get_prev_alloc(header_pointer(ptr)), 0));
   put(footer_pointer(ptr), pack(size, get_prev_alloc(header_pointer(ptr)), 0));
   if (next_block(ptr) != (char *)mem_heap_hi() + WSIZE) {
   	put(header_pointer(next_block(ptr)), pack(get_size(header_pointer(next_block(ptr))), 0, get_alloc(header_pointer(next_block(ptr)))));
   }
   coalesce(ptr);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
	if (verbose) {
		printf("---------------\n");
		printf("realloc: %p size %ld\n", oldptr, size);
		for (int i = 0; i < BIN; i++) {
	    	if (bin[i] != heap_head)
	    		printf("i: %d,  %p,  size: %ld\n", i, bin[i], get_size(header_pointer(bin[i])));
	    }
	}
	if (heap_listp == 0) {
		mm_init();
	}
    size_t oldsize, remain, asize;
    void *newptr;

    if (size == 0) {
    	free(oldptr);
    	return 0;
    }

    if (oldptr == NULL) {
    	return malloc(size);
    }
    if (!aligned(oldptr)) {
		return 0;
	}
	if (!in_heap(oldptr)) {
		return 0;
	}
	if (size <= DSIZE) {
    	size = 3 * WSIZE;
    }
    else {
    	size = WSIZE * ((size + WSIZE + WSIZE - 1) / WSIZE);
    }
	oldsize = get_size(header_pointer(oldptr));
	if (size <= oldsize) {
		remain = oldsize - size;
		if (remain >= 3 * WSIZE) {
			put(header_pointer(oldptr), pack(size, get_prev_alloc(header_pointer(oldptr)), 1));
			put(header_pointer(next_block(oldptr)), pack(remain, 1, 0));
			put(footer_pointer(next_block(oldptr)), pack(remain, 1, 0));
			char *p = next_block(oldptr);
			if (p != (char *)mem_heap_hi() + WSIZE) {
				put(header_pointer(next_block(p)), pack(get_size(header_pointer(next_block(p))), 0, get_alloc(header_pointer(next_block(p)))));
			}
			insert(next_block(oldptr));
			if (tail_block == oldptr) {
				tail_block = next_block(oldptr);
			}
		}
		else {
			put(header_pointer(oldptr), pack(oldsize, get_prev_alloc(header_pointer(oldptr)), 1));
			put(header_pointer(next_block(oldptr)), pack(get_size(header_pointer(next_block(oldptr))), 1, get_alloc(header_pointer(next_block(oldptr)))));
		}
		return oldptr;
	}
	
	else {
		void* nextblock = next_block(oldptr);
		if(!get_alloc(header_pointer(nextblock))) {
			remain = size - oldsize;
			asize = get_size(header_pointer(nextblock));
			remain -= asize;
			if ((signed long)remain < 0) {
				delete(nextblock);
				asize += oldsize;
				remain = asize - size;
				if (remain >= 3 * WSIZE) {
					put(header_pointer(oldptr), pack(size, get_prev_alloc(header_pointer(oldptr)), 1));
					put(header_pointer(next_block(oldptr)), pack(remain, 1, 0));
					put(footer_pointer(next_block(oldptr)), pack(remain, 1, 0));
					insert(next_block(oldptr));
					if (tail_block == nextblock) {
						tail_block = next_block(oldptr);
					}
				}
				else {
					put(header_pointer(oldptr), pack(asize, get_prev_alloc(header_pointer(oldptr)), 1));
					put(header_pointer(next_block(oldptr)), pack(get_size(header_pointer(next_block(oldptr))), 1, get_alloc(header_pointer(next_block(oldptr)))));
					if (tail_block == nextblock) {
						tail_block = oldptr;
					}
				}
				return oldptr;
			}
		}
	}
	
	newptr = malloc(size);
	if (!newptr) {
		return 0;
	}
	memcpy(newptr, oldptr, oldsize);
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

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int v) {
    if (v) {
    	void *ptr = heap_listp;
    	if ((long)get_size((char *)ptr - 3 * WSIZE) != DSIZE ||
    		(long)get_size((char *)ptr - DSIZE) != DSIZE ||
    		!get_alloc((char *)ptr - 3 * WSIZE) ||
    		!get_alloc((char *)ptr - DSIZE)) {
    		printf("prologue block corrupted\n");
    		return 1;
    	}
    	while (get_size(header_pointer(ptr)) > 0) {
    		if (!aligned(ptr)) {
    			printf("not aligned %ld\n", (long)ptr);
    			return 1;
    		}
    		
    		ptr = next_block(ptr);
    	}
    	if (get((char *)ptr - WSIZE) != pack(0, 1, 1)) {

    		printf("Epilogue block corrupted\n");
    		return 1;
    	}
    }
    return 0;
}