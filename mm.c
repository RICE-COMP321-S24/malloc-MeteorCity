
/*
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP3e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"win dian",
	/* First member's full name */
	"John Talghader",
	/* First member's NetID */
	"jat8",
	/* Second member's full name (leave blank if none) */
	"Anjali Yamasani",
	/* Second member's NetID (leave blank if none) */
	"ay50"
};

struct free_block {
	struct free_block *prev;
	struct free_block *next;
};

typedef struct free_block *free_ptr;

/* Define basic constant for the number of size classes in segmented list */
/* Classes are based on total block size, including memory overhead  */
/* {32 - 64}, {65 - 128}, ..., {4097 - inf} */
#define NUM_CLASSES 8

/* Basic constants and macros: */
#define WSIZE	       sizeof(void *) /* Word and header/footer size (bytes) (8) */
#define DSIZE	       (2 * WSIZE)    /* Doubleword size (bytes) (16) */
#define CHUNKSIZE      (1 << 12)      /* Extend heap by this amount (bytes) */
#define MIN_BLOCK_SIZE (2 * DSIZE)    /* Minimum block size (bytes) (32) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)	    (*(uintptr_t *)(p))
#define PUT(p, val) (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)  (GET(p) & ~(WSIZE - 1))
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Determine if prologue or epilogue */
#define IS_FIRST_BLOCK(p) (GET_SIZE(HDRP(PREV_BLKP(p))) == 0)
#define IS_LAST_BLOCK(p)  (GET_SIZE(HDRP(NEXT_BLKP(p))) == 0)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/* Global variables: */
static char *heap_listp; /* Pointer to first block */
static free_ptr fb_list;

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static int get_min_class(size_t asize);
/* static char *get_class_hdr(size_t asize); */
// static void coalesce_helper_back(char *block1, char *block2);
// static void coalesce_helper_front(char *block1, char *block2);
static void insert_node(void *bp);
static void remove_node(void *bp);
static void print_linked_lists();

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp);

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void)
{
	/* Initialize fb_list */
	if ((fb_list = mem_sbrk(NUM_CLASSES * DSIZE)) == (void *)-1)
		return (-1);

	/* Initialize segregated fits free list */
	for (int i = 0; i < NUM_CLASSES; i++) {
		fb_list[i].prev = &fb_list[i];
		fb_list[i].next = &fb_list[i];
	}

	/* Initialize heap */
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return (-1);

	/* Alignment padding */
	PUT(heap_listp, 0);

	/* Prologue header */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));

	/* Prologue footer */
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));

	/* Epilogue header */
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));

	/* Increment the heap_list pointer */
	heap_listp += (2 * WSIZE);

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);
	/* to-do: Put this in the free list? */
	// insert_node(heap_listp);
	print_linked_lists();
	return (0);
}

/*
 * Requires:
 *   size - The size of the payload we're trying to allocate a block for.
 *          Assumes that both pointers are taken into account of in size
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size)
{
	size_t asize;	   /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	printf("Trying to mm_malloc %lu\n", size);
	/* Adjust block size */
	if (size <= DSIZE)
		/* 2 DSIZE for header, footer, and pointers */
		asize = 2 * DSIZE;
	else
		/* Round up to the nearest WSIZE and add DSIZE for hdr and ftr*/
		asize = WSIZE * ((size + DSIZE + (WSIZE - 1)) / WSIZE);

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		printf("Found a fit at %p\n", bp);
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
		return (NULL);
	place(bp, asize);
	return (bp);
}

/*
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));

	/* Make sure ptr points to an allocated block. */
	if (!GET_ALLOC(HDRP(ptr))) {
		printf("Error: Trying to reallocate a free block.\n");
		return NULL;
	}

	oldsize = GET_SIZE(HDRP(ptr)) - DSIZE;
	/* Try to reuse current block if possible. */
	if (oldsize >= size) {
		place(ptr, size);
		return ptr;
	}

	/* Creates a new allocated block and copies over. */
	newptr = mm_malloc(size);

	/* If realloc() fails, the original block is left untouched.  */
	if (newptr == NULL)
		return (NULL);

	/* Copy just the old data, not the old header and footer. */

	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return (newptr);
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp)
{
	size_t size = GET_SIZE(HDRP(bp));
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

	if (prev_alloc && next_alloc) { /* Case 1 */
		insert_node(bp);
		return (bp);
	} else if (prev_alloc && !next_alloc) { /* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		remove_node(NEXT_BLKP(bp));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	} else if (!prev_alloc && next_alloc) { /* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		remove_node(PREV_BLKP(bp));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	} else { /* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		remove_node(NEXT_BLKP(bp));
		remove_node(PREV_BLKP(bp));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	insert_node(bp);
	return (bp);
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words)
{
	size_t size;
	void *bp;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)
		return (NULL);
	printf("Extending heap by %lu\n", size);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));	      /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));	      /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
	insert_node(bp);
	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found.
 */
static void *
find_fit(size_t asize)
{
	int classIdx = get_min_class(asize);
	while (classIdx < NUM_CLASSES) {
		free_ptr head = &fb_list[classIdx];
		free_ptr curr = head->next;
		while (curr != head) {
			if (GET_SIZE(HDRP(curr)) >= asize) {
				return curr;
			}
			curr = curr->next;
		}
		classIdx++;
	}
	return NULL;
	/*
	char *head = get_class_hdr(asize);

	if (head == NULL) {
		return (NULL);
	}
	*/

	/* Iterate through linked list */
	/*
	while (head != NULL) {
		size_t csize = GET_SIZE(head);
		*/

	/* If it can't be housed, increment bp to the next node in LL */
	/*
	if (csize < asize) {
		head = NEXT_LL(head);
	} else {
		break;
	}
}
*/

	/* Return a pointer to the first free block that can house asize */
	/* return (head + WSIZE); Add WSIZE to account for header */
}

/*
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size.
 */
static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));
	if ((csize - asize) >= (MIN_BLOCK_SIZE)) {
		remove_node(bp); // to-do: verify
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		insert_node(bp); // to-do: verify
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		remove_node(bp);
	}
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a search in the free lists for a free block "bp" in the heap.
 */
static bool
isblockinfreelist(void *bp)
{
	for (int i = 0; i < NUM_CLASSES; i++) {
		void *curr = fb_list[i].next;
		// loop through circular linked list for size class i
		while (curr != &fb_list[i]) {
			if (curr == bp) {
				return true;
			}
		}
	}
	return false;
}

/*
 * The remaining routines are heap consistency checker routines.
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp)
{
	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency.
 */
void
checkheap(bool verbose)
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE || !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);

		/* Checks if every free block is actually in the free list. */
		if (!GET_ALLOC(HDRP(bp))) {
			if (!isblockinfreelist(bp)) {
				printf("Free block not in free list.\n");
			}
		}
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");

	// Are there any contiguous free blocks that somehow escaped coalescing?
	// Do the pointers in the free list point to valid free blocks?
	for (int i = 0; i < NUM_CLASSES; i++) {
		free_ptr curr = fb_list[i].next;
		// loop through circular linked list for size class i
		while (curr != &fb_list[i]) {
			if (GET_ALLOC(curr)) {
				printf("Allocated block in free list\n");
			} else {
				// check if prev block is free, given that curr
				// is not the first block
				if (!IS_FIRST_BLOCK(curr) &&
				    !GET_ALLOC(HDRP(PREV_BLKP(curr)))) {
					printf(
					    "Previous free block not coalesced\n");
				}
				/* Check if next block is free, given that curr
				 * is not the last block */
				if (!IS_LAST_BLOCK(curr) &&
				    !GET_ALLOC(HDRP(NEXT_BLKP(curr)))) {
					printf(
					    "Next free block not coalesced\n");
				}
			}
			curr = curr->next;
		}
	}
}

// Do the pointers in the free list point to valid free blocks?
// Do any allocated blocks overlap?
// Do the pointers in a heap block point to valid heap addresses?

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp)
{
	size_t hsize, fsize;
	bool halloc, falloc;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, hsize,
	    (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'));
}

/*
 * Requires:
 *   asize - The size of the block we're trying to allocate
 *
 * Effects:
 *   Returns the int representing the minimum size class asize could fall into
 */
int
get_min_class(size_t asize)
{
	if (asize == 32) {
		return 0;
	}

	/* Subtract 5 from the log since minimum asize is 32 */
	int classIdx = (int)log2(asize - 1) - 5;

	if (classIdx > NUM_CLASSES - 1)
		classIdx = NUM_CLASSES - 1;

	return classIdx;
}

/*
 * Requires:
 *   asize - The size of the block we're trying to allocate
 *
 * Effects:
 *   Returns the head of the linked list that contains a free block with
 *   at least size asize. Returns (null) if one isn't found.
 */
/*
static char *
get_class_hdr(size_t asize) {

}
*/

/*
 * Requires:
 *   bp - Pointer to the free block we're adding to the linked list
 *
 * Effects:
 *   Adds bp to the end of the linked list
 */
static void
insert_node(void *bp)
{
	size_t size = GET_SIZE(HDRP(bp));
	int classIdx = get_min_class(size);
	printf("ClassIdx: %d\n", classIdx);
	free_ptr head = &fb_list[classIdx];
	free_ptr new_block = bp;

	new_block->next = head;
	new_block->prev = head->prev;
	head->prev->next = new_block;
	head->prev = new_block;

	print_linked_lists();
}

/*
 * Requires:
 *   bp - Pointer to the free block we're adding to the linked list
 *
 * Effects:
 *   Removes bp from the linked list
 */
static void
remove_node(void *bp)
{
	size_t size = GET_SIZE(HDRP(bp));
	int classIdx = get_min_class(size);
	free_ptr head = &fb_list[classIdx];
	free_ptr curr = head->next;
	free_ptr remove_block = bp;

	printf("remove_node classIdx=%d\n", classIdx);

	while (curr != head) {
		if (curr == remove_block) {
			remove_block->next->prev = remove_block->prev;
			remove_block->prev->next = remove_block->next;
			remove_block->prev = NULL;
			remove_block->next = NULL;
			return;
		}
		curr = curr->next;
	}
}

static void
print_linked_lists()
{
	for (int i = 0; i < NUM_CLASSES; i++) {
		free_ptr head = &fb_list[i];
		free_ptr curr = head->next;

		printf("Linked List: %d\n", i);
		while (curr != head && curr->next != curr) {
			printf("Next node: %p\n", curr);
			curr = curr->next;
		}
	}
}
