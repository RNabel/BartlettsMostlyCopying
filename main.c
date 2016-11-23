#include <stdio.h>
#include <stdlib.h>

/* This module implements garbage collected storage for C programs using the
"mostly-copying" garbage collection algorithm.
Copyright (c) 1987, Digitial Equipment Corp.
The module is initialized by calling:
gcinit( <heap size>, <stack base>, [ <global>, ... ,] NULL )
where <heap size> is the size of the heap in bytes, and <stack base> is
the address of the first word of the stack which could contain a pointer
to a heap allocated object. Following this are zero or more addresses of
global cells which will contain pointers to garbage collected objects.
This list is terminated by NULL.
Once initialized, storage is allocated by calling:
gcalloc( <bytes>, <pointers> )
where <bytes> is size of the object in bytes, and <pointers> is the number
of pointers into the heap which are contained in the object. The pointers
are expected to be at the start of the object. The function will return a
pointer to the data structure with its pointer cells initialized to NULL.
For example, an instance of the structure:

 struct symbol {
    struct *symbol next;
    char name[10];
}

could be allocated by:
    sp = (symbol*)gcalloc( sizeof( symbol ), 1 );

When the garbage collector is invoked, it will search the processor’s
registers, the stack, and the global pointers for "hints" as to what
storage is still accessible. The hints from the registers and stack will
be used to decide which storage should be left in place. Note that objects
which are referenced by global pointers might be relocated, in which case
the pointer value will be modified.

N.B. This code assumes that pointers and integers are 32-bits long. It
also handles a variable number of arguments in a machine dependent
manner. Define the variable VAX for VAX code, or TITAN for Titan
code.
*/

/* Exported items. */
typedef int *GCP; /* Type definition for a pointer to a garbage
collected object. */
//extern gcinit( /* <heap size in bytes>, <address of stack base>,
//[ <address of global ptr>, ...] NULL */ );

extern GCP gcalloc(size_t i, int i1);
/* External definitions */

/* The heap consists of a contiguous set of pages of memory. */
int firstheappage, /* Page # of first heap page */
        lastheappage, /* Page # of last heap page */
        heappages, /* # of pages in the heap */
        freewords, /* # words left on the current page */
        *freep, /* Ptr to the first free word on the current page */
        allocatedpages, /* # of pages currently allocated for storage */
        freepage, /* First possible free page */
        *space, /* Space number for each page */
        *link, /* Page link for each page */
        *type, /* Type of object allocated on the page */
        queue_head, /* Head of list of pages */
        queue_tail, /* Tail of list of pages */
        current_space, /* Current space number */
        next_space, /* Next space number */
        globals; /* # of global ptr’s at globalp */
unsigned *stackbase; /* Current base of the stack */
GCP *globalp; /* Ptr to global area containing pointers */
/* Page type definitions */
#define OBJECT 0
#define CONTINUED 1
/* PAGEBYTES controls the number of bytes/page */
#define PAGEBYTES 512
#define PAGEWORDS (PAGEBYTES/sizeof(int))
#define WORDBYTES (sizeof(int))
#define STACKINC 4
/* Page number <--> pointer conversion is done by the following defines */
#define PAGE_to_GCP(p) ((GCP) ((p) *PAGEBYTES))
#define GCP_to_PAGE(p) (((int)p) / PAGEBYTES)

/* Objects which are allocated in the heap have a one word header. The
form of the header is:
31            17 16             1 0
+---------------+----------------+-+
| # ptrs in obj | # words in obj |1|
+---------------+----------------+-+
|           user data              | <-- user data starts here. GCP
                .                     ptrs come first
                .
                .
|                                  |
+----------------------------------+

The number of words in the object count INCLUDES one word for the header
and INCLUDES the words occupied by pointers.
When an object is forwarded, the header will be replaced by the pointer to
the new object which will have bit 0 equal to 0.
*/
#define MAKE_HEADER(words, ptrs) ((ptrs)<<17 | (words)<<1 | 1)
#define FORWARDED(header) (((header) & 1) == 0)
#define HEADER_PTRS(header) ((header)>>17 & 0x7FFF)
#define HEADER_WORDS(header) ((header)>>1 & 0xFFFF)
#define HEADER_BYTES(header) (((header)>>1 & 0xFFFF)*WORDBYTES)
/* Garbage collector */
/* A page index is advanced by the following function */
int next_page(int page) {
    if (page == lastheappage) return (firstheappage);
    return (page + 1);
}

/* A page is added to the page queue by the following function. */
void queue(int page) {
    if (queue_head != 0)
        link[queue_tail] = page;
    else
        queue_head = page;
    link[page] = 0;
    queue_tail = page;
}

/* A pointer is moved by the following function. */
GCP move(GCP cp)
/* cp:  Pointer to an object */
{
    int cnt, /* Word count for moving object */
            header; /* Object header */
    GCP np, /* Pointer to the new object */
            from, to; /* Pointers for copying old object */
/* If NULL, or points to next space, then ok */
    if (cp == NULL ||
        space[GCP_to_PAGE(cp)] == next_space)
        return (cp);
/* If cell is already forwarded, return forwarding pointer */
    header = cp[-1];
    if (FORWARDED(header)) return ((GCP) header);
/* Forward cell, leave forwarding pointer in old header */

    np = gcalloc(HEADER_BYTES(header) - 4, 0);
    to = np - 1;
    from = cp - 1;
    cnt = HEADER_WORDS(header);
    while (cnt--) *to++ = *from++;
    cp[-1] = (int) np;
    return (np);
}

/* Pages which have might have references in the stack or the registers are
promoted to the next space by the following function. A list of
promoted pages is formed through the link cells for each page.
*/
void promote_page(int page) {
    /* Page number */

    if (page >= firstheappage && page <= lastheappage &&
        space[page] == current_space) {
        while (type[page] == CONTINUED) {
            allocatedpages = allocatedpages + 1;
            space[page] = next_space;
            page = page - 1;
        }
        space[page] = next_space;
        allocatedpages = allocatedpages + 1;
        queue(page);
    }
}

void collect() {
    unsigned *fp; /* Pointer for checking the stack */
    int reg, /* Register number */
            cnt; /* Counter */
    GCP cp, /* Pointer to sweep across a page */
            pp; /* Pointer to move constituent objects */
    /* Check for out of space during collection */
    if (next_space != current_space) {
        fprintf(stderr, "gcalloc - Out of space during collect\n");
        exit(1);
    }

    /* Allocate current page on a direct call */
    if (freewords != 0) {
        *freep = MAKE_HEADER(freewords, 0);
        freewords = 0;
    }

    /* Advance space */
    next_space = (current_space + 1) & 077777;
    allocatedpages = 0;

    /* Examine stack and registers for possible pointers */
    queue_head = 0;
    for (fp = (unsigned *) (&fp);
         fp <= stackbase;
         fp = (unsigned *) (((char *) fp) + STACKINC)) {
        promote_page(GCP_to_PAGE(*fp));
    }

    /* Move global objects */
    cnt = globals;
    while (cnt--)
        *globalp[cnt] = (int) move((GCP) *globalp[cnt]);

    /* Sweep across promoted pages and move their constituent items */
    while (queue_head != 0) {
        cp = PAGE_to_GCP(queue_head);
        while (GCP_to_PAGE(cp) == queue_head && cp != freep) {
            cnt = HEADER_PTRS(*cp);
            pp = cp + 1;
            while (cnt--) {
                *pp = (int) move((GCP) *pp);
                pp = pp + 1;
            }
            cp = cp + HEADER_WORDS(*cp);
        }
        queue_head = link[queue_head];
    }

    /* Finished */
    current_space = next_space;
}

/* When gcalloc is unable to allocate storage, it calls this routine to
allocate one or more pages. If space is not available then the garbage
collector will be called.
*/
void allocatepage(int pages) {
/* # of pages to allocate */

    int free, /* # contiguous free pages */
            firstpage = 0, /* Page # of first free page */
            allpages; /* # of pages in the heap */
    if (allocatedpages + pages >= heappages / 2) {
        collect();
        return;
    }
    free = 0;
    allpages = heappages;
    while (allpages--) {
        if (space[freepage] != current_space &&
            space[freepage] != next_space) {
            if (free++ == 0) firstpage = freepage;
            if (free == pages) {
                freep = PAGE_to_GCP(firstpage);
                if (current_space != next_space) queue(firstpage);

                freewords = pages * PAGEWORDS;
                allocatedpages = allocatedpages + pages;
                freepage = next_page(freepage);
                space[firstpage] = next_space;
                type[firstpage] = OBJECT;
                while (--pages) {
                    space[++firstpage] = next_space;
                    type[firstpage] = CONTINUED;
                }
                return;
            }
        } else free = 0;
        freepage = next_page(freepage);
        if (freepage == firstheappage) free = 0;
    }
    fprintf(stderr,
            "gcalloc - Unable to allocate %d pages in a %d page heap\n",
            pages, heappages);
    exit(1);
}

/* The heap is allocated and the appropriate data structures are initialized
by the following function.
*/
void gcinit(int heap_size, unsigned stack_base, GCP global_ptr) {
    char *heap;
    int i;
    GCP *gp;
    heappages = heap_size / PAGEBYTES;
    heap = malloc((size_t) (heap_size + PAGEBYTES - 1));

    if ((unsigned) heap & (PAGEBYTES - 1)) {
        heap = heap + (PAGEBYTES - ((unsigned) heap & (PAGEBYTES - 1)));
    }

    firstheappage = GCP_to_PAGE(heap);
    lastheappage = firstheappage + heappages - 1;
    space = ((int *) malloc(heappages * sizeof(int))) - firstheappage;

    for (i = firstheappage; i <= lastheappage; i++) {
        space[i] = 0;
    }

    link = ((int *) malloc(heappages * sizeof(int))) - firstheappage;
    type = ((int *) malloc(heappages * sizeof(int))) - firstheappage;
    globals = 0;
    gp = &global_ptr;

    while (*gp++ != NULL) {
        globals = globals + 1;
    }

    if (globals) {
        globalp = (GCP *) malloc(globals * sizeof(GCP));
        i = globals;
        gp = &global_ptr;

        while (i--) {
            globalp[i] = *gp;
            **gp = NULL;
            gp = gp + 1;
        }

    }
    stackbase = (unsigned int *) stack_base;
    current_space = 1;
    next_space = 1;
    freepage = firstheappage;
    allocatedpages = 0;
    queue_head = 0;
}

/* Storage is allocated by the following function. It will return a pointer
to the object. All pointer slots will be initialized to NULL.
*/
GCP gcalloc(size_t bytes, int pointers)
/* # of bytes in the object */
/* # of pointers in the object */
{
    int words, /* # of words to allocate */
            i; /* Loop index */
    GCP object; /* Pointer to the object */
    words = (int) ((bytes + WORDBYTES - 1) / WORDBYTES + 1);
    while (words > freewords) {
        if (freewords != 0) *freep = MAKE_HEADER(freewords, 0);
        freewords = 0;
        allocatepage((words + PAGEWORDS - 1) / PAGEWORDS);
    }
    *freep = MAKE_HEADER(words, pointers);
    for (i = 1; i <= pointers; i++) freep[i] = NULL;
    object = freep + 1;
    if (words < PAGEWORDS) {
        freewords = freewords - words;
        freep = freep + words;
    } else {
        freewords = 0;
    }
    return (object);
}

int main() {
    gcinit(5120, stackbase, globalp);
    GCP page = gcalloc(50, 2);
    printf("GCP: %p\n", page);
    printf("Hello, World!");
    return 0;
}
