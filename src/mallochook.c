// SPDX-License-Identifier: MIT
#define _GNU_SOURCE /* See feature_test_macros(7) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/param.h>
#include <sys/mman.h>
#include <dlfcn.h>
#include <malloc.h>

#include "box64context.h"
#include "debug.h"
#include "callback.h"
#include "librarian.h"
#include "elfs/elfloader_private.h"
#include "custommem.h"
#include "symbols.h"
#include "khash.h"
#include "alternate.h"
#ifdef BOX32
#include "box32.h"
#endif

/*
    Handling of the malloc family.

    A process only works if it has only one allocator: the one the program provides when it
    overrides the malloc family (mimalloc, tcmalloc inside libcef, ...), or the system one
    (the host libc, interposed by Box64 here) when it doesn't.

    Why it must be only one: the program's own code can use its allocator without going through
    any symbol Box64 could intercept, as compilers inline the small allocator helpers. A pointer
    coming from another allocator would then be freed by the wrong one and corrupt the heap, and
    there is no way to catch that at runtime (guessing "this pointer is mmap'ed so it is
    probably the program's" does not work in general).

    So Box64 does not rewrite the program's malloc family symbols. Instead, when an overridden
    malloc family is found while loading the ELF that defines it, and once that ELF is
    initialized, all the allocations that go through the symbols Box64 interposes are forwarded
    to it, whoever asks for them: the emulated program or a native library. The program's own
    calls are left as they are, they already use the right allocator, and whatever symbol they
    reach (theirs, or Box64's interposed one) ends up on the same heap.

    When no ELF overrides the malloc family, Box64's allocator is the only allocator of the
    process, and everything is allocated and freed with it.

    The allocations made with Box64's allocator while the program's allocator is, or is about to
    become, the process allocator (the ELF providing it is not initialized yet, or the current
    thread cannot run emulated code) are remembered, so a free of one of them goes back to
    Box64's allocator and never to the program's one.
*/
#ifndef ANDROID

static int allocator_known = 0;  // an ELF providing its own malloc family was found
static int allocator_active = 0; // and it is initialized, so it can be used

static uintptr_t real_malloc = 0;
static uintptr_t real_free = 0;
static uintptr_t real_calloc = 0;
static uintptr_t real_realloc = 0;
static uintptr_t real_aligned_alloc = 0;
static uintptr_t real_memalign = 0;
static uintptr_t real_posix_memalign = 0;
static uintptr_t real_valloc = 0;
static uintptr_t real_pvalloc = 0;
static uintptr_t real_malloc_usable_size = 0;

// C++ operators, only used by the wrapped tbbmalloc proxy
static uintptr_t real__Znwm = 0;
static uintptr_t real__ZnwmRKSt9nothrow_t = 0;
static uintptr_t real__Znam = 0;
static uintptr_t real__ZnamRKSt9nothrow_t = 0;
static uintptr_t real__ZdaPv = 0;
static uintptr_t real__ZdaPvm = 0;
static uintptr_t real__ZdaPvmSt11align_val_t = 0;
static uintptr_t real__ZdlPv = 0;
static uintptr_t real__ZdlPvm = 0;
static uintptr_t real__ZnwmSt11align_val_t = 0;
static uintptr_t real__ZnwmSt11align_val_tRKSt9nothrow_t = 0;
static uintptr_t real__ZnamSt11align_val_t = 0;
static uintptr_t real__ZnamSt11align_val_tRKSt9nothrow_t = 0;
static uintptr_t real__ZdlPvRKSt9nothrow_t = 0;
static uintptr_t real__ZdaPvRKSt9nothrow_t = 0;
static uintptr_t real__ZdaPvSt11align_val_t = 0;
static uintptr_t real__ZdaPvSt11align_val_tRKSt9nothrow_t = 0;
static uintptr_t real__ZdlPvSt11align_val_t = 0;
static uintptr_t real__ZdlPvmSt11align_val_t = 0;
static uintptr_t real__ZdlPvSt11align_val_tRKSt9nothrow_t = 0;

size_t (*box_malloc_usable_size)(void*) = NULL;

// allocations made with Box64's allocator, that the program's allocator must not free
KHASH_SET_INIT_INT64(allocset)
static kh_allocset_t* our_allocs = NULL;

static void remember_our_alloc(void* p)
{
    if (!allocator_known || !p)
        return;
    if (!our_allocs)
        our_allocs = kh_init(allocset);
    int ret;
    kh_put(allocset, our_allocs, (uintptr_t)p, &ret);
}

static int forget_our_alloc(void* p)
{
    if (!our_allocs || !p)
        return 0;
    khint_t k = kh_get(allocset, our_allocs, (uintptr_t)p);
    if (k == kh_end(our_allocs))
        return 0;
    kh_del(allocset, our_allocs, k);
    return 1;
}

static int is_our_alloc(void* p)
{
    if (!our_allocs || !p) return 0;
    return kh_get(allocset, our_allocs, (uintptr_t)p) != kh_end(our_allocs);
}

// set while the program's allocator is running: anything it asks for indirectly (box64's own
// bookkeeping, a native library it calls) must not re-enter it, and goes to box64's heap
static __thread int in_guest_allocator = 0;

#define RUN_GUEST_ALLOC(FN, ...)                            \
    ({                                                      \
        in_guest_allocator = 1;                             \
        uint64_t _r = RunFunctionFmtNoAlt(FN, __VA_ARGS__); \
        in_guest_allocator = 0;                             \
        _r;                                                 \
    })

static int can_use_allocator(void)
{
    return allocator_active && !in_guest_allocator;
}

char* box_strdup(const char* s)
{
    char* ret = box_calloc(1, strlen(s) + 1);
    memcpy(ret, s, strlen(s));
    return ret;
}

char* box_realpath(const char* path, char* ret)
{
    if (ret)
        return realpath(path, ret);
#ifdef PATH_MAX
    size_t path_max = PATH_MAX;
#else
    size_t path_max = pathconf(path, _PC_PATH_MAX);
    if (path_max <= 0)
        path_max = 4096;
#endif
    char tmp[path_max];
    char* p = realpath(path, tmp);
    if (!p)
        return NULL;
    return box_strdup(tmp);
}

static size_t pot(size_t l)
{
    size_t ret = 0;
    while (l > (1u << ret))
        ++ret;
    return 1u << ret;
}

#ifdef BOX32
int isCustomAddr(void* p);
// Check if entire allocation (ptr to ptr+size-1) fits within 32-bit address space
#define FITS_IN_32BIT(ptr, size) (((uintptr_t)(ptr) + (size)) <= 0x100000000ULL)
void* box32_calloc(size_t n, size_t s)
{
    void* ret = box_calloc(n, s);
    if (ret && FITS_IN_32BIT(ret, n * s)) return ret;
    box_free(ret);
    malloc_trim(0);
    ret = box_calloc(n, s);
    if (ret && FITS_IN_32BIT(ret, n * s)) return ret;
    box_free(ret);
    return customCalloc32(n, s);
}
void* box32_malloc(size_t s)
{
    void* ret = box_malloc(s);
    if (ret && FITS_IN_32BIT(ret, s)) return ret;
    box_free(ret);
    malloc_trim(0);
    ret = box_malloc(s);
    if (ret && FITS_IN_32BIT(ret, s)) return ret;
    box_free(ret);
    return customMalloc32(s);
}
void* box32_realloc(void* p, size_t s)
{
    if (isCustomAddr(p))
        return customRealloc32(p, s);
    void* ret = box_realloc(p, s);
    if (!ret) return NULL;
    if (FITS_IN_32BIT(ret, s)) return ret;
    malloc_trim(0);
    void* newret = customMalloc32(s);
    memcpy(newret, ret, s);
    box_free(ret);
    return newret;
}
void box32_free(void* p)
{
    if (isCustomAddr(p))
        customFree32(p);
    else
        box_free(p);
}
void* box32_memalign(size_t align, size_t s)
{
    void* ret = box_memalign(align, s);
    if (ret && FITS_IN_32BIT(ret, s)) return ret;
    box_free(ret);
    malloc_trim(0);
    return customMemAligned32(align, s);
}
size_t box32_malloc_usable_size(void* p)
{
    if (isCustomAddr(p))
        return customGetUsableSize(p);
    else
        return box_malloc_usable_size(p);
}

char* box32_strdup(const char* s)
{
    char* ret = box32_calloc(1, strlen(s) + 1);
    memcpy(ret, s, strlen(s));
    return ret;
}

#endif

EXPORT void* malloc(size_t l)
{
    void* ret = actual_calloc(1, l);
    remember_our_alloc(ret);
    return ret;
}

EXPORT void free(void* p)
{
    if (!p) return;
    if (forget_our_alloc(p) || !can_use_allocator() || !real_free) {
        actual_free(p);
        return;
    }
    // everything else belongs to the program's allocator
    RUN_GUEST_ALLOC(real_free, "p", p);
}

EXPORT void* calloc(size_t n, size_t s)
{
    void* ret = actual_calloc(n, s);
    remember_our_alloc(ret);
    return ret;
}

EXPORT void* realloc(void* p, size_t s)
{
    if (!is_our_alloc(p) && can_use_allocator()) {
        if (real_realloc)
            return (void*)RUN_GUEST_ALLOC(real_realloc, "pL", p, s);
        // the program's allocator has no realloc: do it by hand
        size_t old = real_malloc_usable_size ? (size_t)RUN_GUEST_ALLOC(real_malloc_usable_size, "p", p) : 0;
        void* ret = (void*)RUN_GUEST_ALLOC(real_malloc, "L", s);
        if (!ret)
            return NULL;
        if (p && old)
            memcpy(ret, p, (old < s) ? old : s);
        if (p)
            RUN_GUEST_ALLOC(real_free, "p", p);
        return ret;
    }
    forget_our_alloc(p);
    void* ret = actual_realloc(p, s);
    remember_our_alloc(ret);
    return ret;
}

EXPORT void* memalign(size_t align, size_t size)
{
    if (box64_is32bits && align == 4)
        align = sizeof(void*);
    void* ret = actual_memalign(align, size);
    remember_our_alloc(ret);
    return ret;
}

EXPORT void* aligned_alloc(size_t align, size_t size)
{
    void* ret = actual_memalign(align, size);
    remember_our_alloc(ret);
    return ret;
}

EXPORT int posix_memalign(void** p, size_t align, size_t size)
{
    if (box64_is32bits && align == 4)
        align = sizeof(void*);
    if ((align % sizeof(void*)) || (pot(align) != align))
        return EINVAL;
    void* ret = actual_memalign(align, size);
    if (!ret)
        return ENOMEM;
    remember_our_alloc(ret);
    *p = ret;
    return 0;
}

EXPORT void* valloc(size_t size)
{
    void* ret = actual_memalign(box64_pagesize, size);
    remember_our_alloc(ret);
    return ret;
}

EXPORT void* pvalloc(size_t size)
{
    void* ret = actual_memalign(box64_pagesize, ALIGN(size));
    remember_our_alloc(ret);
    return ret;
}

EXPORT void cfree(void* p)
{
    free(p);
}

EXPORT size_t malloc_usable_size(void* p)
{
    if (can_use_allocator() && real_malloc_usable_size && !is_our_alloc(p))
        return RUN_GUEST_ALLOC(real_malloc_usable_size, "p", p);
    return box_malloc_usable_size ? box_malloc_usable_size(p) : 0;
}

EXPORT void* my__Znwm(size_t sz) // operator new(size_t)
{
    void* ret = actual_malloc(sz);
    remember_our_alloc(ret);
    return ret;
}

EXPORT void* my__ZnwmRKSt9nothrow_t(size_t sz, void* p) // operator new(size_t, std::nothrow_t const&)
{
    void* ret = actual_malloc(sz);
    remember_our_alloc(ret);
    return ret;
}

EXPORT void* my__Znam(size_t sz) // operator new[](size_t)
{
    void* ret = actual_malloc(sz);
    remember_our_alloc(ret);
    return ret;
}

EXPORT void* my__ZnamRKSt9nothrow_t(size_t sz, void* p) // operator new[](size_t, std::nothrow_t const&)
{
    void* ret = actual_malloc(sz);
    remember_our_alloc(ret);
    return ret;
}

EXPORT void* my__ZnwmSt11align_val_t(size_t sz, size_t align) // operator new(unsigned long, std::align_val_t)
{
    void* ret = actual_memalign(align, sz);
    remember_our_alloc(ret);
    return ret;
}

EXPORT void* my__ZnwmSt11align_val_tRKSt9nothrow_t(size_t sz, size_t align, void* p) // operator new(unsigned long, std::align_val_t, std::nothrow_t const&)
{
    void* ret = actual_memalign(align, sz);
    remember_our_alloc(ret);
    return ret;
}

EXPORT void* my__ZnamSt11align_val_t(size_t sz, size_t align) // operator new[](unsigned long, std::align_val_t)
{
    void* ret = actual_memalign(align, sz);
    remember_our_alloc(ret);
    return ret;
}

EXPORT void* my__ZnamSt11align_val_tRKSt9nothrow_t(size_t sz, size_t align, void* p) // operator new[](unsigned long, std::align_val_t, std::nothrow_t const&)
{
    void* ret = actual_memalign(align, sz);
    remember_our_alloc(ret);
    return ret;
}

EXPORT void my__ZdaPv(void* p) // operator delete[](void*)
{
    if (!p) return;
    if (forget_our_alloc(p) || !can_use_allocator() || !real__ZdaPv) {
        actual_free(p);
        return;
    }
    RUN_GUEST_ALLOC(real__ZdaPv, "p", p);
}

EXPORT void my__ZdaPvm(void* p, size_t sz) // operator delete[](void*, size_t)
{
    if (!p) return;
    if (forget_our_alloc(p) || !can_use_allocator() || !real__ZdaPvm) {
        actual_free(p);
        return;
    }
    RUN_GUEST_ALLOC(real__ZdaPvm, "pL", p, sz);
}

EXPORT void my__ZdaPvmSt11align_val_t(void* p, size_t sz, size_t align) // operator delete[](void*, unsigned long, std::align_val_t)
{
    if (!p) return;
    if (forget_our_alloc(p) || !can_use_allocator() || !real__ZdaPvmSt11align_val_t) {
        actual_free(p);
        return;
    }
    RUN_GUEST_ALLOC(real__ZdaPvmSt11align_val_t, "pLL", p, sz, align);
}

EXPORT void my__ZdlPv(void* p) // operator delete(void*)
{
    if (!p) return;
    if (forget_our_alloc(p) || !can_use_allocator() || !real__ZdlPv) {
        actual_free(p);
        return;
    }
    RUN_GUEST_ALLOC(real__ZdlPv, "p", p);
}

EXPORT void my__ZdlPvm(void* p, size_t sz) // operator delete(void*, size_t)
{
    if (!p) return;
    if (forget_our_alloc(p) || !can_use_allocator() || !real__ZdlPvm) {
        actual_free(p);
        return;
    }
    RUN_GUEST_ALLOC(real__ZdlPvm, "pL", p, sz);
}

EXPORT void my__ZdlPvRKSt9nothrow_t(void* p, void* n) // operator delete(void*, std::nothrow_t const&)
{
    if (!p) return;
    if (forget_our_alloc(p) || !can_use_allocator() || !real__ZdlPvRKSt9nothrow_t) {
        actual_free(p);
        return;
    }
    RUN_GUEST_ALLOC(real__ZdlPvRKSt9nothrow_t, "pp", p, n);
}

EXPORT void my__ZdaPvRKSt9nothrow_t(void* p, void* n) // operator delete[](void*, std::nothrow_t const&)
{
    if (!p) return;
    if (forget_our_alloc(p) || !can_use_allocator() || !real__ZdaPvRKSt9nothrow_t) {
        actual_free(p);
        return;
    }
    RUN_GUEST_ALLOC(real__ZdaPvRKSt9nothrow_t, "pp", p, n);
}

EXPORT void my__ZdaPvSt11align_val_t(void* p, size_t align) // operator delete[](void*, std::align_val_t)
{
    if (!p) return;
    if (forget_our_alloc(p) || !can_use_allocator() || !real__ZdaPvSt11align_val_t) {
        actual_free(p);
        return;
    }
    RUN_GUEST_ALLOC(real__ZdaPvSt11align_val_t, "pL", p, align);
}

EXPORT void my__ZdaPvSt11align_val_tRKSt9nothrow_t(void* p, size_t align, void* n) // operator delete[](void*, std::align_val_t, std::nothrow_t const&)
{
    if (!p) return;
    if (forget_our_alloc(p) || !can_use_allocator() || !real__ZdaPvSt11align_val_tRKSt9nothrow_t) {
        actual_free(p);
        return;
    }
    RUN_GUEST_ALLOC(real__ZdaPvSt11align_val_tRKSt9nothrow_t, "pLp", p, align, n);
}

EXPORT void my__ZdlPvSt11align_val_t(void* p, size_t align) // operator delete(void*, std::align_val_t)
{
    if (!p) return;
    if (forget_our_alloc(p) || !can_use_allocator() || !real__ZdlPvSt11align_val_t) {
        actual_free(p);
        return;
    }
    RUN_GUEST_ALLOC(real__ZdlPvSt11align_val_t, "pL", p, align);
}

EXPORT void my__ZdlPvmSt11align_val_t(void* p, size_t sz, size_t align) // operator delete(void*, unsigned long, std::align_val_t)
{
    if (!p) return;
    if (forget_our_alloc(p) || !can_use_allocator() || !real__ZdlPvmSt11align_val_t) {
        actual_free(p);
        return;
    }
    RUN_GUEST_ALLOC(real__ZdlPvmSt11align_val_t, "pLL", p, sz, align);
}

EXPORT void my__ZdlPvSt11align_val_tRKSt9nothrow_t(void* p, size_t align, void* n) // operator delete(void*, std::align_val_t, std::nothrow_t const&)
{
    if (!p) return;
    if (forget_our_alloc(p) || !can_use_allocator() || !real__ZdlPvSt11align_val_tRKSt9nothrow_t) {
        actual_free(p);
        return;
    }
    RUN_GUEST_ALLOC(real__ZdlPvSt11align_val_tRKSt9nothrow_t, "pLp", p, align, n);
}


typedef struct alloc_sym_s {
    const char* name;
    uintptr_t* addr;
} alloc_sym_t;

// finding the malloc family in an elf means this elf provides the process allocator
static alloc_sym_t alloc_syms[] = {
    { "malloc", &real_malloc },
    { "__libc_malloc", &real_malloc },
    { "free", &real_free },
    { "__libc_free", &real_free },
    { "calloc", &real_calloc },
    { "__libc_calloc", &real_calloc },
    { "realloc", &real_realloc },
    { "__libc_realloc", &real_realloc },
    { "aligned_alloc", &real_aligned_alloc },
    { "memalign", &real_memalign },
    { "__libc_memalign", &real_memalign },
    { "posix_memalign", &real_posix_memalign },
    { "valloc", &real_valloc },
    { "__libc_valloc", &real_valloc },
    { "pvalloc", &real_pvalloc },
    { "__libc_pvalloc", &real_pvalloc },
    { "malloc_usable_size", &real_malloc_usable_size },
    { "_Znwm", &real__Znwm },
    { "_ZnwmRKSt9nothrow_t", &real__ZnwmRKSt9nothrow_t },
    { "_Znam", &real__Znam },
    { "_ZnamRKSt9nothrow_t", &real__ZnamRKSt9nothrow_t },
    { "_ZdaPv", &real__ZdaPv },
    { "_ZdaPvm", &real__ZdaPvm },
    { "_ZdaPvmSt11align_val_t", &real__ZdaPvmSt11align_val_t },
    { "_ZdlPv", &real__ZdlPv },
    { "_ZdlPvm", &real__ZdlPvm },
    { "_ZnwmSt11align_val_t", &real__ZnwmSt11align_val_t },
    { "_ZnwmSt11align_val_tRKSt9nothrow_t", &real__ZnwmSt11align_val_tRKSt9nothrow_t },
    { "_ZnamSt11align_val_t", &real__ZnamSt11align_val_t },
    { "_ZnamSt11align_val_tRKSt9nothrow_t", &real__ZnamSt11align_val_tRKSt9nothrow_t },
    { "_ZdlPvRKSt9nothrow_t", &real__ZdlPvRKSt9nothrow_t },
    { "_ZdaPvRKSt9nothrow_t", &real__ZdaPvRKSt9nothrow_t },
    { "_ZdaPvSt11align_val_t", &real__ZdaPvSt11align_val_t },
    { "_ZdaPvSt11align_val_tRKSt9nothrow_t", &real__ZdaPvSt11align_val_tRKSt9nothrow_t },
    { "_ZdlPvSt11align_val_t", &real__ZdlPvSt11align_val_t },
    { "_ZdlPvSt11align_val_tRKSt9nothrow_t", &real__ZdlPvSt11align_val_tRKSt9nothrow_t },
    { NULL, NULL }
};

static void recordAllocSym(const char* symname, uintptr_t offs)
{
    for (int i = 0; alloc_syms[i].name; ++i)
        if (!strcmp(symname, alloc_syms[i].name)) {
            if (!*alloc_syms[i].addr)
                *alloc_syms[i].addr = offs;
            break;
        }
}

void checkHookedSymbols(elfheader_t* h)
{
    if (box64_nolibs || allocator_known)
        return;
    if (box64_is32bits)
        return;
    for (size_t i = 0; i < h->numSymTab; ++i) {
        int type = ELF64_ST_TYPE(h->SymTab._64[i].st_info);
        if ((type == STT_FUNC) && (h->SymTab._64[i].st_shndx != 0 && h->SymTab._64[i].st_shndx <= 65521))
            recordAllocSym(h->StrTab + h->SymTab._64[i].st_name, h->SymTab._64[i].st_value + h->delta);
    }
    if (!real_malloc) {
        for (size_t i = 0; i < h->numDynSym; ++i) {
            const char* symname = h->DynStr + h->DynSym._64[i].st_name;
            int bind = ELF64_ST_BIND(h->DynSym._64[i].st_info);
            int type = ELF64_ST_TYPE(h->DynSym._64[i].st_info);
            int vis = h->DynSym._64[i].st_other & 0x3;
            if ((type == STT_FUNC)
                && (vis == STV_DEFAULT || vis == STV_PROTECTED) && (h->DynSym._64[i].st_shndx != 0 && h->DynSym._64[i].st_shndx <= 65521)
                && (bind != STB_LOCAL && bind != STB_WEAK))
                recordAllocSym(symname, h->DynSym._64[i].st_value + h->delta);
        }
    }
    if (real_malloc) {
        allocator_known = 1;
        h->own_allocator = 1;
        printf_log(LOG_INFO, "Program's malloc family found in %s (malloc=%p, free=%p), program memory will be freed with it\n", ElfName(h), (void*)real_malloc, (void*)real_free);
    }
}

void StartGuestAllocator()
{
    allocator_active = 1;
}
void EndGuestAllocator()
{
    allocator_active = 0;
}

EXPORT int my___TBB_internal_find_original_malloc(int n, char* names[], void* ptr[])
{
    static const struct {
        const char* name;
        void* f;
    } allocs[] = {
        { "malloc", malloc },
        { "free", free },
        { "calloc", calloc },
        { "realloc", realloc },
        { "memalign", memalign },
        { "posix_memalign", posix_memalign },
        { "valloc", valloc },
        { "pvalloc", pvalloc },
        { "aligned_alloc", aligned_alloc },
        { "cfree", cfree },
        { "malloc_usable_size", malloc_usable_size },
        { NULL, NULL }
    };
    int ret = 1;
    for (int i = 0; i < n; ++i) {
        ptr[i] = NULL;
        for (int j = 0; allocs[j].name; ++j)
            if (!strcmp(names[i], allocs[j].name)) {
                ptr[i] = allocs[j].f;
                break;
            }
        if (!ptr[i])
            ret = 0;
    }
    return ret;
}

EXPORT void my___TBB_call_with_my_server_info(void* cb, void* server)
{
    // nothing
}

EXPORT int my___TBB_make_rml_server(void* factory, void* server, void* client)
{
    // nothing
    return 0;
}

EXPORT void my___RML_close_factory(void* server)
{
    // nothing
}

EXPORT int my___RML_open_factory(void* factory, void* server_version, int client_version)
{
    // nothing
    return 0;
}

void init_malloc_hook()
{
    box_malloc_usable_size = dlsym(RTLD_NEXT, "malloc_usable_size");
}

#else  // ANDROID
void init_malloc_hook() { }
void StartGuestAllocator() { }
void EndGuestAllocator() { }
void checkHookedSymbols(elfheader_t* h) { }
#endif //! ANDROID
