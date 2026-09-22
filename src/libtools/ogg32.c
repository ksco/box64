// SPDX-License-Identifier: MIT
/*
    ogg_sync_pageout hook for 32-bit binaries.

    ogg_sync_pageout/pageseek populates an ogg_page with pointers into the ogg_sync_state
    internal buffer. A later ogg_sync_buffer call may realloc that buffer, invalidating those
    pointers, and games that statically link libogg (e.g. Grim Fandango Remastered) then crash
    on a stale pointer. It can happen on any backend where realloc moves the buffer instead of
    extending it in place, so this is currently gated to PPC64LE, where 64KB pages make it
    particularly likely, but it may apply to other backends too.

    The fix: after calling the original ogg_sync_pageout, copy the page header and body to
    stable allocations.

    See https://github.com/ptitSeb/box64/issues/3587
*/
#include "elfs/elfloader_private.h"

#if !defined(BOX32) || !defined(PPC64LE)

void checkOggHookedSymbols32(elfheader_t* h)
{
    (void)h;
}

#else

#include <stdint.h>
#include <string.h>
#include "debug.h"
#include "box64context.h"
#include "callback.h"
#include "alternate.h"
#include "bridge.h"
#include "wrapper32.h"

typedef struct __attribute__((packed)) {
    ptr_t header; // unsigned char*
    long_t header_len;
    ptr_t body; // unsigned char*
    long_t body_len;
} ogg_page_32_t;

static uintptr_t real_ogg_sync_pageout_32 = 0;
static void* ogg_page_header_copy = NULL;
static void* ogg_page_body_copy = NULL;

static int my_ogg_sync_pageout_32(void* oy, void* og)
{
    // Call the original emulated ogg_sync_pageout
    int ret = (int)RunFunctionFmtNoAlt(real_ogg_sync_pageout_32, "pp", oy, og);

    if (ret > 0 && og) {
        // ogg_sync_pageout succeeded — og now has pointers into oy->data
        // which may be invalidated by a later ogg_sync_buffer/realloc.
        // Copy the page data to stable allocations.
        ogg_page_32_t* page = (ogg_page_32_t*)og;

        // Free previous copies
        if (ogg_page_header_copy) {
            actual_free(ogg_page_header_copy);
            ogg_page_header_copy = NULL;
        }
        if (ogg_page_body_copy) {
            actual_free(ogg_page_body_copy);
            ogg_page_body_copy = NULL;
        }

        if (page->header && page->header_len > 0) {
            ogg_page_header_copy = actual_malloc(page->header_len);
            if (ogg_page_header_copy) {
                memcpy(ogg_page_header_copy, from_ptrv(page->header), page->header_len);
                page->header = to_ptrv(ogg_page_header_copy);
            }
        }

        if (page->body && page->body_len > 0) {
            ogg_page_body_copy = actual_malloc(page->body_len);
            if (ogg_page_body_copy) {
                memcpy(ogg_page_body_copy, from_ptrv(page->body), page->body_len);
                page->body = to_ptrv(ogg_page_body_copy);
            }
        }
    }

    return ret;
}

void checkOggHookedSymbols32(elfheader_t* h)
{
    if (!h->numSymTab || !h->SymTab._32)
        return;

    // Scan for ogg_sync_pageout in the 32-bit symbol table
    for (size_t i = 0; i < h->numSymTab; ++i) {
        int type = ELF32_ST_TYPE(h->SymTab._32[i].st_info);
        if (type == STT_FUNC && h->SymTab._32[i].st_shndx != 0
            && h->SymTab._32[i].st_shndx <= 65521) {
            const char* symname = h->StrTab + h->SymTab._32[i].st_name;
            if (!strcmp(symname, "ogg_sync_pageout")) {
                uintptr_t offs = h->SymTab._32[i].st_value + h->delta;
                if (!real_ogg_sync_pageout_32) {
                    real_ogg_sync_pageout_32 = offs;
                    uintptr_t alt = AddCheckBridge(my_context->system, iFpp_32, (void*)my_ogg_sync_pageout_32, 0, "my_ogg_sync_pageout_32");
                    addAlternate((void*)offs, (void*)alt);
                    printf_log(LOG_INFO, "Hooked statically-linked ogg_sync_pageout at %p in %s (ogg realloc fix)\n", (void*)offs, ElfName(h));
                }
                break;
            }
        }
    }
}

#endif
