// SPDX-License-Identifier: MIT

#ifndef __KHASH_LOCK_H__
#define __KHASH_LOCK_H__

#include "khash.h"

void lockBox32Maps(void);
void unlockBox32Maps(void);

#define KHASH_LOCK_ACCESSORS(name, khkey_t, khval_t)                                      \
    static inline void kh_##name##_locked_lock(void)                                      \
    {                                                                                     \
        lockBox32Maps();                                                                  \
    }                                                                                     \
    static inline void kh_##name##_locked_unlock(void)                                    \
    {                                                                                     \
        unlockBox32Maps();                                                                \
    }                                                                                     \
    static inline int kh_##name##_locked_get(kh_##name##_t* h, khkey_t key, khval_t* val) \
    {                                                                                     \
        int found = 0;                                                                    \
        lockBox32Maps();                                                                  \
        if(h) {                                                                           \
            khint_t k = kh_get(name, h, key);                                             \
            if(k!=kh_end(h)) {                                                            \
                if(val) *val = kh_value(h, k);                                            \
                found = 1;                                                                \
            }                                                                             \
        }                                                                                 \
        unlockBox32Maps();                                                                \
        return found;                                                                     \
    }                                                                                     \
    static inline khval_t kh_##name##_locked_get_or_create(kh_##name##_t* h, khkey_t key, khval_t (*create)(void*), void* ctx) \
    {                                                                                     \
        lockBox32Maps();                                                                  \
        khint_t k = kh_get(name, h, key);                                                 \
        if(k==kh_end(h)) {                                                                \
            int r;                                                                        \
            k = kh_put(name, h, key, &r);                                                 \
            kh_value(h, k) = create(ctx);                                                 \
        }                                                                                 \
        khval_t val = kh_value(h, k);                                                     \
        unlockBox32Maps();                                                                \
        return val;                                                                       \
    }                                                                                     \
    static inline int kh_##name##_locked_del(kh_##name##_t* h, khkey_t key)               \
    {                                                                                     \
        int found = 0;                                                                    \
        lockBox32Maps();                                                                  \
        if(h) {                                                                           \
            khint_t k = kh_get(name, h, key);                                             \
            if(k!=kh_end(h)) {                                                            \
                kh_del(name, h, k);                                                       \
                found = 1;                                                                \
            }                                                                             \
        }                                                                                 \
        unlockBox32Maps();                                                                \
        return found;                                                                     \
    }

#endif //__KHASH_LOCK_H__
