#define _GNU_SOURCE /* See feature_test_macros(7) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dlfcn.h>

#include "wrappedlibs.h"

#include "debug.h"
#include "wrapper.h"
#include "bridge.h"
#include "librarian/library_private.h"
#include "x64emu.h"
#include "emu/x64emu_private.h"
#include "callback.h"
#include "box64context.h"
#include "librarian.h"
#include "myalign.h"

const char* libluajitName = "libluajit-5.1.so.2";
#define LIBNAME libluajit


#define ADDED_FUNCTIONS()

#include "generated/wrappedlibluajittypes.h"

#include "wrappercallback.h"

#define SUPER() \
    GO(0)       \
    GO(1)       \
    GO(2)       \
    GO(3)       \
    GO(4)       \
    GO(5)       \
    GO(6)       \
    GO(7)       \
    GO(9)       \
    GO(8)       \
    GO(10)      \
    GO(11)      \
    GO(12)      \
    GO(13)      \
    GO(14)      \
    GO(15)      \
    GO(16)      \
    GO(17)      \
    GO(18)      \
    GO(19)      \
    GO(20)      \
    GO(21)      \
    GO(22)      \
    GO(23)      \
    GO(24)      \
    GO(25)      \
    GO(26)      \
    GO(27)      \
    GO(28)      \
    GO(29)      \
    GO(30)      \
    GO(31)      \
    GO(32)      \
    GO(33)      \
    GO(34)      \
    GO(35)      \
    GO(36)      \
    GO(37)      \
    GO(38)      \
    GO(39)      \
    GO(40)      \
    GO(41)      \
    GO(42)      \
    GO(43)      \
    GO(44)      \
    GO(45)      \
    GO(46)      \
    GO(47)      \
    GO(48)      \
    GO(49)      \
    GO(50)      \
    GO(51)      \
    GO(52)      \
    GO(53)      \
    GO(54)      \
    GO(55)      \
    GO(56)      \
    GO(57)      \
    GO(58)      \
    GO(59)      \
    GO(60)      \
    GO(61)      \
    GO(62)      \
    GO(63)      \
    GO(64)      \
    GO(65)      \
    GO(66)      \
    GO(67)      \
    GO(68)      \
    GO(69)      \
    GO(70)      \
    GO(71)      \
    GO(72)      \
    GO(73)      \
    GO(74)      \
    GO(75)      \
    GO(76)      \
    GO(77)      \
    GO(78)      \
    GO(79)      \
    GO(80)      \
    GO(81)      \
    GO(82)      \
    GO(83)      \
    GO(84)      \
    GO(85)      \
    GO(86)      \
    GO(87)      \
    GO(88)      \
    GO(89)      \
    GO(90)      \
    GO(91)      \
    GO(92)      \
    GO(93)      \
    GO(94)      \
    GO(95)      \
    GO(96)      \
    GO(97)      \
    GO(98)      \
    GO(99)      \
    GO(100)      \
    GO(101)      \
    GO(102)      \
    GO(103)      \
    GO(104)      \
    GO(105)      \
    GO(106)      \
    GO(107)      \
    GO(108)      \
    GO(109)      \
    GO(110)      \
    GO(111)      \
    GO(112)      \
    GO(113)      \
    GO(114)      \
    GO(115)      \
    GO(116)      \
    GO(117)      \
    GO(118)      \
    GO(119)      \
    GO(120)      \
    GO(121)      \
    GO(122)      \
    GO(123)      \
    GO(124)      \
    GO(125)      \
    GO(126)      \
    GO(127)      \
    GO(128)      \
    GO(129)      \
    GO(130)      \
    GO(131)      \
    GO(132)      \
    GO(133)      \
    GO(134)      \
    GO(135)      \
    GO(136)      \
    GO(137)      \
    GO(138)      \
    GO(139)      \
    GO(140)      \
    GO(141)      \
    GO(142)      \
    GO(143)      \
    GO(144)      \
    GO(145)      \
    GO(146)      \
    GO(147)      \
    GO(148)      \
    GO(149)      \
    GO(150)      \
    GO(151)      \
    GO(152)      \
    GO(153)      \
    GO(154)      \
    GO(155)      \
    GO(156)      \
    GO(157)      \
    GO(158)      \
    GO(159)      \
    GO(160)      \
    GO(161)      \
    GO(162)      \
    GO(163)      \
    GO(164)      \
    GO(165)      \
    GO(166)      \
    GO(167)      \
    GO(168)      \
    GO(169)      \

#define GO(A)                                            \
    static uintptr_t my_pushcclosure_fct_##A = 0;        \
    static int my_pushcclosure_##A(void* L)              \
    {                                                    \
        RunFunctionFmt(my_pushcclosure_fct_##A, "p", L); \
    }
SUPER()
#undef GO
static void* find_pushcclosure_Fct(void* fct)
{
    if (!fct) return fct;
    if (GetNativeFnc((uintptr_t)fct)) return GetNativeFnc((uintptr_t)fct);
#define GO(A) \
    if (my_pushcclosure_fct_##A == (uintptr_t)fct) return my_pushcclosure_##A;
    SUPER()
#undef GO
#define GO(A)                                     \
    if (my_pushcclosure_fct_##A == 0) {           \
        my_pushcclosure_fct_##A = (uintptr_t)fct; \
        return my_pushcclosure_##A;               \
    }
    SUPER()
#undef GO
    printf_log(LOG_NONE, "Warning, no more slot for luajit pushcclosure callback\n");
    return NULL;
}

EXPORT
void my_lua_pushcclosure(x64emu_t* emu, void* L, void* fn, int n)
{
    return my->lua_pushcclosure(L, find_pushcclosure_Fct(fn), n);
}

#include "wrappedlib_init.h"
