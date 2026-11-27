// SPDX-License-Identifier: MIT
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <errno.h>

#include "debug.h"
#include "box64context.h"
#include "box64cpu.h"
#include "emu/x64emu_private.h"
#include "x64emu.h"
#include "box64stack.h"
#include "callback.h"
#include "emu/x64run_private.h"
#include "x64trace.h"
#include "dynarec_native.h"

#include "rv64_printer.h"
#include "dynarec_rv64_private.h"
#include "dynarec_rv64_functions.h"
#include "../dynarec_helper.h"

uintptr_t dynarec64_AVX_0F38(dynarec_rv64_t* dyn, uintptr_t addr, uintptr_t ip, int ninst, vex_t vex, int* ok, int* need_epilog)
{
    (void)ip;
    (void)need_epilog;

    uint8_t opcode = F8;
    uint8_t nextop, u8;
    uint8_t gd, ed, vd;
    uint8_t wback, wb1, wb2;
    uint8_t eb1, eb2, gb1, gb2;
    int32_t i32, i32_;
    int cacheupd = 0;
    int v0, v1, v2;
    int q0, q1, q2;
    int d0, d1, d2;
    int s0;
    uint64_t tmp64u;
    int64_t j64;
    int64_t fixedaddress;
    int unscaled;
    MAYUSE(wb1);
    MAYUSE(wb2);
    MAYUSE(eb1);
    MAYUSE(eb2);
    MAYUSE(gb1);
    MAYUSE(gb2);
    MAYUSE(q0);
    MAYUSE(q1);
    MAYUSE(d0);
    MAYUSE(d1);
    MAYUSE(s0);
    MAYUSE(j64);
    MAYUSE(cacheupd);

    rex_t rex = vex.rex;

    switch (opcode) {
        case 0xF2:
            INST_NAME("ANDN Gd, Vd, Ed");
            nextop = F8;
            SETFLAGS(X_ALL, SF_SET, NAT_FLAGS_NOFUSION);
            GETGDd;
            GETED(0);
            GETVD;
            ANDN(gd, ed, vd, x5);
            if (!rex.w) {
                ZEROUP(gd);
            }
            CLEAR_FLAGS();
            IFX (X_SF) {
                SRLI(x5, gd, rex.w ? 63 : 31);
                SLLI(x5, x5, F_SF);
                OR(xFlags, xFlags, x5);
            }
            IFX (X_ZF) {
                SET_FLAGS_EQZ(gd, F_ZF, x5);
            }
            if (BOX64DRENV(dynarec_safeflags)) {
                IFX (X_PF) emit_pf(dyn, ninst, gd, x2, x5);
            }
            break;
        case 0xF3: {
            nextop = F8;
            const int operation = (nextop >> 3) & 7;
            switch (operation) {
                case 1:
                    INST_NAME("BLSR Vd, Ed");
                    break;
                case 2:
                    INST_NAME("BLSMSK Vd, Ed");
                    break;
                case 3:
                    INST_NAME("BLSI Vd, Ed");
                    break;
                default:
                    DEFAULT;
            }
            SETFLAGS(X_ALL, SF_SET, NAT_FLAGS_NOFUSION);
            if (MODREG) {
                GETED(0);
            } else {
                SMREAD();
                addr = geted(dyn, addr, ninst, nextop, &wback, x2, x1, &fixedaddress, rex, NULL, 1, 0);
                ed = x1;
                if (rex.w) {
                    LD(ed, wback, fixedaddress);
                } else {
                    LWU(ed, wback, fixedaddress);
                }
            }
            vd = TO_NAT(vex.v);
            MARKREGd(vd);
            const int source_zero_extended = !rex.w && (!MODREG || isUpper32Zero(dyn, ninst, ed));
            CLEAR_FLAGS();
            IFX (X_CF) {
                int test_source = ed;
                if (!rex.w && !source_zero_extended) {
                    ADDIW(x5, ed, 0);
                    test_source = x5;
                }
                if (operation == 3) {
                    SNEZ(x5, test_source);
                } else {
                    SEQZ(x5, test_source);
                }
                OR(xFlags, xFlags, x5);
            }
            if (operation == 3) {
                SUBxw(x3, xZR, ed);
                AND(vd, ed, x3);
            } else {
                ADDIxw(x3, ed, -1);
                if (operation == 2) {
                    XOR(vd, ed, x3);
                } else {
                    AND(vd, ed, x3);
                }
            }
            int result_has_upper_bits = !rex.w && (operation == 2 || !source_zero_extended);
            if (!rex.w) {
                if (!result_has_upper_bits) {
                    UP32_ZERO(vd);
                } else if (NEED_ZEROUP32(vd)) {
                    ZEROUP_RESULT(vd);
                    result_has_upper_bits = 0;
                }
            }
            IFX (X_ZF) {
                if (operation != 2) {
                    int test_result = vd;
                    if (result_has_upper_bits) {
                        ADDIW(x3, vd, 0);
                        test_result = x3;
                    }
                    SET_FLAGS_EQZ(test_result, F_ZF, x5);
                }
            }
            IFX (X_SF) {
                SRLIxw(x5, vd, rex.w ? 63 : 31);
                SLLI(x5, x5, F_SF);
                OR(xFlags, xFlags, x5);
            }
            if (BOX64DRENV(dynarec_safeflags)) {
                IFX (X_PF) emit_pf(dyn, ninst, vd, x3, x5);
            }
            break;
        }

        case 0xF5:
            INST_NAME("BZHI Gd, Ed, Vd");
            nextop = F8;
            SETFLAGS(X_ALL, SF_SET, NAT_FLAGS_NOFUSION);
            GETGDd;
            GETED(0);
            GETVD;
            CLEAR_FLAGS();
            if (rex.w) {
                ANDI(x4, vd, 0xc0);
                if (cpuext.zicond) {
                    ADDI(x6, xZR, -1);
                    SLL(x6, x6, vd);
                    CZERO_NEZ(x6, x6, x4);
                    IFX (X_CF) { SNEZ(x4, x4); }
                } else {
                    SNEZ(x4, x4);
                    ADDI(x6, x4, -1);
                    SLL(x6, x6, vd);
                }
                IFX (X_CF) { OR(xFlags, xFlags, x4); }
                ANDN(gd, ed, x6, x6);
            } else if (cpuext.zbb) {
                ANDI(x4, vd, 0xff);
                ADDI(x5, xZR, 32);
                MINU(x4, x4, x5);
                IFX (X_CF) {
                    SRLI(x5, x4, 5);
                    OR(xFlags, xFlags, x5);
                }
                ADDI(x6, xZR, -1);
                SLL(x6, x6, x4);
                ANDN_(gd, ed, x6);
            } else {
                ANDI(x4, vd, 0xff);
                ADDI(x5, xZR, 32);
                BGE_MARK(x4, x5);
                ADDI(x6, xZR, -1);
                SLL(x6, x6, x4);
                NOT(x6, x6);
                AND(gd, ed, x6);
                B_MARK2_nocond;
                MARK;
                MV(gd, ed);
                IFX (X_CF) {
                    ORI(xFlags, xFlags, 1 << F_CF);
                }
                MARK2;
                ZEROUP(gd);
            }
            IFX (X_ZF) {
                SET_FLAGS_EQZ(gd, F_ZF, x5);
            }
            IFX (X_SF) {
                SRLI(x5, gd, rex.w ? 63 : 31);
                SLLI(x5, x5, F_SF);
                OR(xFlags, xFlags, x5);
            }
            break;

        case 0xF7:
            INST_NAME("BEXTR Gd, Ed, Vd");
            nextop = F8;
            SETFLAGS(X_ALL, SF_SET, NAT_FLAGS_NOFUSION);
            GETGDd;
            GETED(0);
            GETVD;
            if (cpuext.zicond) {
                if (!rex.w && MODREG) {
                    ZEXTW2(x2, ed);
                    ed = x2;
                }
                ANDI(x4, vd, 0xc0);
                SRLI(x3, vd, 8);
                ANDI(x6, x3, 0xc0);
                ADDI(x5, xZR, -1);
                SLL(x5, x5, x3);
                SRL(x3, ed, vd);
                CZERO_NEZ(x5, x5, x6);
                ANDN(x3, x3, x5, x5);
                CZERO_NEZ(gd, x3, x4);
            } else {
                ANDI(x4, vd, 0xff);       // start
                SRLI(x3, vd, 8);
                ANDI(x3, x3, 0xff);       // length
                XOR(x5, x5, x5);
                BEQZ_MARK(x3);
                ADDI(x6, xZR, rex.w ? 64 : 32);
                BGE_MARK(x4, x6);
                SRLxw(x5, ed, x4);
                BLT_MARK(x6, x3);
                SUBxw(x6, x6, x3);
                SLLxw(x5, x5, x6);
                SRLxw(x5, x5, x6);
                MARK;
                MV(gd, x5);
                if (!rex.w) ZEROUP(gd);
            }
            CLEAR_FLAGS();
            IFX (X_ZF) {
                SET_FLAGS_EQZ(gd, F_ZF, x5);
            }
            break;
        default:
            DEFAULT;
    }
    return addr;
}
