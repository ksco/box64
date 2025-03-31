#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <errno.h>

#include "debug.h"
#include "box64context.h"
#include "dynarec.h"
#include "emu/x64emu_private.h"
#include "emu/x64run_private.h"
#include "x64run.h"
#include "x64emu.h"
#include "box64stack.h"
#include "callback.h"
#include "emu/x64run_private.h"
#include "x64trace.h"
#include "emu/x87emu_private.h"
#include "dynarec_native.h"

#include "la64_printer.h"
#include "dynarec_la64_private.h"
#include "../dynarec_helper.h"
#include "dynarec_la64_functions.h"

uintptr_t dynarec64_DF(dynarec_la64_t* dyn, uintptr_t addr, uintptr_t ip, int ninst, rex_t rex, int rep, int* ok, int* need_epilog)
{
    (void)ip;
    (void)rep;
    (void)need_epilog;

    uint8_t nextop = F8;
    uint8_t ed, wback, u8;
    int v1, v2;
    int s0;
    int64_t j64;
    int64_t fixedaddress;

    MAYUSE(s0);
    MAYUSE(v2);
    MAYUSE(v1);
    MAYUSE(j64);

    switch (nextop) {
        case 0xC0 ... 0xC7:
            INST_NAME("FFREEP STx");
            // not handling Tag...
            X87_POP_OR_FAIL(dyn, ninst, x3);
            break;

        case 0xE0:
            INST_NAME("FNSTSW AX");
            LD_WU(x2, xEmu, offsetof(x64emu_t, top));
            if (dyn->lsx.x87stack) {
                ADDI_W(x2, x2, -dyn->lsx.x87stack);
                ANDI(x2, x2, 0x7);
            }
            LD_HU(x1, xEmu, offsetof(x64emu_t, sw));
            MOV32w(x3, 0b1100011111111111); // mask
            AND(x1, x1, x3);
            SLLI_W(x2, x2, 11);
            OR(x1, x1, x2); // inject top
            ST_H(x1, xEmu, offsetof(x64emu_t, sw));
            SRLI_D(xRAX, xRAX, 16);
            SLLI_D(xRAX, xRAX, 16);
            OR(xRAX, xRAX, x1);
            break;
        case 0xE8 ... 0xF7:
            if (nextop < 0xF0) {
                INST_NAME("FUCOMIP ST0, STx");
            } else {
                INST_NAME("FCOMIP ST0, STx");
            }
            SETFLAGS(X_ALL, SF_SET, NAT_FLAGS_NOFUSION);
            SET_DFNONE();
            v1 = x87_get_st(dyn, ninst, x1, x2, 0, X87_COMBINE(0, nextop & 7));
            v2 = x87_get_st(dyn, ninst, x1, x2, nextop & 7, X87_COMBINE(0, nextop & 7));
            RESTORE_EFLAGS(x1);
            CLEAR_FLAGS(x3);
            IFX (X_ZF | X_PF | X_CF) {
                if (ST_IS_F(0)) {
                    FCMP_S(fcc0, v1, v1, cEQ);
                    FCMP_S(fcc1, v2, v2, cEQ);
                    BCEQZ(fcc0, 8 * 4);
                    BCEQZ(fcc1, 7 * 4); // undefined/NaN
                    FCMP_S(fcc2, v1, v2, cEQ);
                    BCNEZ(fcc2, 7 * 4);           // equal
                    FCMP_S(fcc3, v1, v2, cLT);       // x3 = (v1<v2)?1:0
                    MOVCF2GR(x3, fcc3);
                    OR(xFlags, xFlags, x3); // CF is the least significant bit
                    B(16);                  // end
                    // NaN
                    ORI(xFlags, xFlags, (1 << F_ZF) | (1 << F_PF) | (1 << F_CF));
                    B(8); // end
                    // equal
                    ORI(xFlags, xFlags, 1 << F_ZF);
                    // end
                } else {
                    FCMP_D(fcc0, v1, v1, cEQ);
                    FCMP_D(fcc1, v2, v2, cEQ);
                    BCEQZ(fcc0, 8 * 4);
                    BCEQZ(fcc1, 7 * 4); // undefined/NaN
                    FCMP_D(fcc2, v1, v2, cEQ);
                    BCNEZ(fcc2, 7 * 4);           // equal
                    FCMP_D(fcc3, v1, v2, cLT);       // x3 = (v1<v2)?1:0
                    MOVCF2GR(x3, fcc3);
                    OR(xFlags, xFlags, x3); // CF is the least significant bit
                    B(16);                  // end
                    // NaN
                    ORI(xFlags, xFlags, (1 << F_ZF) | (1 << F_PF) | (1 << F_CF));
                    B(8); // end
                    // equal
                    ORI(xFlags, xFlags, 1 << F_ZF);
                    // end
                }
            }
            SPILL_EFLAGS();
            X87_POP_OR_FAIL(dyn, ninst, x3);
            break;
        case 0xC8 ... 0xDF:
        case 0xE1 ... 0xE7:
        case 0xF8 ... 0xFF:
            DEFAULT;
            break;

        default:
            switch ((nextop >> 3) & 7) {
                case 0:
                    INST_NAME("FILD ST0, Ew");
                    X87_PUSH_OR_FAIL(v1, dyn, ninst, x1, LSX_CACHE_ST_F);
                    addr = geted(dyn, addr, ninst, nextop, &wback, x3, x4, &fixedaddress, rex, NULL, 1, 0);
                    LD_H(x4, wback, fixedaddress);
                    MOVGR2FR_D(v1, x4);
                    if (ST_IS_F(0)) {
                        FFINT_S_L(v1, v1);
                    } else {
                        FFINT_D_L(v1, v1);
                    }
                    break;
                case 1:
                    INST_NAME("FISTTP Ew, ST0");
                    v1 = x87_get_st(dyn, ninst, x1, x2, 0, LSX_CACHE_ST_F);
                    addr = geted(dyn, addr, ninst, nextop, &wback, x3, x4, &fixedaddress, rex, NULL, 1, 0);
                    if (!BOX64ENV(dynarec_fastround)) {
                        FSFLAGSI(0, x5); // reset all bits
                    }
                    v2 = fpu_get_scratch(dyn);
                    if (ST_IS_F(0)) {
                        FTINTRZ_W_S(v2, v1);
                        MOVFR2GR_S(x4, v2);
                    } else {
                        FTINTRZ_W_D(v2, v1);
                        MOVFR2GR_D(x4, v2);
                    }
                    if (!BOX64ENV(dynarec_fastround)) {
                        FRFLAGS(x5); // get back FPSR to check the IOC bit
                        FRFLAGSTEST(x5, (1 << FR_V) );
                        BNEZ_MARK(x5);
                        SLLI_W(x5, x4, 16);
                        SRAI_W(x5, x5, 16);
                        ZEROUP(x5);
                        BEQ_MARK2(x5, x4);
                        MARK;
                        MOV32w(x4, 0x8000);
                        
                    }
                    MARK2;
                    ST_H(x4, wback, fixedaddress);
                    X87_POP_OR_FAIL(dyn, ninst, x3);
                    break;
                case 2:
                    INST_NAME("FIST Ew, ST0");
                    v1 = x87_get_st(dyn, ninst, x1, x2, 0, LSX_CACHE_ST_F);
                    u8 = x87_setround(dyn, ninst, x1, x6);
                    addr = geted(dyn, addr, ninst, nextop, &wback, x2, x3, &fixedaddress, rex, NULL, 1, 0);
                    if (!BOX64ENV(dynarec_fastround)) {
                        FSFLAGSI(0, x4); // reset all bits
                    }
                    v2 = fpu_get_scratch(dyn);
                    if (ST_IS_F(0)) {
                        FTINT_W_S(v2, v1);
                        MOVFR2GR_S(x4, v2);
                    } else {
                        FTINT_W_D(v2, v1);
                        MOVFR2GR_D(x4, v2);
                    }
                    x87_restoreround(dyn, ninst, u8);
                    if (!BOX64ENV(dynarec_fastround)) {
                        FRFLAGS(x5); // get back FPSR to check the IOC bit
                        FRFLAGSTEST(x5, (1 << FR_V) );
                        BNEZ_MARK(x5);
                        SLLI_W(x5, x4, 16);
                        SRAI_W(x5, x5, 16);
                        ZEROUP(x5);                        
                        BEQ_MARK2(x5, x4);
                        MARK;
                        MOV32w(x4, 0x8000);
                    }
                    MARK2;
                    ST_H(x4, wback, fixedaddress);
                    break;
                case 3:
                    INST_NAME("FISTP Ew, ST0");
                    v1 = x87_get_st(dyn, ninst, x1, x2, 0, LSX_CACHE_ST_F);
                    u8 = x87_setround(dyn, ninst, x1, x6);
                    addr = geted(dyn, addr, ninst, nextop, &wback, x2, x3, &fixedaddress, rex, NULL, 1, 0);
                    if (!BOX64ENV(dynarec_fastround)) {
                        FSFLAGSI(0, x4); // reset all bits
                    }
                    v2 = fpu_get_scratch(dyn);
                    if (ST_IS_F(0)) {
                        FTINT_W_S(v2, v1);
                        MOVFR2GR_S(x4, v2);
                    } else {
                        FTINT_W_D(v2, v1);
                        MOVFR2GR_D(x4, v2);
                    }
                    x87_restoreround(dyn, ninst, u8);
                    if (!BOX64ENV(dynarec_fastround)) {
                        FRFLAGS(x5); // get back FPSR to check the IOC bit
                        FRFLAGSTEST(x5, (1 << FR_V) );
                        BNEZ_MARK(x5);
                        SLLI_W(x5, x4, 16);
                        SRAI_W(x5, x5, 16);
                        ZEROUP(x5);
                        BEQ_MARK2(x5, x4);
                        MARK;
                        MOV32w(x4, 0x8000);
                    }
                    MARK2;
                    ST_H(x4, wback, fixedaddress);
                    X87_POP_OR_FAIL(dyn, ninst, x3);
                    break;
                case 4:
                    INST_NAME("FBLD ST0, tbytes");
                    X87_PUSH_EMPTY_OR_FAIL(dyn, ninst, x1);
                    addr = geted(dyn, addr, ninst, nextop, &ed, x1, x2, &fixedaddress, rex, NULL, 0, 0);
                    s0 = x87_stackcount(dyn, ninst, x3);
                    CALL2(fpu_fbld, -1, ed, 0);
                    x87_unstackcount(dyn, ninst, x3, s0);
                    break;
                case 5:
                    INST_NAME("FILD ST0, i64");
                    X87_PUSH_OR_FAIL(v1, dyn, ninst, x1, LSX_CACHE_ST_I64);
                    addr = geted(dyn, addr, ninst, nextop, &wback, x2, x3, &fixedaddress, rex, NULL, 1, 0);
                    FLD_D(v1, wback, fixedaddress);
                    if (!ST_IS_I64(0)) {
                        if (rex.is32bits) {
                            // need to also feed the STll stuff...
                            ADDI_D(x4, xEmu, offsetof(x64emu_t, fpu_ll));
                            LD_WU(x5, xEmu, offsetof(x64emu_t, top));
                            int a = 0 - dyn->lsx.x87stack;
                            if (a) {
                                ADDI_W(x5, x5, a);
                                ANDI(x5, x5, 0x7);
                            }
                            ALSL_D(x5, x5, x4, 4); // fpu_ll is 2 i64
                            FST_D(v1, x5, 8); // ll
                        }
                        FFINT_D_L(v1, v1);
                        if (rex.is32bits) {
                            FST_D(v1, x5, 0); // ref
                        }
                    }
                    break;
                case 6:
                    INST_NAME("FBSTP tbytes, ST0");
                    x87_forget(dyn, ninst, x1, x2, 0);
                    addr = geted(dyn, addr, ninst, nextop, &ed, x1, x2, &fixedaddress, rex, NULL, 0, 0);
                    s0 = x87_stackcount(dyn, ninst, x3);
                    CALL2(fpu_fbst, -1, ed, 0);
                    x87_unstackcount(dyn, ninst, x3, s0);
                    X87_POP_OR_FAIL(dyn, ninst, x3);
                    break;
                case 7:
                    INST_NAME("FISTP i64, ST0");
                    v1 = x87_get_st(dyn, ninst, x1, x2, 0, LSX_CACHE_ST_I64);
                    if (!ST_IS_I64(0)) {
                        u8 = x87_setround(dyn, ninst, x1, x6);
                    }
                    addr = geted(dyn, addr, ninst, nextop, &wback, x2, x3, &fixedaddress, rex, NULL, 1, 0);

                    if (ST_IS_I64(0)) {
                        FST_D(v1, wback, fixedaddress);
                    } else {
                        if (rex.is32bits) {
                            // need to check STll first...
                            ADDI_D(x4, xEmu, offsetof(x64emu_t, fpu_ll));
                            LD_WU(x5, xEmu, offsetof(x64emu_t, top));
                            int a = 0 - dyn->lsx.x87stack;
                            if (a) {
                                ADDI_W(x5, x5, a);
                                ANDI(x5, x5, 0x7);
                            }
                            ALSL_D(x5, x5, x4, 4);// fpu_ll is 2 i64
                            MOVFR2GR_D(x3, v1);
                            LD_D(x6, x5, 0); // ref
                            BNE_MARK(x6, x3);
                            LD_D(x6, x5, 8); // ll
                            ST_D(x6, wback, fixedaddress);
                            B_MARK3_nocond;
                            MARK;
                        }

                        if (!BOX64ENV(dynarec_fastround)) {
                            FSFLAGSI(0, x7); // reset all bits
                        }
                        v2 = fpu_get_scratch(dyn);
                        FTINT_L_D(v2, v1);
                        if (!BOX64ENV(dynarec_fastround)) {
                            FRFLAGS(x5); // get back FPSR to check the IOC bit
                            FRFLAGSTEST(x5, (1 << FR_V) );
                            BEQ_MARK2(x5, xZR);
                            MOV64x(x4, 0x8000000000000000LL);
                            MOVGR2FR_D(v2, x4);
                        }
                        MARK2;
                        FST_D(v2, wback, fixedaddress);
                        MARK3;
                        x87_restoreround(dyn, ninst, u8);
                    }
                    X87_POP_OR_FAIL(dyn, ninst, x3);
                    break;
                default:
                    DEFAULT;
                    break;
            }
    }
    return addr;
}
