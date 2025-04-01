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


uintptr_t dynarec64_DB(dynarec_la64_t* dyn, uintptr_t addr, uintptr_t ip, int ninst, rex_t rex, int rep, int* ok, int* need_epilog)
{
    (void)ip;
    (void)rep;
    (void)need_epilog;

    uint8_t nextop = F8;
    uint8_t ed;
    uint8_t wback;
    uint8_t u8;
    int64_t fixedaddress;
    int unscaled;
    int v1, v2, v3;
    int s0;
    int64_t j64;

    MAYUSE(s0);
    MAYUSE(v2);
    MAYUSE(v1);
    MAYUSE(j64);

    switch (nextop) {
        case 0xC0:
        case 0xC1:
        case 0xC2:
        case 0xC3:
        case 0xC4:
        case 0xC5:
        case 0xC6:
        case 0xC7:
            INST_NAME("FCMOVNB ST0, STx");
            READFLAGS(X_CF);
            RESTORE_EFLAGS(x1);
            v1 = x87_get_st(dyn, ninst, x1, x2, 0, X87_COMBINE(0, nextop & 7));
            v2 = x87_get_st(dyn, ninst, x1, x2, nextop & 7, X87_COMBINE(0, nextop & 7));
            ANDI(x1, xFlags, 1 << F_CF);
            CBNZ_NEXT(x1);
            if (ST_IS_F(0)) {
                FMOV_S(v1, v2);
            } else {
                FMOV_D(v1, v2); // F_CF==0
            }
            break;
        case 0xC8:
        case 0xC9:
        case 0xCA:
        case 0xCB:
        case 0xCC:
        case 0xCD:
        case 0xCE:
        case 0xCF:
            INST_NAME("FCMOVNE ST0, STx");
            READFLAGS(X_ZF);
            RESTORE_EFLAGS(x1);
            v1 = x87_get_st(dyn, ninst, x1, x2, 0, X87_COMBINE(0, nextop & 7));
            v2 = x87_get_st(dyn, ninst, x1, x2, nextop & 7, X87_COMBINE(0, nextop & 7));
            ANDI(x1, xFlags, 1 << F_ZF);
            CBNZ_NEXT(x1);
            if (ST_IS_F(0)) {
                FMOV_S(v1, v2);
            } else {
                FMOV_D(v1, v2); // F_ZF==0
            }
            break;
        case 0xD0:
        case 0xD1:
        case 0xD2:
        case 0xD3:
        case 0xD4:
        case 0xD5:
        case 0xD6:
        case 0xD7:
            INST_NAME("FCMOVNBE ST0, STx");
            READFLAGS(X_CF | X_ZF);
            RESTORE_EFLAGS(x1);
            v1 = x87_get_st(dyn, ninst, x1, x2, 0, X87_COMBINE(0, nextop & 7));
            v2 = x87_get_st(dyn, ninst, x1, x2, nextop & 7, X87_COMBINE(0, nextop & 7));
            ANDI(x1, xFlags, (1 << F_CF) | (1 << F_ZF));
            CBNZ_NEXT(x1);
            if (ST_IS_F(0)) {
                FMOV_S(v1, v2);
            } else {
                FMOV_D(v1, v2); // F_CF==0 & F_ZF==0
            }
            break;
        case 0xD8:
        case 0xD9:
        case 0xDA:
        case 0xDB:
        case 0xDC:
        case 0xDD:
        case 0xDE:
        case 0xDF:
            INST_NAME("FCMOVNU ST0, STx");
            READFLAGS(X_PF);
            RESTORE_EFLAGS(x1);
            v1 = x87_get_st(dyn, ninst, x1, x2, 0, X87_COMBINE(0, nextop & 7));
            v2 = x87_get_st(dyn, ninst, x1, x2, nextop & 7, X87_COMBINE(0, nextop & 7));
            ANDI(x1, xFlags, 1 << F_PF);
            CBNZ_NEXT(x1);
            if (ST_IS_F(0)) {
                FMOV_S(v1, v2);
            } else {
                FMOV_D(v1, v2); // F_PF==0
            }
            break;
        case 0xE1:
            INST_NAME("FDISI8087_NOP"); // so.. NOP?
            break;
        case 0xE2:
            INST_NAME("FNCLEX");
            LD_H(x2, xEmu, offsetof(x64emu_t, sw));
            ANDI(x2, x2, ~(0xff));  // IE .. PE, SF, ES
            MOV32w(x1, ~(1 << 15)); // B
            AND(x2, x2, x1);
            ST_H(x2, xEmu, offsetof(x64emu_t, sw));
            break;
        case 0xE3:
            INST_NAME("FNINIT");
            MESSAGE(LOG_DUMP, "Need Optimization\n");
            x87_purgecache(dyn, ninst, 0, x1, x2, x3);
            CALL(reset_fpu, -1);
            break;
        case 0xE8:
        case 0xE9:
        case 0xEA:
        case 0xEB:
        case 0xEC:
        case 0xED:
        case 0xEE:
        case 0xEF:
            INST_NAME("FUCOMI ST0, STx");
            SETFLAGS(X_ALL, SF_SET, NAT_FLAGS_NOFUSION);
            v1 = x87_get_st(dyn, ninst, x1, x2, 0, X87_COMBINE(0, nextop & 7));
            v2 = x87_get_st(dyn, ninst, x1, x2, nextop & 7, X87_COMBINE(0, nextop & 7));
            if (ST_IS_F(0)) {
                FCOMIS(v1, v2, x1, x2);
            } else {
                FCOMID(v1, v2, x1, x2);
            }
            break;
        case 0xF0:
        case 0xF1:
        case 0xF2:
        case 0xF3:
        case 0xF4:
        case 0xF5:
        case 0xF6:
        case 0xF7:
            INST_NAME("FCOMI ST0, STx");
            SETFLAGS(X_ALL, SF_SET, NAT_FLAGS_NOFUSION);
            v1 = x87_get_st(dyn, ninst, x1, x2, 0, X87_COMBINE(0, nextop & 7));
            v2 = x87_get_st(dyn, ninst, x1, x2, nextop & 7, X87_COMBINE(0, nextop & 7));
            if (ST_IS_F(0)) {
                FCOMIS(v1, v2, x1, x2);
            } else {
                FCOMID(v1, v2, x1, x2);
            }
            break;

        case 0xE0:
        case 0xE4:
        case 0xE5:
        case 0xE6:
        case 0xE7:
            DEFAULT;
            break;

        default:
            switch ((nextop >> 3) & 7) {
                case 0:
                    INST_NAME("FILD ST0, Ed");
                    X87_PUSH_OR_FAIL(v1, dyn, ninst, x1, LSX_CACHE_ST_D);
                    addr = geted(dyn, addr, ninst, nextop, &ed, x2, x1, &fixedaddress, rex, NULL, 1, 0);
                    FLD_S(v1, ed, fixedaddress);
                    FFINT_D_W(v1, v1); // i32 -> double
                    break;
                case 1:
                    INST_NAME("FISTTP Ed, ST0");
                    v1 = x87_get_st(dyn, ninst, x1, x2, 0, LSX_CACHE_ST_D);
                    addr = geted(dyn, addr, ninst, nextop, &wback, x3, x4, &fixedaddress, rex, NULL, 1, 0);
                    if (!BOX64ENV(dynarec_fastround)) {
                        FSFLAGSI(0, x5); // reset all bits
                    }
                    v2 = fpu_get_scratch(dyn);
                    FTINTRZ_W_D(v2, v1);
                    if (!BOX64ENV(dynarec_fastround)) {
                        FRFLAGS(x5); // get back FCSR1 Enable to check the IOC bit
                        FRFLAGSTEST(x5, (1 << FR_V) );
                        BEQZ_MARK(x5);
                        MOV32w(x4, 0x80000000);
                        MOVGR2FR_W(v2, x4);
                        MARK;
                    }
                    FST_S(v2, wback, fixedaddress);
                    X87_POP_OR_FAIL(dyn, ninst, x3);
                    break;
                case 2:
                    INST_NAME("FIST Ed, ST0");
                    DEFAULT;
                    break;
                case 3:
                    INST_NAME("FISTP Ed, ST0");
                    v1 = x87_get_st(dyn, ninst, x1, x2, 0, LSX_CACHE_ST_D);
                    u8 = x87_setround(dyn, ninst, x1, x6);
                    addr = geted(dyn, addr, ninst, nextop, &wback, x2, x3, &fixedaddress, rex, NULL, 1, 0);
                    v2 = fpu_get_scratch(dyn);
                    if (!BOX64ENV(dynarec_fastround)) {
                        FSFLAGSI(0, x4); // reset all bits
                    }
                    v2 = fpu_get_scratch(dyn);
                    FTINT_W_D(v2, v1);
                    if (!BOX64ENV(dynarec_fastround)) {
                        FRFLAGS(x5); // get back FPSR to check the IOC bit
                        FRFLAGSTEST(x5, (1 << FR_V) );
                        BEQ_MARK2(x5, xZR);
                        MOV32w(x4, 0x80000000);
                        MOVGR2FR_W(v2, x4);
                    }
                    MARK2;
                    x87_restoreround(dyn, ninst, u8);
                    FST_S(v2, wback, fixedaddress);
                    X87_POP_OR_FAIL(dyn, ninst, x3);
                    break;
                case 5:
                    INST_NAME("FLD tbyte");
                    addr = geted(dyn, addr, ninst, nextop, &ed, x1, x2, &fixedaddress, rex, NULL, 8, 0);
                    // if ((PK(0) == 0xDB && ((PK(1) >> 3) & 7) == 7) || (PK(0) >= 0x40 && PK(0) <= 0x4f && PK(1) == 0xDB && ((PK(2) >> 3) & 7) == 7)) {
                    //     NOTEST(x5);
                    //     // the FLD is immediatly followed by an FSTP
                    //     LD_D(x5, ed, fixedaddress + 0);
                    //     LD_H(x6, ed, fixedaddress + 8);
                    //     // no persistant scratch register, so unrool both instruction here...
                    //     MESSAGE(LOG_DUMP, "\tHack: FSTP tbyte\n");
                    //     nextop = F8; // 0xDB or rex
                    //     if (nextop >= 0x40 && nextop <= 0x4f) {
                    //         rex.rex = nextop;
                    //         nextop = F8; // 0xDB
                    //     } else
                    //         rex.rex = 0;
                    //     nextop = F8; // modrm
                    //     addr = geted(dyn, addr, ninst, nextop, &ed, x1, x2, &fixedaddress, rex, NULL, 8, 0);
                    //     ST_D(x5, ed, fixedaddress + 0);
                    //     ST_H(x6, ed, fixedaddress + 8);
                    // } else 
                    {
                        if (BOX64ENV(x87_no80bits)) {
                            X87_PUSH_OR_FAIL(v1, dyn, ninst, x1, LSX_CACHE_ST_D);
                            FLD_D(v1, ed, fixedaddress);
                        } else if(la64_lbt){
                            X87_PUSH_OR_FAIL(v1, dyn, ninst, x1, LSX_CACHE_ST_D);
                            v2 = fpu_get_scratch(dyn);
                            v3 = fpu_get_scratch(dyn);
                            FLD_D(v2, ed, fixedaddress);
                            LD_H(x4, ed, fixedaddress+8);
                            MOVGR2FR_W(v3, x4);
                            FCVT_D_LD(v1, v2, v3);
                        } else {
                            ADDI_D(x1, ed, fixedaddress);
                            X87_PUSH_EMPTY_OR_FAIL(dyn, ninst, x3);
                            x87_reflectcount(dyn, ninst, x3, x4);
                            CALL2(native_fld, -1, x1, 0);
                            x87_unreflectcount(dyn, ninst, x3, x4, x5);
                            
                        }
                    }
                    break;
                case 7:
                    INST_NAME("FSTP tbyte");
                    if (BOX64ENV(x87_no80bits)) {
                        v1 = x87_get_st(dyn, ninst, x1, x2, 0, LSX_CACHE_ST_D);
                        addr = geted(dyn, addr, ninst, nextop, &wback, x2, x1, &fixedaddress, rex, NULL, 1, 0);
                        FST_D(v1, wback, fixedaddress);
                    } else if(la64_lbt){
                        v1 = x87_get_st(dyn, ninst, x1, x2, 0, LSX_CACHE_ST_D);
                        addr = geted(dyn, addr, ninst, nextop, &wback, x2, x1, &fixedaddress, rex, NULL, 1, 0);
                        v2 = fpu_get_scratch(dyn);
                        v3 = fpu_get_scratch(dyn);
                        FCVT_LD_D(v2, v1);
                        FCVT_UD_D(v3, v1);
                        MOVFR2GR_S(x4, v3);
                        FST_D(v2, wback, fixedaddress);
                        ST_H(x4, wback, fixedaddress+8);
                    }else{
                        x87_forget(dyn, ninst, x1, x3, 0);
                        addr = geted(dyn, addr, ninst, nextop, &ed, x1, x2, &fixedaddress, rex, NULL, 0, 0);
                        x87_reflectcount(dyn, ninst, x3, x4);
                        CALL2(native_fstp, -1, ed, 0);
                        x87_unreflectcount(dyn, ninst, x3, x4, x5);
                    }
                    X87_POP_OR_FAIL(dyn, ninst, x3);
                    break;
                default:
                    DEFAULT;
            }
    }
    return addr;
}
