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

uintptr_t dynarec64_AVX_F3_0F38(dynarec_rv64_t* dyn, uintptr_t addr, uintptr_t ip, int ninst, vex_t vex, int* ok, int* need_epilog)
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
        case 0xF5:
            INST_NAME("PEXT Gd, Vd, Ed");
            nextop = F8;
            GETGDd;
            GETVD;
            GETED(0);
            if (rex.w || !MODREG) {
                MV(x4, ed);
            } else {
                ZEXTW2(x4, ed);
            }
            if (gd == vd) {
                gb1 = gd;
                gd = x6;
            } else {
                gb1 = 0;
            }
            ADDIxw(x5, x4, 1);
            if (rex.w) {
                MV(gd, vd);
            } else {
                ZEXTW2(gd, vd);
            }
            BEQZ_MARK2(x5);
            ADDI(gd, xZR, 0);
            BEQZ_MARK2(x4);
            if (cpuext.vector && cpuext.vlen >= 32 && cpuext.zbb) {
                ADDI(x5, x4, -1);
                ANDN(x2, x4, x5, x2);
                AND(x5, x4, x5);
                AND(x2, x2, vd);
                SNEZ(gd, x2);
                BEQZ_MARK2(x5);
                CPOP(x2, x5);
                SLTIU(x2, x2, rex.w ? 11 : 8);
                BNEZ_MARK4(x2);

                rvv_config_t incoming = dyn->rvv;
                int bit_count = rex.w ? 64 : 32;
                int grouping = bit_count > cpuext.vlen ? VECTOR_LMUL2 : VECTOR_LMUL1;
                int selection = vpu_get_scratch(dyn);
                int source_bits = vpu_get_scratch_lmul(dyn, grouping);
                int extracted = vpu_get_scratch_lmul(dyn, grouping);
                rvv_set_config(dyn, ninst, x2, VECTOR_SEW64, VECTOR_LMUL1, 1);
                VMV_S_X(VMASK, vd);
                VMV_S_X(selection, x4);
                rvv_set_config(dyn, ninst, x2, VECTOR_SEW8, grouping, bit_count);
                VMV_V_I(source_bits, 0);
                VMERGE_VIM(source_bits, source_bits, 1);
                VMV_V_I(extracted, 0);
                VCOMPRESS_VM(extracted, source_bits, selection);
                VMSNE_VI(VMASK, extracted, 0, VECTOR_UNMASKED);
                rvv_set_config(dyn, ninst, x2, VECTOR_SEW64, VECTOR_LMUL1, 1);
                VMV_X_S(gd, VMASK);
                if (!rex.w) { ZEXTW2(gd, gd); }
                if (incoming.vl)
                    rvv_set_config(dyn, ninst, x2, incoming.sew, incoming.lmul, incoming.vl);
                dyn->rvv = incoming;
                B_MARK2_nocond;
                MARK4;
                MV(x4, x5);
                ADDI(x3, xZR, 2);
            } else {
                ADDI(x3, xZR, 1);
            }
            MARK;
            ADDI(x5, x4, -1);
            ANDN(x2, x4, x5, x2);
            AND(x4, x4, x5);
            AND(x2, vd, x2);
            if (cpuext.zicond) {
                CZERO_EQZ(x2, x3, x2);
                OR(gd, gd, x2);
            } else if (cpuext.xtheadcondmov) {
                OR(x5, gd, x3);
                TH_MVNEZ(gd, x5, x2);
            } else {
                BEQZ_MARK3(x2);
                OR(gd, gd, x3);
            }
            MARK3;
            SLLI(x3, x3, 1);
            BNEZ_MARK(x4);
            MARK2;
            if (gb1) MV(gb1, gd);
            break;

        case 0xF7:
            INST_NAME("SARX Gd, Ed, Vd");
            nextop = F8;
            GETGDd;
            GETED(0);
            GETVD;
            ANDI(x5, vd, rex.w ? 0x3f : 0x1f);
            SRAxw(gd, ed, x5);
            break;
        default:
            DEFAULT;
    }
    return addr;
}
