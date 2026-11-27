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

uintptr_t dynarec64_66F20F(dynarec_rv64_t* dyn, uintptr_t addr, uintptr_t ip, int ninst, rex_t rex, int* ok, int* need_epilog)
{
    (void)ip;
    (void)need_epilog;

    uint8_t opcode = F8;
    uint8_t nextop, u8, s8;
    int32_t i32;
    uint8_t gd, ed;
    uint8_t wback, wb1, wb2, gback;
    uint8_t eb1, eb2;
    int64_t j64;
    uint64_t tmp64u, tmp64u2;
    int v0, v1;
    int q0, q1;
    int d0, d1;
    int64_t fixedaddress, gdoffset;
    int unscaled;

    MAYUSE(d0);
    MAYUSE(d1);
    MAYUSE(q0);
    MAYUSE(q1);
    MAYUSE(eb1);
    MAYUSE(eb2);
    MAYUSE(j64);

    static const int8_t round_round[] = { RD_RNE, RD_RDN, RD_RUP, RD_RTZ };

    switch (opcode) {
        case 0x38: // these are some more SSSE4.2+ opcodes
            opcode = F8;
            switch (opcode) {
                case 0xF1:
                    if (rex.w) return dynarec64_F20F(dyn, addr - 2, ip, ninst, rex, ok, need_epilog);
                    INST_NAME("CRC32 Gd, Ew");
                    nextop = F8;
                    GETGDw;
                    UP32_WRITE32(gd);
                    GETEW(x1, 0);
                    if (cpuext.zbc) {
                        XOR(x5, ed, gd);
                        SLLI(x5, x5, 48);
                        MOV32w(x2, 0x4869EC38DEA713F1ULL & 0xffff);
                        CLMUL(x5, x5, x2);
                        TABLE64_(x2, 0x105EC76F1ULL);
                        CLMULH(x5, x5, x2);
                        ZEXTW2(x4, gd);
                        SRLI(x4, x4, 16);
                        XOR(gd, x5, x4);
                    } else {
                        XOR(gd, gd, ed);
                        ZEROUP(gd);
                        TABLE64C(x2, const_crc32c_byte_table);
                        for (int byte = 0; byte < 2; ++byte) {
                            ANDI(x4, gd, 0xff);
                            if (cpuext.zba) {
                                SH2ADD(x4, x4, x2);
                            } else {
                                SLLI(x4, x4, 2);
                                ADD(x4, x4, x2);
                            }
                            LWU(x4, x4, 0);
                            SRLI(gd, gd, 8);
                            XOR(gd, gd, x4);
                        }
                    }
                    break;
                default:
                    DEFAULT;
            }
            break;
        default:
            DEFAULT;
    }
    return addr;
}
