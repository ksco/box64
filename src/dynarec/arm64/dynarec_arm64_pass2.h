#define INIT        dyn->native_size = 0
#define FINI                                                                                            \
        if(ninst) {                                                                                     \
                dyn->insts[ninst].address = (dyn->insts[ninst-1].address+dyn->insts[ninst-1].size);     \
                dyn->insts_size += 1+((dyn->insts[ninst-1].x64.size>(dyn->insts[ninst-1].size/4))?dyn->insts[ninst-1].x64.size:(dyn->insts[ninst-1].size/4))/15; \
        }

#define MESSAGE(A, ...) do {} while (0)
#define EMIT(A)     do{dyn->insts[ninst].size+=4; dyn->native_size+=4;}while(0)
#define NEW_INST                                                                                        \
        if(ninst) {                                                                                     \
                dyn->insts[ninst].address = (dyn->insts[ninst-1].address+dyn->insts[ninst-1].size);     \
                dyn->insts_size += 1+((dyn->insts[ninst-1].x64.size>(dyn->insts[ninst-1].size/4))?dyn->insts[ninst-1].x64.size:(dyn->insts[ninst-1].size/4))/15; \
                dyn->insts[ninst].ymm0_pass2 = dyn->ymm_zero;   \
        }
#define INST_EPILOG dyn->insts[ninst].epilog = dyn->native_size; 
#define INST_NAME(name) 
#define TABLE64(A, V)   {Table64(dyn, (V), 2); EMIT(0);}
#define TABLE64C(A, V)  {Table64(dyn, getConst(V), 2); EMIT(0);}
#define FTABLE64(A, V)  {mmx87_regs_t v = {.d = V}; Table64(dyn, v.q, 2); EMIT(0);}
#define CALLRET_RET()   do {dyn->callrets[dyn->callret_size].type = 0; dyn->callrets[dyn->callret_size++].offs = dyn->native_size; EMIT(ARCH_NOP); } while(0)
#define CALLRET_LOOP()   do {dyn->callrets[dyn->callret_size].type = 1; dyn->callrets[dyn->callret_size++].offs = dyn->native_size; EMIT(ARCH_NOP); } while(0)