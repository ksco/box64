/*********************************************************************
 * File automatically generated by rebuild_wrappers_32.py (v0.0.2.2) *
 *********************************************************************/
#ifndef __wrappedlibvdpauTYPES32_H_
#define __wrappedlibvdpauTYPES32_H_

#ifndef LIBNAME
#error You should only #include this file inside a wrapped*.c file
#endif
#ifndef ADDED_FUNCTIONS
#define ADDED_FUNCTIONS() 
#endif

typedef int32_t (*iFpipp_t)(void*, int32_t, void*, void*);

#define SUPER() ADDED_FUNCTIONS() \
	GO(vdp_device_create_x11, iFpipp_t)

#endif // __wrappedlibvdpauTYPES32_H_