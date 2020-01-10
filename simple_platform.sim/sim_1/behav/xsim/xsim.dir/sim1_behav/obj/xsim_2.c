/**********************************************************************/
/*   ____  ____                                                       */
/*  /   /\/   /                                                       */
/* /___/  \  /                                                        */
/* \   \   \/                                                         */
/*  \   \        Copyright (c) 2003-2013 Xilinx, Inc.                 */
/*  /   /        All Right Reserved.                                  */
/* /---/   /\                                                         */
/* \   \  /  \                                                        */
/*  \___\/\___\                                                       */
/**********************************************************************/


#include "iki.h"
#include <string.h>
#include <math.h>
#ifdef __GNUC__
#include <stdlib.h>
#else
#include <malloc.h>
#define alloca _alloca
#endif
#include "svdpi.h"
#include <cstring>


#if (defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
#define DPI_DLLISPEC __declspec(dllimport)
#define DPI_DLLESPEC __declspec(dllexport)
#else
#define DPI_DLLISPEC
#define DPI_DLLESPEC
#endif


extern "C"
{
	DPI_DLLISPEC extern void  DPISetMode(int mode) ;
	DPI_DLLISPEC extern int   DPIGetMode() ; 
	DPI_DLLISPEC extern void  DPIAllocateExportedFunctions(int size) ;
	DPI_DLLISPEC extern void  DPIAddExportedFunction(int index, const char* value) ;
	DPI_DLLISPEC extern void  DPIAllocateSVCallerName(int index, const char* y) ;
	DPI_DLLISPEC extern void  DPISetCallerName(int index, const char* y) ;
	DPI_DLLISPEC extern void  DPISetCallerLine(int index, unsigned int y) ;
	DPI_DLLISPEC extern void  DPISetCallerOffset(int index, int y) ;
	DPI_DLLISPEC extern void  DPIAllocateDPIScopes(int size) ;
	DPI_DLLISPEC extern void  DPISetDPIScopeFunctionName(int index, const char* y) ;
	DPI_DLLISPEC extern void  DPISetDPIScopeHierarchy(int index, const char* y) ;
	DPI_DLLISPEC extern void  DPIRelocateDPIScopeIP(int index, char* IP) ;
	DPI_DLLISPEC extern void  DPIAddDPIScopeAccessibleFunction(int index, unsigned int y) ;
	DPI_DLLISPEC extern void  DPIFlushAll() ;
	DPI_DLLISPEC extern void  DPIVerifyScope() ;
	DPI_DLLISPEC extern char* DPISignalHandle(char* sigHandle, int length) ;
	DPI_DLLISPEC extern char* DPIMalloc(unsigned noOfBytes) ;
	DPI_DLLISPEC extern void  DPITransactionAuto(char* srcValue, unsigned int startIndex, unsigned int endIndex, char* net) ;
	DPI_DLLISPEC extern void  DPIScheduleTransactionBlocking(char* var, char* driver, char* src, unsigned setback, unsigned lenMinusOnne) ;
	DPI_DLLISPEC extern void  DPIMemsetSvToDpi(char* dst, char* src, int numCBytes, int is2state) ;
	DPI_DLLISPEC extern void  DPIMemsetDpiToSv(char* dst, char* src, int numCBytes, int is2state) ;
	DPI_DLLISPEC extern void  DPIMemsetSvLogic1ToDpi(char* dst, char* src) ;
	DPI_DLLISPEC extern void  DPIMemsetDpiToSvLogic1(char* dst, char* src) ;
	DPI_DLLISPEC extern void  DPIMemsetDpiToSvUnpackedLogic(char* dst, char* src, int* numRshift, int* shift) ;
	DPI_DLLISPEC extern void  DPIMemsetDpiToSvUnpackedLogicWithPackedDim(char* dst, char* src, int pckedSz, int* numRshift, int* shift) ;
	DPI_DLLISPEC extern void  DPIMemsetSvToDpiUnpackedLogic(char* dst, char* src, int* numRshift, int* shift) ;
	DPI_DLLISPEC extern void  DPIMemsetSvToDpiUnpackedLogicWithPackedDim(char* dst, char* src, int pckdSz, int* numRshift, int* shift) ;
	DPI_DLLISPEC extern void  DPIMemsetDpiToSvUnpackedBit(char* dst, char* src, int* numRshift, int* shift) ;
	DPI_DLLISPEC extern void  DPIMemsetDpiToSvUnpackedBitWithPackedDim(char* dst, char* src, int pckdSz, int* numRshift, int* shift) ;
	DPI_DLLISPEC extern void  DPIMemsetSvToDpiUnpackedBit(char* dst, char* src, int* numRshift, int* shift) ;
	DPI_DLLISPEC extern void  DPIMemsetSvToDpiUnpackedBitWithPackedDim(char* dst, char* src, int pckdSz, int* numRshift, int* shift) ;
	DPI_DLLISPEC extern void  DPISetFuncName(const char* funcName) ;
	DPI_DLLISPEC extern int   staticScopeCheck(const char* calledFunction) ;
	DPI_DLLISPEC extern void  DPIAllocateSVCallerInfo(int size) ;
	DPI_DLLISPEC extern void* DPICreateContext(int scopeId, char* IP, int callerIdx);
	DPI_DLLISPEC extern void* DPIGetCurrentContext();
	DPI_DLLISPEC extern void  DPISetCurrentContext(void*);
	DPI_DLLISPEC extern void  DPIRemoveContext(void*);
	DPI_DLLISPEC extern int   svGetScopeStaticId();
	DPI_DLLISPEC extern char* svGetScopeIP();
	DPI_DLLISPEC extern unsigned DPIGetUnpackedSizeFromSVOpenArray(svOpenArray*);
	DPI_DLLISPEC extern unsigned DPIGetConstraintSizeFromSVOpenArray(svOpenArray*, int);
	DPI_DLLISPEC extern int   topOffset() ;
	DPI_DLLISPEC extern char* DPIInitializeFunction(char* p, unsigned size, long long offset) ;
	DPI_DLLISPEC extern void  DPIInvokeFunction(char* processPtr, char* SP, void* func, char* IP) ;
	DPI_DLLISPEC extern void  DPIDeleteFunctionInvocation(char* SP) ;
	DPI_DLLISPEC extern void  DPISetTaskScopeId(int scopeId) ;
	DPI_DLLISPEC extern void  DPISetTaskCaller(int index) ;
	DPI_DLLISPEC extern int   DPIGetTaskCaller() ;
	DPI_DLLISPEC extern char* DPIInitializeTask(long long subprogInDPOffset, char* scopePropInIP, unsigned size, char* parentBlock) ;
	DPI_DLLISPEC extern void  DPIInvokeTask(long long subprogInDPOffset, char* SP, void* func, char* IP) ;
	DPI_DLLISPEC extern void  DPIDeleteTaskInvocation(char* SP) ;
	DPI_DLLISPEC extern void* DPICreateTaskContext(int (*wrapper)(char*, char*, char*), char* DP, char* IP, char* SP, size_t stackSz) ;
	DPI_DLLISPEC extern void  DPIRemoveTaskContext(void*) ;
	DPI_DLLISPEC extern void  DPICallCurrentContext() ;
	DPI_DLLISPEC extern void  DPIYieldCurrentContext() ;
	DPI_DLLISPEC extern void* DPIGetCurrentTaskContext() ;
	DPI_DLLISPEC extern int   DPIRunningInNewContext() ;
	DPI_DLLISPEC extern void  DPISetCurrentTaskContext(void* x) ;
}

namespace XILINX_DPI { 

	void dpiInitialize()
	{
		DPIAllocateExportedFunctions(2) ;
		DPIAddExportedFunction(0, "wishbone_write") ;
		DPIAddExportedFunction(1, "wishbone_read") ;
		DPIAllocateDPIScopes(2) ;
		DPISetDPIScopeFunctionName(0, "wishbone_write") ;
		DPISetDPIScopeHierarchy(0, "sim1") ;
		DPIRelocateDPIScopeIP(0, (char*)(0xe988)) ;
		DPIAddDPIScopeAccessibleFunction(0, 0) ;
		DPIAddDPIScopeAccessibleFunction(0, 1) ;
	}

}


extern "C" {
	void iki_initialize_dpi()
	{ XILINX_DPI::dpiInitialize() ; } 
}


extern "C" {

	extern void subprog_m_3a485ca_30637d5a_13(char*, char*, char*);
	extern void subprog_m_3a485ca_30637d5a_12(char*, char*, char*);
}


extern "C" {
}


extern "C" {
	DPI_DLLESPEC 
	int wishbone_write(int arg0, int arg1, char arg2, char* arg3)
	{
		int result ;
		DPIVerifyScope();
		int functionToCall = staticScopeCheck("wishbone_write") ;
		switch(functionToCall)
		{
			case 0:
			{

	{
		DPIFlushAll();
		int staticIndex = 0 ;
		char* IP = NULL ;
		staticIndex = svGetScopeStaticId() ;
		IP = svGetScopeIP();
		int callingProcessOffset = DPIGetTaskCaller() ;
		char* SP ;
		void* oldSPcontext = DPIGetCurrentContext();
		SP = DPIInitializeTask(58760, IP + 2784, 184, 0) ;
		char driver0[32] ;
		for(int i = 0 ; i < 32 ; ++i) driver0[i] = 0 ;
		char driver1[32] ;
		for(int i = 0 ; i < 32 ; ++i) driver1[i] = 0 ;
		char driver2[32] ;
		for(int i = 0 ; i < 32 ; ++i) driver2[i] = 0 ;
		char copyArg_0_0[8];
		{
		char* ptrToSP = (char*)copyArg_0_0;
		DPIMemsetDpiToSv( ptrToSP, (char*)(&arg0), 4, 1 );
		ptrToSP = ptrToSP + 8; 
		}
		DPIScheduleTransactionBlocking(IP +1608, driver0, (char*)(&copyArg_0_0), 0, 31) ;
		char copyArg_1_1[8];
		{
		char* ptrToSP = (char*)copyArg_1_1;
		DPIMemsetDpiToSv( ptrToSP, (char*)(&arg1), 4, 1 );
		ptrToSP = ptrToSP + 8; 
		}
		DPIScheduleTransactionBlocking(IP +1664, driver1, (char*)(&copyArg_1_1), 0, 31) ;
		char copyArg_2_2[8];
		{
		char* ptrToSP = (char*)copyArg_2_2;
		DPIMemsetDpiToSv( ptrToSP, (char*)(&arg2), 1, 1 );
		ptrToSP = ptrToSP + 8; 
		}
		DPIScheduleTransactionBlocking(IP +1720, driver2, (char*)(&copyArg_2_2), 0, 7) ;
		char* oldSP = *((char**)(IP + callingProcessOffset + 80)) ; 
		DPIInvokeTask(58760, SP, (void*)subprog_m_3a485ca_30637d5a_12, IP) ;
		DPIYieldCurrentContext() ;
		{
		char* ptrToSP = (char*)DPISignalHandle(IP +1776, 8);
		DPIMemsetSvToDpi( (char*)(arg3), ptrToSP, 1, 1 );
		ptrToSP = ptrToSP + 8; 
		}
		DPIDeleteTaskInvocation(SP) ;
		*((char**)(IP + callingProcessOffset + 80)) = oldSP ; 
		DPISetCurrentContext(oldSPcontext);
		DPIFlushAll();
if (*(unsigned int*)(SP + 147) == 1) 
{
result = 1 ;
}
else
{
result = 0 ;
}
	}
			}
			break ;
			default:
			break ;
		}
		return result ;
	}
	DPI_DLLESPEC 
	int wishbone_read(int arg0, int arg1, int* arg2, char* arg3)
	{
		int result ;
		DPIVerifyScope();
		int functionToCall = staticScopeCheck("wishbone_read") ;
		switch(functionToCall)
		{
			case 1:
			{

	{
		DPIFlushAll();
		int staticIndex = 0 ;
		char* IP = NULL ;
		staticIndex = svGetScopeStaticId() ;
		IP = svGetScopeIP();
		int callingProcessOffset = DPIGetTaskCaller() ;
		char* SP ;
		void* oldSPcontext = DPIGetCurrentContext();
		SP = DPIInitializeTask(58576, IP + 4520, 184, 0) ;
		char driver0[32] ;
		for(int i = 0 ; i < 32 ; ++i) driver0[i] = 0 ;
		char driver1[32] ;
		for(int i = 0 ; i < 32 ; ++i) driver1[i] = 0 ;
		char copyArg_4_0[8];
		{
		char* ptrToSP = (char*)copyArg_4_0;
		DPIMemsetDpiToSv( ptrToSP, (char*)(&arg0), 4, 1 );
		ptrToSP = ptrToSP + 8; 
		}
		DPIScheduleTransactionBlocking(IP +3232, driver0, (char*)(&copyArg_4_0), 0, 31) ;
		char copyArg_5_1[8];
		{
		char* ptrToSP = (char*)copyArg_5_1;
		DPIMemsetDpiToSv( ptrToSP, (char*)(&arg1), 4, 1 );
		ptrToSP = ptrToSP + 8; 
		}
		DPIScheduleTransactionBlocking(IP +3288, driver1, (char*)(&copyArg_5_1), 0, 31) ;
		char* oldSP = *((char**)(IP + callingProcessOffset + 80)) ; 
		DPIInvokeTask(58576, SP, (void*)subprog_m_3a485ca_30637d5a_13, IP) ;
		DPIYieldCurrentContext() ;
		{
		char* ptrToSP = (char*)DPISignalHandle(IP +3344, 32);
		DPIMemsetSvToDpi( (char*)(arg2), ptrToSP, 4, 1 );
		ptrToSP = ptrToSP + 8; 
		}
		{
		char* ptrToSP = (char*)DPISignalHandle(IP +3400, 8);
		DPIMemsetSvToDpi( (char*)(arg3), ptrToSP, 1, 1 );
		ptrToSP = ptrToSP + 8; 
		}
		DPIDeleteTaskInvocation(SP) ;
		*((char**)(IP + callingProcessOffset + 80)) = oldSP ; 
		DPISetCurrentContext(oldSPcontext);
		DPIFlushAll();
if (*(unsigned int*)(SP + 147) == 1) 
{
result = 1 ;
}
else
{
result = 0 ;
}
	}
			}
			break ;
			default:
			break ;
		}
		return result ;
	}
}

