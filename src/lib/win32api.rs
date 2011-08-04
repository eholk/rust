/*
  A redefinition of the parts of the Windows API we use in our runtime
  and standard libary.

  Also includes some higher level wrapper things.
*/

import ptr::null;
import sys::size_of;

import kernel32::*;

export BYTE;
export WORD;
export DWORD;
export LPVOID;
export HANDLE;
export LPCTSTR;
export LPTSTR;

export PROCESS_INFORMATION;
export SECURITY_ATTRIBUTES;
export STARTUPINFO;

export CreateProcessA;
export WaitForSingleObject;
export GetExitCodeProcess;

export STILL_ACTIVE;
export WAIT_OBJECT_0;
export WAIT_TIMEOUT;

export handle;

native "x86stdcall" mod kernel32 {
    fn CloseHandle(hObject : HANDLE) -> BOOL;
    fn WaitForSingleObject(hHandle : HANDLE, dwMilliseconds : DWORD) -> DWORD;
    fn CreateProcessA(lpApplicationName : LPCTSTR,
                      lpCommandLine : LPTSTR,
                      lpProcessAttributes : &SECURITY_ATTRIBUTES,
                      lpThreadAttributes : &SECURITY_ATTRIBUTES,
                      bInheritHandles : BOOL,
                      dwCreationFlags : DWORD,
                      lpEnvironment : LPVOID,
                      lpCurrentDirectory : LPCTSTR,
                      lpStartupInfo : &STARTUPINFO,
                      lpProcessInformation : &PROCESS_INFORMATION) -> BOOL;
    fn GetExitCodeProcess(hHandle : HANDLE, 
                          dwStatus : &DWORD) -> BOOL;
}

type BYTE = u8;
type BOOL = i32;
type WORD = u16;
type DWORD = u32;
type LPVOID = *u8;
type HANDLE = LPVOID;
type LPCTSTR = *u8;
type LPTSTR = *u8;

type PROCESS_INFORMATION = {
    hProcess    : HANDLE,
    hThread     : HANDLE,
    dwProcessId : DWORD,
    dwThreadId  : DWORD
};

fn init_ProcessInformation() -> PROCESS_INFORMATION {
    {   
        hProcess    : null(),
        hThread     : null(),
        dwProcessId : 0u32,
        dwThreadId  : 0u32
    }
}

type SECURITY_ATTRIBUTES = {
    nLength : DWORD,
    lpSecurityDescriptor : LPVOID,
    bInheritHandle : BOOL
};

fn init_SecurityAttributes() -> SECURITY_ATTRIBUTES {
    {
        nLength: size_of[SECURITY_ATTRIBUTES]() as u32,
        lpSecurityDescriptor: null(),
        bInheritHandle: 0i32 
    }
}

type STARTUPINFO = {
    cb : DWORD,
    lpReserved : LPTSTR,
    lpDesktop : LPTSTR,
    lpTitle : LPTSTR,
    dwX : DWORD,
    dwY : DWORD,
    dwXSize : DWORD,
    dwYSize : DWORD,
    dwXCountChars : DWORD,
    dwYCountChars : DWORD,
    dwFillAttribute : DWORD,
    dwFlags : DWORD,
    wShowWindow : WORD,
    cbReserved2 : WORD,
    lpReserved2 : *BYTE,
    hStdInput : HANDLE,
    hStdOutput : HANDLE,
    hStdError : HANDLE
};

fn init_StartupInfo() -> STARTUPINFO {
    {
        cb : size_of[STARTUPINFO]() as u32,
        lpReserved : null(),
        lpDesktop : null(),
        lpTitle : null(),
        dwX : 0u32,
        dwY : 0u32,
        dwXSize : 0u32,
        dwYSize : 0u32,
        dwXCountChars : 0u32,
        dwYCountChars : 0u32,
        dwFillAttribute : 0u32,
        dwFlags : 0u32,
        wShowWindow : 0u16,
        cbReserved2 : 0u16,
        lpReserved2 : null(),
        hStdInput : null(),
        hStdOutput : null(),
        hStdError :null()
    }
}

resource handle(h : HANDLE) {
    kernel32::CloseHandle(h);
}

const WAIT_OBJECT_0  : DWORD = 0x00000000u32;
const WAIT_ABANDONED : DWORD = 0x00000080u32;
const WAIT_TIMEOUT   : DWORD = 0x00000102u32;
const WAIT_FAILED    : DWORD = 0xffffffffu32;

const STILL_ACTIVE   : DWORD = 0x00000103u32;