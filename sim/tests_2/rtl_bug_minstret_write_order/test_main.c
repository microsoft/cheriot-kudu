// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <util.h>
extern void cheri_atest(unsigned *results);
static unsigned results[3];
static void print_hex32(unsigned value){static const char h[]="0123456789abcdef";prints("0x");for(int i=7;i>=0;--i)send_char(h[(value>>(i*4))&0xf]);}
static void print_hex16(unsigned value){static const char h[]="0123456789abcdef";prints("0x");for(int i=3;i>=0;--i)send_char(h[(value>>(i*4))&0xf]);}
static void print_dec(unsigned value){char b[10];int p=0;if(!value){send_char('0');return;}while(value){b[p++]=(char)('0'+value%10);value/=10;}while(p)send_char(b[--p]);}
int mymain(int argc,int argv){(void)argc;(void)argv;cheri_atest(results);unsigned pass=(results[0]==0 && results[1]==5 && results[2]==7);prints("MINSTRET INCREMENT csr=");print_hex16(0x0b02);prints(" observed first=");print_hex32(results[0]);prints(" second=");print_hex32(results[1]);prints(" third=");print_hex32(results[2]);prints("\nMINSTRET INCREMENT ");prints(pass?"PASS":"FAIL");prints(" failures=");print_dec(pass?0:1);prints(" cases=");print_dec(1);prints("\n");stop_sim();return pass?0:1;}
