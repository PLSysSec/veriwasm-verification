
// Derived portions fall under:
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Derived from Intel Open Source Licensed work .
/*
Intel Open Source License 

Copyright (c) 2002-2018 Intel Corporation. All rights reserved.
 
Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

Redistributions of source code must retain the above copyright notice,
this list of conditions and the following disclaimer.  Redistributions
in binary form must reproduce the above copyright notice, this list of
conditions and the following disclaimer in the documentation and/or
other materials provided with the distribution.  Neither the name of
the Intel Corporation nor the names of its contributors may be used to
endorse or promote products derived from this software without
specific prior written permission.
 
THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE INTEL OR
ITS CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
END_LEGAL */


#include <fstream>
#include <iomanip>
#include <iostream>
#include <string.h>
#include "pin.H"

struct cpustate
{
	unsigned long long rax;
	unsigned long long rcx;
	unsigned long long rdx;
	unsigned long long rbx;
	unsigned long long rsp;
	unsigned long long rbp;
	unsigned long long rsi;
	unsigned long long rdi;
	unsigned long long r8;
	unsigned long long r9;
	unsigned long long r10;
	unsigned long long r11;
	unsigned long long r12;
	unsigned long long r13;
	unsigned long long r14;
	unsigned long long r15;

	unsigned long long ymm0[4];
	unsigned long long ymm1[4];
	unsigned long long ymm2[4];
	unsigned long long ymm3[4];
	unsigned long long ymm4[4];
	unsigned long long ymm5[4];
	unsigned long long ymm6[4];
	unsigned long long ymm7[4];
	unsigned long long ymm8[4];
	unsigned long long ymm9[4];
	unsigned long long ymm10[4];
	unsigned long long ymm11[4];
	unsigned long long ymm12[4];
	unsigned long long ymm13[4];
	unsigned long long ymm14[4];
	unsigned long long ymm15[4];

	bool cf;
	bool pf;
	bool af;
	bool zf;
	bool sf;
	bool of;
};

ifstream inFile;
ofstream outFile;
int testcase;
int op1, op2; //0=ax, 1=bx, 2=cx,3=dx
cpustate c; // initial state
VOID *operandmem;
bool is_memory=false;

KNOB<size_t> KnobTc(KNOB_MODE_WRITEONCE, "pintool", "c", "0",
    "testcase to use");
KNOB<size_t> KnobOP1(KNOB_MODE_WRITEONCE, "pintool", "o", "1",
    "operand 1");
KNOB<size_t> KnobOP2(KNOB_MODE_WRITEONCE, "pintool", "p", "2",
    "operand 2");


bool read_flag()
{
	char buffer[100];
	unsigned int a;

	inFile.read(buffer,9);
	inFile >> a; 
	if(a==0) return false;
	return true;
}

ADDRINT set_flag(bool f, ADDRINT val, ADDRINT mask)
{
	if(f) 
	{
		val = val | mask;
		
	} else
	{
		val = val & (~mask);
	}
	return val;
}

unsigned long long read_reg()
{
	char buffer[100];
	unsigned int a,b,c,d,e,f,g,h;
	unsigned long long qword=0;

	inFile.read(buffer,9);
	inFile >> hex;
	inFile >> a >> b >> c >> d >> e >> f >> g >> h;
	qword=h;
	qword+= (unsigned long long) g << 8;
	qword+= (unsigned long long) f << 16;
	qword+= (unsigned long long) e << 24;
	qword+= (unsigned long long) d << 32;
	qword+= (unsigned long long) c << 40;
	qword+= (unsigned long long) b << 48;
	qword+= (unsigned long long) a << 56;
	return qword;
}
void read_ymm(unsigned long long *ymmreg)
{
	char buffer[100];
	unsigned int a,b,c,d,e,f,g,h;
	unsigned long long qword=0;

	inFile.read(buffer,9);
	inFile >> hex;
	inFile >> a >> b >> c >> d >> e >> f >> g >> h;
	qword=h;
	qword+= (unsigned long long) g << 8;
	qword+= (unsigned long long) f << 16;
	qword+= (unsigned long long) e << 24;
	qword+= (unsigned long long) d << 32;
	qword+= (unsigned long long) c << 40;
	qword+= (unsigned long long) b << 48;
	qword+= (unsigned long long) a << 56;
	ymmreg[3] = qword;
	inFile >> hex;
	inFile >> a >> b >> c >> d >> e >> f >> g >> h;
	qword=h;
	qword+= (unsigned long long) g << 8;
	qword+= (unsigned long long) f << 16;
	qword+= (unsigned long long) e << 24;
	qword+= (unsigned long long) d << 32;
	qword+= (unsigned long long) c << 40;
	qword+= (unsigned long long) b << 48;
	qword+= (unsigned long long) a << 56;
	ymmreg[2] = qword;
	inFile >> hex;
	inFile >> a >> b >> c >> d >> e >> f >> g >> h;
	qword=h;
	qword+= (unsigned long long) g << 8;
	qword+= (unsigned long long) f << 16;
	qword+= (unsigned long long) e << 24;
	qword+= (unsigned long long) d << 32;
	qword+= (unsigned long long) c << 40;
	qword+= (unsigned long long) b << 48;
	qword+= (unsigned long long) a << 56;
	ymmreg[1] = qword;
	inFile >> hex;
	inFile >> a >> b >> c >> d >> e >> f >> g >> h;
	qword=h;
	qword+= (unsigned long long) g << 8;
	qword+= (unsigned long long) f << 16;
	qword+= (unsigned long long) e << 24;
	qword+= (unsigned long long) d << 32;
	qword+= (unsigned long long) c << 40;
	qword+= (unsigned long long) b << 48;
	qword+= (unsigned long long) a << 56;
	ymmreg[0] = qword;
}

//to_flag_var 

cpustate get_testcase(int casenumber)
{
	int lines_skip = (casenumber*78)+4;
	char buffer[300];
	for(int i=0;i<lines_skip;i++) inFile.getline(buffer,300);
	c.rax = read_reg();
	c.rcx = read_reg();
	c.rdx = read_reg();
	c.rbx = read_reg();
	c.rsp = read_reg();
	c.rbp = read_reg();
	c.rsi = read_reg();
	c.rdi = read_reg();
	c.r8  = read_reg();
	c.r9  = read_reg();
	c.r10 = read_reg();
	c.r11 = read_reg();
	c.r12 = read_reg();
	c.r13 = read_reg();
	c.r14 = read_reg();
	c.r15 = read_reg();
	inFile.getline(buffer,300); //skip line
	read_ymm(&c.ymm0[0]);
	read_ymm(&c.ymm1[0]);
	read_ymm(&c.ymm2[0]);
	read_ymm(&c.ymm3[0]);
	read_ymm(&c.ymm4[0]);
	read_ymm(&c.ymm5[0]);
	read_ymm(&c.ymm6[0]);
	read_ymm(&c.ymm7[0]);
	read_ymm(&c.ymm8[0]);
	read_ymm(&c.ymm9[0]);
	read_ymm(&c.ymm10[0]);
	read_ymm(&c.ymm11[0]);
	read_ymm(&c.ymm12[0]);
	read_ymm(&c.ymm13[0]);
	read_ymm(&c.ymm14[0]);
	read_ymm(&c.ymm15[0]);
	inFile.getline(buffer,300); //skip line
	c.cf = read_flag();
	read_flag();
	c.pf = read_flag();
	read_flag();
	c.af= read_flag();
	read_flag();
	c.zf = read_flag();
	c.sf = read_flag();
	read_flag();
	read_flag();
	read_flag();
	c.of = read_flag();	
	return c;
	
}

VOID startregs(
	PIN_REGISTER* rax, PIN_REGISTER* rbx, 
	PIN_REGISTER* rcx, PIN_REGISTER* rdx,  
	PIN_REGISTER* r8, PIN_REGISTER* r9, 
	PIN_REGISTER* r10, PIN_REGISTER* r11,  
	PIN_REGISTER* r12, PIN_REGISTER* r13,  
	PIN_REGISTER* r14, PIN_REGISTER* r15,  
	PIN_REGISTER* sse0, PIN_REGISTER* sse1, 
	PIN_REGISTER* sse2, PIN_REGISTER* sse3,
    PIN_REGISTER* sse4, PIN_REGISTER* sse5, 
	PIN_REGISTER* sse6, PIN_REGISTER* sse7,
    PIN_REGISTER* sse8, PIN_REGISTER* sse9, 
	PIN_REGISTER* sse10, PIN_REGISTER* sse11,
    PIN_REGISTER* sse12, PIN_REGISTER* sse13, 
	PIN_REGISTER* sse14, PIN_REGISTER* sse15, PIN_REGISTER* flags)
{
	int i;
	
	cpustate c=get_testcase(testcase);
	rax->qword[0]=c.rax;
	rbx->qword[0]=c.rbx;
	rcx->qword[0]=c.rcx;
	rdx->qword[0]=c.rdx;
//	rsp->qword[0]=c.rsp;
//	rbp->qword[0]=c.rbp;
//	rsi->qword[0]=c.rsi;
//	rdi->qword[0]=c.rdi;
	r8->qword[0]=c.r8;
	r9->qword[0]=c.r9;
	r10->qword[0]=c.r10;
	r11->qword[0]=c.r11;
	r12->qword[0]=c.r11;
	r13->qword[0]=c.r13;
	r14->qword[0]=c.r14;
	r15->qword[0]=c.r15;
	
	for (i=0;i<4;i++) {
		sse0->qword[i]=c.ymm0[i];
		sse1->qword[i]=c.ymm1[i];
		sse2->qword[i]=c.ymm2[i];
		sse3->qword[i]=c.ymm3[i];
		sse4->qword[i]=c.ymm4[i];
		sse5->qword[i]=c.ymm5[i];
		sse6->qword[i]=c.ymm6[i];
		sse7->qword[i]=c.ymm7[i];
		sse8->qword[i]=c.ymm8[i];
		sse9->qword[i]=c.ymm9[i];
		sse10->qword[i]=c.ymm10[i];
		sse11->qword[i]=c.ymm11[i];
		sse12->qword[i]=c.ymm12[i];
		sse13->qword[i]=c.ymm13[i];
		sse14->qword[i]=c.ymm14[i];
		sse15->qword[i]=c.ymm15[i];
	}
	flags->qword[0]=set_flag(c.cf,flags->qword[0],0x001);
	flags->qword[0]=set_flag(c.pf,flags->qword[0],0x004);
	flags->qword[0]=set_flag(c.af,flags->qword[0],0x010);
	flags->qword[0]=set_flag(c.zf,flags->qword[0],0x040);
	flags->qword[0]=set_flag(c.sf,flags->qword[0],0x080);
	flags->qword[0]=set_flag(c.of,flags->qword[0],0x800);
}

VOID printregs(ADDRINT rax, ADDRINT rbx, ADDRINT rcx, ADDRINT rdx, 
			   ADDRINT r8, ADDRINT r9, ADDRINT r10, ADDRINT r11, 
			   ADDRINT r12, ADDRINT r13, ADDRINT r14, ADDRINT r15, 	
			   PIN_REGISTER* sse0, PIN_REGISTER* sse1, 
				PIN_REGISTER* sse2, PIN_REGISTER* sse3,
				PIN_REGISTER* sse4, PIN_REGISTER* sse5, 
				PIN_REGISTER* sse6, PIN_REGISTER* sse7,
				PIN_REGISTER* sse8, PIN_REGISTER* sse9, 
				PIN_REGISTER* sse10, PIN_REGISTER* sse11,
				PIN_REGISTER* sse12, PIN_REGISTER* sse13, 
				PIN_REGISTER* sse14, PIN_REGISTER* sse15, ADDRINT rflags 
			   )
{
	//Operands
	if (op1==0)	{
		outFile << "0x" << hex << c.rax << endl;
		outFile << "0x" << hex << rax << endl; 
	}
	if (op1==1)	{
		outFile << "0x" << hex << c.rbx << endl;
		outFile << "0x" << hex << rbx << endl; 
	}
	if (op1==2)	{
		outFile << "0x" << hex << c.rcx << endl;
		outFile << "0x" << hex << rcx << endl; 
	}
	if (op1==3)	{
		outFile << "0x" << hex << c.rdx << endl;
		outFile << "0x" << hex << rdx << endl; 
	}
	//do src data
	if (op2==0)	{
		outFile << "0x" << hex << c.rax << endl;
		outFile << "0x" << hex << rax << endl; 
	}
	if (op2==1)	{
		outFile << "0x" << hex << c.rbx << endl;
		outFile << "0x" << hex << rbx << endl; 
	}
	if (op2==2)	{
		outFile << "0x" << hex << c.rcx << endl;
		outFile << "0x" << hex << rcx << endl; 
	}
	if (op2==3)	{
		outFile << "0x" << hex << c.rdx << endl;
		outFile << "0x" << hex << rdx << endl; 
	}

	//Flags
	if(c.cf) outFile << "(flag_cf, True),";
	else outFile << "(flag_cf, False),";
	if(c.pf) outFile << "(flag_pf, True),";
	else outFile << "(flag_pf, False),";
//	if(c.af) outFile << "(flag_af, True),";
//	else outFile << "(flag_af, False),";
	if(c.zf) outFile << "(flag_zf, True),";
	else outFile << "(flag_zf, False),";
	if(c.sf) outFile << "(flag_sf, True),";
	else outFile << "(flag_sf, False),";
	if(c.of) outFile << "(flag_of, True)";
	else outFile << "(flag_of, False)";
	outFile << endl;
	
	if((rflags & 0x001)>0) outFile << "(flag_cf, True),";
	else outFile << "(flag_cf, False),";
	if((rflags & 0x004)>0) outFile << "(flag_pf, True),";
	else outFile << "(flag_pf, False),";
//	if((rflags & 0x010)>0) outFile << "(flag_af, True),";
//	else outFile << "(flag_af, False),";
	if((rflags & 0x040)>0) outFile << "(flag_zf, True),";
	else outFile << "(flag_zf, False),";
	if((rflags & 0x080)>0) outFile << "(flag_sf, True),";
	else outFile << "(flag_sf, False),";
	if((rflags & 0x800)>0) outFile << "(flag_of, True)";
	else outFile << "(flag_of, False)";
	outFile << endl;
	
	//For Direct Writes
	
	outFile << "(rax,0x" << hex << c.rax << ")" << endl;
	outFile << "(rax,0x" << hex << rax << ")" << endl; 
	outFile << "(rdx,0x" << hex << c.rdx << ")" << endl;
	outFile << "(rdx,0x" << hex << rdx << ")" << endl; 
	
	//ymms
	outFile << "0x" << hex << c.ymm0[3] 		<< ", 0x" << c.ymm0[2] 		<< ", 0x" << c.ymm0[1] 		<< ", 0x" << c.ymm0[0] << endl;
	outFile << "0x" << hex << sse0->qword[3] 	<< ", 0x" << sse0->qword[2] << ", 0x" << sse0->qword[1] << ", 0x" << sse0->qword[0] << endl; 

	outFile << "0x" << hex << c.ymm1[3] 		<< ", 0x" << c.ymm1[2] 		<< ", 0x" << c.ymm1[1] 		<< ", 0x" << c.ymm1[0] << endl;
	outFile << "0x" << hex << sse1->qword[3] 	<< ", 0x" << sse1->qword[2] << ", 0x" << sse1->qword[1] << ", 0x" << sse1->qword[0] << endl; 

	outFile << "0x" << hex << c.ymm2[3] 		<< ", 0x" << c.ymm2[2] 		<< ", 0x" << c.ymm2[1] 		<< ", 0x" << c.ymm2[0] << endl;
	outFile << "0x" << hex << sse2->qword[3] 	<< ", 0x" << sse2->qword[2] << ", 0x" << sse2->qword[1] << ", 0x" << sse2->qword[0] << endl; 

	outFile << "0x" << hex << c.ymm3[3] 		<< ", 0x" << c.ymm3[2] 		<< ", 0x" << c.ymm3[1] 		<< ", 0x" << c.ymm3[0] << endl;
	outFile << "0x" << hex << sse3->qword[3] 	<< ", 0x" << sse3->qword[2] << ", 0x" << sse3->qword[1] << ", 0x" << sse3->qword[0] << endl; 

	outFile << "0x" << hex << c.ymm4[3] 		<< ", 0x" << c.ymm4[2] 		<< ", 0x" << c.ymm4[1] 		<< ", 0x" << c.ymm4[0] << endl;
	outFile << "0x" << hex << sse4->qword[3] 	<< ", 0x" << sse4->qword[2] << ", 0x" << sse4->qword[1] << ", 0x" << sse4->qword[0] << endl; 

	if(is_memory) 
	{
	//memory operand
		outFile << is_memory << " 0x" << hex << *((ADDRINT* ) operandmem+3) << " 0x" << hex << *((ADDRINT* ) operandmem+2) 
							 << " 0x" << hex << *((ADDRINT* ) operandmem+1) << " 0x" << hex << *((ADDRINT* ) operandmem+0)
				<< endl;
	} else
	{
		outFile << is_memory << " 0x0000000000000000" << endl;
		
	}
	
/*
	outFile << "0x" << hex << c.ymm3[3] << c.ymm3[2] << c.ymm3[1] << c.ymm3[0] << endl;
	outFile << "0x" << hex << sse3->qword[3] << sse3->qword[2] << sse3->qword[1] << sse3->qword[0] << endl; 
	outFile << "0x" << hex << c.ymm4[3] << c.ymm4[2] << c.ymm4[1] << c.ymm4[0] << endl;
	outFile << "0x" << hex << sse4->qword[3] << sse4->qword[2] << sse4->qword[1] << sse4->qword[0] << endl; 
	outFile << "0x" << hex << c.ymm5[3] << c.ymm5[2] << c.ymm5[1] << c.ymm5[0] << endl;
	outFile << "0x" << hex << sse5->qword[3] << sse5->qword[2] << sse5->qword[1] << sse5->qword[0] << endl; 
	outFile << "0x" << hex << c.ymm6[3] << c.ymm6[2] << c.ymm6[1] << c.ymm6[0] << endl;
	outFile << "0x" << hex << sse6->qword[3] << sse6->qword[2] << sse6->qword[1] << sse6->qword[0] << endl; 
	outFile << "0x" << hex << c.ymm7[3] << c.ymm7[2] << c.ymm7[1] << c.ymm7[0] << endl;
	outFile << "0x" << hex << sse7->qword[3] << sse7->qword[2] << sse7->qword[1] << sse7->qword[0] << endl; 
	outFile << "0x" << hex << c.ymm8[3] << c.ymm8[2] << c.ymm8[1] << c.ymm8[0] << endl;
	outFile << "0x" << hex << sse8->qword[3] << sse8->qword[2] << sse8->qword[1] << sse8->qword[0] << endl; 
	outFile << "0x" << hex << c.ymm9[3] << c.ymm9[2] << c.ymm9[1] << c.ymm9[0] << endl;
	outFile << "0x" << hex << sse9->qword[3] << sse9->qword[2] << sse9->qword[1] << sse9->qword[0] << endl; 
	outFile << "0x" << hex << c.ymm10[3] << c.ymm10[2] << c.ymm10[1] << c.ymm10[0] << endl;
	outFile << "0x" << hex << sse10->qword[3] << sse10->qword[2] << sse10->qword[1] << sse10->qword[0] << endl; 
	outFile << "0x" << hex << c.ymm11[3] << c.ymm11[2] << c.ymm11[1] << c.ymm11[0] << endl;
	outFile << "0x" << hex << sse11->qword[3] << sse11->qword[2] << sse11->qword[1] << sse11->qword[0] << endl; 
	outFile << "0x" << hex << c.ymm12[3] << c.ymm12[2] << c.ymm12[1] << c.ymm12[0] << endl;
	outFile << "0x" << hex << sse12->qword[3] << sse12->qword[2] << sse12->qword[1] << sse12->qword[0] << endl; 
	outFile << "0x" << hex << c.ymm13[3] << c.ymm13[2] << c.ymm13[1] << c.ymm13[0] << endl;
	outFile << "0x" << hex << sse13->qword[3] << sse13->qword[2] << sse13->qword[1] << sse13->qword[0] << endl; 
	outFile << "0x" << hex << c.ymm14[3] << c.ymm14[2] << c.ymm14[1] << c.ymm14[0] << endl;
	outFile << "0x" << hex << sse14->qword[3] << sse14->qword[2] << sse14->qword[1] << sse14->qword[0] << endl; 
*/	
}
VOID record_address(VOID* addr) {
	operandmem=addr;
	is_memory=true;
//	cout << "Here!!" << endl;
}

VOID start(INS& ins)
{
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)startregs, 
	IARG_REG_REFERENCE, REG_RAX, IARG_REG_REFERENCE, REG_RBX, 
	IARG_REG_REFERENCE, REG_RCX, IARG_REG_REFERENCE, REG_RDX,
	IARG_REG_REFERENCE, REG_R8, IARG_REG_REFERENCE, REG_R9,
	IARG_REG_REFERENCE, REG_R10, IARG_REG_REFERENCE, REG_R11,
	IARG_REG_REFERENCE, REG_R12, IARG_REG_REFERENCE, REG_R13,
	IARG_REG_REFERENCE, REG_R14, IARG_REG_REFERENCE, REG_R15,	
	IARG_REG_REFERENCE, REG_YMM0,  IARG_REG_REFERENCE, REG_YMM1,
	IARG_REG_REFERENCE, REG_YMM2,  IARG_REG_REFERENCE, REG_YMM3,
	IARG_REG_REFERENCE, REG_YMM4,  IARG_REG_REFERENCE, REG_YMM5,
	IARG_REG_REFERENCE, REG_YMM6,  IARG_REG_REFERENCE, REG_YMM7,
	IARG_REG_REFERENCE, REG_YMM8,  IARG_REG_REFERENCE, REG_YMM9,
	IARG_REG_REFERENCE, REG_YMM10, IARG_REG_REFERENCE, REG_YMM11,
	IARG_REG_REFERENCE, REG_YMM12, IARG_REG_REFERENCE, REG_YMM13,
	IARG_REG_REFERENCE, REG_YMM14, IARG_REG_REFERENCE, REG_YMM15,
	IARG_REG_REFERENCE, REG_RFLAGS, 
	IARG_END);
}

VOID output(INS& ins)
{
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)printregs, 
	IARG_REG_VALUE, REG_RAX, IARG_REG_VALUE, REG_RBX, 
	IARG_REG_VALUE, REG_RCX, IARG_REG_VALUE, REG_RDX,
	IARG_REG_VALUE, REG_R8, IARG_REG_VALUE, REG_R9, 
	IARG_REG_VALUE, REG_R10, IARG_REG_VALUE, REG_R11,
	IARG_REG_VALUE, REG_R12, IARG_REG_VALUE, REG_R13,
	IARG_REG_VALUE, REG_R14, IARG_REG_VALUE, REG_R15,
	IARG_REG_REFERENCE, REG_YMM0,  IARG_REG_REFERENCE, REG_YMM1,
	IARG_REG_REFERENCE, REG_YMM2,  IARG_REG_REFERENCE, REG_YMM3,
	IARG_REG_REFERENCE, REG_YMM4,  IARG_REG_REFERENCE, REG_YMM5,
	IARG_REG_REFERENCE, REG_YMM6,  IARG_REG_REFERENCE, REG_YMM7,
	IARG_REG_REFERENCE, REG_YMM8,  IARG_REG_REFERENCE, REG_YMM9,
	IARG_REG_REFERENCE, REG_YMM10, IARG_REG_REFERENCE, REG_YMM11,
	IARG_REG_REFERENCE, REG_YMM12, IARG_REG_REFERENCE, REG_YMM13,
	IARG_REG_REFERENCE, REG_YMM14, IARG_REG_REFERENCE, REG_YMM15,
	IARG_REG_VALUE, REG_RFLAGS, 
	IARG_END);
}

// Pin calls this function every time a new rtn is executed
VOID Routine(RTN rtn, VOID *v)
{
    
	int instr_counter=0;
	
	bool is_target = RTN_Name(rtn) == "main";
            
    RTN_Open(rtn);
                
    // For each instruction of the routine
    for (INS ins = RTN_InsHead(rtn); INS_Valid(ins); ins = INS_Next(ins))
    {
		if (is_target && instr_counter==0) {
			start(ins);
		}	
		if (is_target && instr_counter==1) {
			output(ins);
		}	
		
		if (is_target) {
				// Record memory references
			for (size_t i = 0, ie = INS_MemoryOperandCount(ins); i < ie; ++i) {
				if (INS_MemoryOperandIsRead(ins, i)) {
					INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR) record_address,
							IARG_MEMORYOP_EA, i, 
							IARG_END);
				}
				if (INS_MemoryOperandIsWritten(ins, i)) {
					INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR) record_address,
							IARG_MEMORYOP_EA, i,
							IARG_END);
				}
			}
		}
		
		
		instr_counter++;
    }    
    RTN_Close(rtn);
}

// This function is called when the application exits
// It prints the name and count for each procedure
VOID Fini(INT32 code, VOID *v)
{
   outFile.close();
   inFile.close();
}

/* ===================================================================== */
/* Print Help Message                                                    */
/* ===================================================================== */

INT32 Usage()
{
    cerr << "This Pintool counts the number of times a routine is executed" << endl;
    cerr << "and the number of instructions executed in a routine" << endl;
    cerr << endl << KNOB_BASE::StringKnobSummary() << endl;
    return -1;
}

/* ===================================================================== */
/* Main                                                                  */
/* ===================================================================== */

int main(int argc, char * argv[])
{
    // Initialize symbol table code, needed for rtn instrumentation
    PIN_InitSymbols();

    inFile.open("chum_test.in");
    outFile.open("chum_test.out");

    // Initialize pin
    if (PIN_Init(argc, argv)) return Usage();

	testcase = KnobTc.Value();
	op1 = KnobOP1.Value();
	op2 = KnobOP2.Value();
	
    // Register Routine to be called to instrument rtn
    RTN_AddInstrumentFunction(Routine, 0);

    // Register Fini to be called when the application exits
    PIN_AddFiniFunction(Fini, 0);
    
    // Start the program, never returns
    PIN_StartProgram();
    
    return 0;
}
