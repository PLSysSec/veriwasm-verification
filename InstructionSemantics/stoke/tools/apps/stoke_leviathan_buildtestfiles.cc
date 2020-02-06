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

#include <iostream>

#include "src/ext/cpputil/include/command_line/command_line.h"
#include "src/ext/cpputil/include/signal/debug_handler.h"
#include "src/ext/cpputil/include/io/filterstream.h"
#include "src/ext/cpputil/include/io/column.h"
#include "src/ext/cpputil/include/io/console.h"

#include "src/symstate/simplify.h"
#include "src/symstate/print_visitor.h"
#include "src/validator/handlers/strata_handler.h"
#include "src/specgen/specgen.h"
#include "src/specgen/support.h"

#include "src/leviathan/leviathan_table.h"
#include "src/leviathan/leviathan_x86_family_table.h"
#include "src/symstate/leviathan_visitor.h"

#include "tools/gadgets/functions.h"
#include "tools/gadgets/solver.h"
#include "tools/gadgets/target.h"
#include "tools/gadgets/validator.h"

#include <boost/iostreams/stream.hpp>
#include <boost/iostreams/device/file.hpp>
#include <boost/format.hpp>
#include <boost/filesystem.hpp>
#include <cstdlib>

using namespace cpputil;
using namespace std;
using namespace stoke;
using namespace x64asm; 
using namespace boost::iostreams;
using namespace boost;

typedef std::map<std::string, bool>  FlagTable;

FlagTable flag_table = {
    #include "src/leviathan/flag.table"
};

int lemma_count;
int lemma_start;
std::stringstream set_filename;

typedef std::pair<x64asm::Opcode, std::vector<x64asm::Type>> EntryExternal;
typedef std::pair<vector<std::string>, EntryExternal> Entry;

typedef std::vector<Entry> Row;
typedef std::vector<std::string> IntelNmenonics;
typedef std::map<std::string, Row> Table;

extern Table leviathan_table;
extern FamilyTable leviathan_x86_family_table;
ifstream inFile;

cpputil::ValueArg<std::string>& strata_path_arg =
  cpputil::ValueArg<std::string>::create("strata_path")
  .usage("<path/to/dir>")
  .description("The path to the directory with the strata circuits (a collection of .s files)")
  .default_val("");

  cpputil::ValueArg<std::string>& lemma_start_arg =
  cpputil::ValueArg<std::string>::create("lemma_start")
  .usage(" <int>")
  .description("The starting Testcase offset )")
  .default_val("0");

   cpputil::ValueArg<std::string>& lemma_count_arg =
  cpputil::ValueArg<std::string>::create("lemma_count")
  .usage(" <int>")
  .description("The lemma count")
  .default_val("1");

   cpputil::ValueArg<std::string>& template_prefix_arg =
   cpputil::ValueArg<std::string>::create("template_prefix")
  .usage(" <string> ")
  .description("Theory prefix for batching testcases")
  .default_val("_Set0");
  
  
auto& support_only_arg = FlagArg::create("support_only").description("Only Show Supported / Unsupported");
auto& enable_flags_arg = FlagArg::create("with_flags").description("Enables generation of flags in rules");

template <typename T>
bool has_changed(T reg, SymBitVector& sym) {
  stringstream ss;
  ss << (*reg);
  if (sym.type() == SymBitVector::Type::VAR) {
    const SymBitVectorVar* const var = static_cast<const SymBitVectorVar* const>(sym.ptr);
    if (var->get_name() == ss.str()) return false;
  }
  return true;
}

template <typename T>
bool has_changed(T reg, SymBool& sym) {
  stringstream ss;
  ss << (*reg);
  if (sym.type() == SymBool::Type::VAR) {
    const SymBoolVar* const var = static_cast<const SymBoolVar* const>(sym.ptr);
    if (var->get_name() == ss.str()) return false;
  }
  return true;
}

std::pair<std::string, Entry> find_entry_by_opcode(x64asm::Opcode o)
{
	string s;
	Entry e;
	for (auto it=leviathan_table.begin(); it!=leviathan_table.end();++it) { //for each instrucftion nemonic
		s = it->first;
		for (Entry ee : it->second) {  //For each Instruction Variant of a given nmenonic
			e = ee;
			if( e.second.first == o)
				return std::make_pair (s,e);
		}
	}
	return std::make_pair (s,e); 
}

enum TestTemplate { 
tt_nullary, tt_r, tt_m, tt_m_r, tt_r_imm, tt_r_r, tt_r_m, tt_m_imm, //Gen Set
//SIMD Set
tt_simd_simd, tt_simd_m, tt_m_simd, tt_simd_r, tt_r_simd,
//Ternary Set
tt_r_r_r, tt_r_r_m, tt_simd_simd_simd, tt_simd_simd_m, tt_r_m_r, 
tt_unsupported};

enum OperandType { r, imm, m, simd, notsupported};

OperandType get_operandtype (Type t)
{
	switch (t)
	{
		case Type::RH:
		case Type::R_8:
		case Type::R_16:
		case Type::R_32:
		case Type::R_64:
			return OperandType::r;
			break;
		case Type::M_8:
		case Type::M_16:
		case Type::M_32:
		case Type::M_64:
		case Type::M_128:
		case Type::M_256:
			return OperandType::m;
			break;
		case Type::IMM_8:
		case Type::IMM_16:
		case Type::IMM_32:
		case Type::IMM_64:
			return OperandType::imm;
			break;
		case Type::XMM:
		case Type::YMM:
			return OperandType::simd;			
		default:
			break;
	}
	return OperandType::notsupported;
}

string getMemSize(Type t)
{
	switch (t)
	{
		case Type::M_8:
			return "Suc 0";
			break;
		case Type::M_16:
			return "2";
		  break;
		case Type::M_32:
			return "4";
		  break;
		case Type::M_64:
			return "8";
		  break;
		case Type::M_128:
			return "16";
			break;
		case Type::M_256:
			return "32";
			break;
		default:
			return "NAN";
			break;
	}
	return "NAN";
}

string getRegType(Type t)
{
	switch (t)
	{
		case Type::R_8:
			return "EightLow";
			break;
		case Type::RH:
			return "EightHigh";
			break;
		case Type::R_16:
			return "Sixteen";
		  break;
		case Type::R_32:
			return "ThirtyTwo";
		  break;
		case Type::R_64:
			return "SixtyFour";
		  break;
		default:
			return "NAN";
			break;
	}
	
	
	return "NAN";
}

string getOperands_r_r(Type t, Type t2)
{
	switch (t)
	{
		case Type::R_16:
			if(t2== Type::R_16) {
				return "bx, cx";
			} else if(t2== Type::R_8) {
				return "bx, cl";
			} else if(t2== Type::RH) {
//				return "bx, ah";
				return "bx, ch";
			}	
		  break;
		case Type::R_32:
			if(t2== Type::R_32) {
				return "ebx, ecx";
			} else if(t2== Type::R_8) {
				return "ebx, cl";
			} else if(t2== Type::RH) {
//				return "ebx, ah";
				return "ebx, ch";
			} else if(t2== Type::R_16) {
				return "ebx, cx";
			}
		  break;
		case Type::R_64:
			if(t2== Type::R_64) {
				return "rbx, rcx";
			} else if(t2== Type::R_8) {
				return "rbx, cl";
			} else if(t2== Type::RH) {
//				return "rbx, ah";
				return "rbx, ch";
			} else if(t2== Type::R_16) {
				return "rbx, cx";
			} else if(t2== Type::R_32) {
				return "rbx, ecx";
			}
		  break;
		case Type::RH:
			if( t2== Type::RH)
			{
//				return "ah, bh";
				return "bh, ch";
			} else
			{
//				return "ah, bl";				
				return "bh, cl";				
			}				
		  break;
		case Type::R_8:
			if( t2== Type::RH)
			{
//				return "bl, ah";
				return "bl, ch";
			} else
			{
				return "bl, cl";				
			}				
		  break;
		 
		default:
			break;
	}

	return "NAN";
}

int getOperands_r_r_type(Type t, Type t2)
{
	return 12;
	switch (t)
	{
		case Type::R_16:
			if(t2== Type::R_16) {
				return 12;
			} else if(t2== Type::R_8) {
				return 12;
			} else if(t2== Type::RH) {
				return 10;
			}	
		  break;
		case Type::R_32:
			if(t2== Type::R_32) {
				return 12;
			} else if(t2== Type::R_8) {
				return 12;
			} else if(t2== Type::RH) {
				return 10;
			} else if(t2== Type::R_16) {
				return 12;
			}
		  break;
		case Type::R_64:
			if(t2== Type::R_64) {
				return 12;
			} else if(t2== Type::R_8) {
				return 12;
			} else if(t2== Type::RH) {
				return 10;
			} else if(t2== Type::R_16) {
				return 10;
			} else if(t2== Type::R_32) {
				return 12;
			}
		  break;
		case Type::RH:
			if( t2== Type::RH)
			{
				return 1;
			} else
			{
				return 1;				
			}				
		  break;
		case Type::R_8:
			if( t2== Type::RH)
			{
				return 10;
			} else
			{
				return 12;				
			}				
		  break;
		 
		default:
			break;
	}

	return 0;
}

string getOperands_r(Type t)
{
	switch (t)
	{
		case Type::R_16:
			return "bx";
			break;
		case Type::R_32:
			return "ebx";
			break;
		case Type::R_64:
			return "rbx";
			break;
		case Type::RH:
//			return "ah";	
			return "bh";	
			break;
		case Type::R_8:
			return "bl";	
			break;
		default:
			break;
	}

	return "NAN";
}

int getOperands_r_type(Type t)
{
	return 1; //rbx
	switch (t)
	{
		case Type::RH:
			return 0;
			break;
		default:
			return 1;
			break;
	}
	return 1;
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

void read_simd_reg(unsigned long long *ymmreg)
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


unsigned long long swap_byte_order(unsigned long long memop)
{
		return ((memop & 0xff) << 56) + 
						 (((memop >> 8 )& 0xff) << 48) + 
						 (((memop >> 16 )& 0xff) << 40) + 
						 (((memop >> 24 )& 0xff) << 32) + 
						 (((memop >> 32 )& 0xff) << 24) + 
						 (((memop >> 40 )& 0xff) << 16) + 
						 (((memop >> 48 )& 0xff) << 8) + 
						  ((memop >> 52 )& 0xff)  
						 ;

}
unsigned long long get_testcase_register(int casenumber, int regoffset)
{
	unsigned long long qword;
	int lines_skip = (casenumber*78)+4+regoffset;
	char buffer[300];
	
	inFile.clear();
	inFile.seekg(0, ios::beg);
	
	for(int i=0;i<lines_skip;i++) {
		inFile.getline(buffer,300);
	}
	qword = read_reg();
	return qword;
}

void get_testcase_simd_register(int casenumber, int regoffset, unsigned long long *simd_reg)
{
	unsigned long long qword;
	int lines_skip = (casenumber*78)+21+regoffset;
	char buffer[300];
	
	inFile.clear();
	inFile.seekg(0, ios::beg);
	
	for(int i=0;i<lines_skip;i++) {
		inFile.getline(buffer,300);
	}
	read_simd_reg(simd_reg);
}

string add_hex_prefix(string s)
{
	stringstream ss;
	ss << "0x" << s;
	return ss.str();
}
string reg_to_imm(Type t, unsigned long long qword)
{
	stringstream ss;
	
	switch (t)
	{
		case Type::IMM_8:
			ss << "0x" << hex << (qword & 0xff);
			break;
		case Type::IMM_16:
			ss << "0x" << hex << (qword & 0xffff);
			break;
		case Type::IMM_32:
			ss << "0x" << hex << (qword & 0xffffffff);
			break;
		case Type::IMM_64:
			ss << "0x" << hex << (qword & 0xffffffffffffffff);
			break;	
		default:
			break;
	}
	return ss.str();
	
}

void reg_to_m(unsigned long long qword, string& s7,string& s6,string& s5,string& s4,
										string& s3,string& s2,string& s1,string& s0)
{
	stringstream ss[8];
	
	ss[0] << setfill('0') << setw(2) << hex << ((qword      ) & 0xff);
	ss[1] << setfill('0') << setw(2) << hex << ((qword >>  8) & 0xff);
	ss[2] << setfill('0') << setw(2) << hex << ((qword >> 16) & 0xff);
	ss[3] << setfill('0') << setw(2) << hex << ((qword >> 24) & 0xff);
	ss[4] << setfill('0') << setw(2) << hex << ((qword >> 32) & 0xff);
	ss[5] << setfill('0') << setw(2) << hex << ((qword >> 40) & 0xff);
	ss[6] << setfill('0') << setw(2) << hex << ((qword >> 48) & 0xff);
	ss[7] << setfill('0') << setw(2) << hex << ((qword >> 56) & 0xff);
	
	s0=ss[0].str();
	s1=ss[1].str();
	s2=ss[2].str();
	s3=ss[3].str();
	s4=ss[4].str();
	s5=ss[5].str();
	s6=ss[6].str();
	s7=ss[7].str();
	
}

void simdreg_to_m(unsigned long long* simd_reg, 
						string& s31, string& s30, string& s29, string& s28,
						string& s27, string& s26, string& s25, string& s24,
						string& s23, string& s22, string& s21, string& s20,
						string& s19, string& s18, string& s17, string& s16,
						string& s15, string& s14, string& s13, string& s12,
						string& s11, string& s10, string& s9,  string& s8,
						string& s7,  string& s6,  string& s5,  string& s4,
						string& s3,  string& s2,  string& s1,  string& s0)
{
	stringstream ss3[8],ss2[8],ss1[8],ss0[8];
	
	ss0[0] << setfill('0') << setw(2) << hex << ((simd_reg[0]      ) & 0xff);
	ss0[1] << setfill('0') << setw(2) << hex << ((simd_reg[0] >>  8) & 0xff);
	ss0[2] << setfill('0') << setw(2) << hex << ((simd_reg[0] >> 16) & 0xff);
	ss0[3] << setfill('0') << setw(2) << hex << ((simd_reg[0] >> 24) & 0xff);
	ss0[4] << setfill('0') << setw(2) << hex << ((simd_reg[0] >> 32) & 0xff);
	ss0[5] << setfill('0') << setw(2) << hex << ((simd_reg[0] >> 40) & 0xff);
	ss0[6] << setfill('0') << setw(2) << hex << ((simd_reg[0] >> 48) & 0xff);
	ss0[7] << setfill('0') << setw(2) << hex << ((simd_reg[0] >> 56) & 0xff);
	s0=ss0[0].str();s1=ss0[1].str();s2=ss0[2].str();s3=ss0[3].str();
	s4=ss0[4].str();s5=ss0[5].str();s6=ss0[6].str();s7=ss0[7].str();
	
	ss1[0] << setfill('0') << setw(2) << hex << ((simd_reg[1]      ) & 0xff);
	ss1[1] << setfill('0') << setw(2) << hex << ((simd_reg[1] >>  8) & 0xff);
	ss1[2] << setfill('0') << setw(2) << hex << ((simd_reg[1] >> 16) & 0xff);
	ss1[3] << setfill('0') << setw(2) << hex << ((simd_reg[1] >> 24) & 0xff);
	ss1[4] << setfill('0') << setw(2) << hex << ((simd_reg[1] >> 32) & 0xff);
	ss1[5] << setfill('0') << setw(2) << hex << ((simd_reg[1] >> 40) & 0xff);
	ss1[6] << setfill('0') << setw(2) << hex << ((simd_reg[1] >> 48) & 0xff);
	ss1[7] << setfill('0') << setw(2) << hex << ((simd_reg[1] >> 56) & 0xff);
	s8=ss1[0].str();s9=ss1[1].str();s10=ss1[2].str();s11=ss1[3].str();
	s12=ss1[4].str();s13=ss1[5].str();s14=ss1[6].str();s15=ss1[7].str();
	
	ss2[0] << setfill('0') << setw(2) << hex << ((simd_reg[2]      ) & 0xff);
	ss2[1] << setfill('0') << setw(2) << hex << ((simd_reg[2] >>  8) & 0xff);
	ss2[2] << setfill('0') << setw(2) << hex << ((simd_reg[2] >> 16) & 0xff);
	ss2[3] << setfill('0') << setw(2) << hex << ((simd_reg[2] >> 24) & 0xff);
	ss2[4] << setfill('0') << setw(2) << hex << ((simd_reg[2] >> 32) & 0xff);
	ss2[5] << setfill('0') << setw(2) << hex << ((simd_reg[2] >> 40) & 0xff);
	ss2[6] << setfill('0') << setw(2) << hex << ((simd_reg[2] >> 48) & 0xff);
	ss2[7] << setfill('0') << setw(2) << hex << ((simd_reg[2] >> 56) & 0xff);
	s16=ss2[0].str();s17=ss2[1].str();s18=ss2[2].str();s19=ss2[3].str();
	s20=ss2[4].str();s21=ss2[5].str();s22=ss2[6].str();s23=ss2[7].str();
	
	ss3[0] << setfill('0') << setw(2) << hex << ((simd_reg[3]      ) & 0xff);
	ss3[1] << setfill('0') << setw(2) << hex << ((simd_reg[3] >>  8) & 0xff);
	ss3[2] << setfill('0') << setw(2) << hex << ((simd_reg[3] >> 16) & 0xff);
	ss3[3] << setfill('0') << setw(2) << hex << ((simd_reg[3] >> 24) & 0xff);
	ss3[4] << setfill('0') << setw(2) << hex << ((simd_reg[3] >> 32) & 0xff);
	ss3[5] << setfill('0') << setw(2) << hex << ((simd_reg[3] >> 40) & 0xff);
	ss3[6] << setfill('0') << setw(2) << hex << ((simd_reg[3] >> 48) & 0xff);
	ss3[7] << setfill('0') << setw(2) << hex << ((simd_reg[3] >> 56) & 0xff);
	s24=ss3[0].str();s25=ss3[1].str();s26=ss3[2].str();s27=ss3[3].str();
	s28=ss3[4].str();s29=ss3[5].str();s30=ss3[6].str();s31=ss3[7].str();
	
}


string getOperands_r_op1(Type t)
{
	stringstream ss;
	switch (t)
	{
		case Type::RH:
//			ss << "ah, ";
			ss << "bh, ";
		  break;
		case Type::R_8:
			ss << "bl, ";
		  break;
		case Type::R_16:
			ss << "bx, ";
		  break;
		case Type::R_32:
			ss << "ebx, ";
		  break;
		case Type::R_64:
			ss << "rbx, ";
		  break;
		default:
			ss << "Meh, ";
			break;
	}

	return ss.str();
}

string getOperands_m_r(Type t)
{
	stringstream ss;
	switch (t)
	{
		case Type::RH:
//			ss << ", ah";
			ss << ", ch";
		  break;
		case Type::R_8:
			ss << ", cl";
		  break;
		case Type::R_16:
			ss << ", cx";
		  break;
		case Type::R_32:
			ss << ", ecx";
		  break;
		case Type::R_64:
			ss << ", rcx";
		  break;
		default:
			ss << ", Meh";
			break;
	}
	return ss.str();
}


string sizeof_Type_bits(Type t)
{
	switch (t)
	{
		case Type::RH:
			return "h";			
			break;
		case Type::IMM_8:
		case Type::R_8:
		case Type::M_8:
			return "8";
			break;
		case Type::IMM_16:
		case Type::R_16:
		case Type::M_16:
			return "16";
		  break;
		case Type::IMM_32:
		case Type::R_32:
		case Type::M_32:
			return "32";
		  break;
		case Type::IMM_64:
		case Type::R_64:
		case Type::M_64:
			return "64";
		  break;
		case Type::XMM:
		case Type::M_128:
			return "128";
			break;
		case Type::YMM:
		case Type::M_256:
			return "256";
			break;
		default:
			return "NAN";
			break;
	}
	return "NAN";
}

TestTemplate get_template ( Entry e)
{
	if (e.second.second.size()==0)
	{ 
		return TestTemplate::tt_nullary;
	}
	if(e.second.second.size()==1) 
	{
		switch(get_operandtype(e.second.second[0]))
		{
			case OperandType::r:
				return TestTemplate::tt_r;
				break;
			case OperandType::m:
				return TestTemplate::tt_m;
				break;
			default:
				return TestTemplate::tt_unsupported;
				break;
		}
	} 
	
	if(e.second.second.size()==2) {
	switch(get_operandtype(e.second.second[0]))
	{
		case OperandType::r:
				switch (get_operandtype(e.second.second[1]))
				{
					case OperandType::imm:
						return TestTemplate::tt_r_imm;
						break;
					case OperandType::m:
						return TestTemplate::tt_r_m;
						break;
					case OperandType::r:
						return TestTemplate::tt_r_r;
						break;
					case OperandType::simd:
						return TestTemplate::tt_r_simd;
						break;
					default:
						break;
				}					
				break;
		case OperandType::m:
				switch (get_operandtype(e.second.second[1]))
				{
					case OperandType::imm:
						return TestTemplate::tt_m_imm;
						break;
					case OperandType::simd:
						return TestTemplate::tt_m_simd;
						break;
					case OperandType::r:
						return TestTemplate::tt_m_r;
						break;
					default:
						break;
				}					
				break;
		case OperandType::simd:
				switch (get_operandtype(e.second.second[1]))
				{
					case OperandType::simd:
						return TestTemplate::tt_simd_simd;
						break;
					case OperandType::m:
						return TestTemplate::tt_simd_m;
						break;
					case OperandType::r:
						return TestTemplate::tt_simd_r;
						break;
					default:
						break;
				}					
				break;
		default:
			break;
	} }
	return TestTemplate::tt_unsupported;
}

std::string get_lemmas(std::string filename, int count, int start)
{
	char *buffer; 
	int i;
	std::streambuf* raw_buffer; 
	ifstream template_file;
	std::stringstream lemmas;
	
	template_file.open(filename, std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int k=raw_buffer->sgetn(buffer, 20000);
	buffer[k]=0;
	
	for(i=0;i<count;i++)
	{
		lemmas << boost::format(buffer) % (start+i+1);
	}
	template_file.close();
	delete buffer;
	return lemmas.str();
}


std::string get_iopairs_nullary(int count, int start, std::string pin_instr, bool flags)
{
	char *buffer; 
	int i;
	std::streambuf* raw_buffer; 
	ifstream template_file;
	std::stringstream iopairs;
	
	template_file.open("/root/TestLemmas/Templates/Template_IOPair.thy", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int k=raw_buffer->sgetn(buffer, 20000);
	buffer[k]=0;
	
	ifstream f;
		
	for(i=0;i<count;i++)
	{
		char dst_start[50],dst_end[50],src_start[50],src_end[50],flag_in[500],flag_out[500],rax_start[50],rax_end[50],rdx_start[50],rdx_end[50];
		
		//get iopair from pintool instrument
		std::stringstream s_tmp;
				s_tmp << "cd && ./runpin.sh " << (start+i) << " 1 2 " <<  pin_instr ;
			int j = std::system(s_tmp.str().c_str());
			j++;
			
		f.open("/root/chum_test.out");
		f.getline(dst_start,50);
		f.getline(dst_end,50);
		f.getline(src_start,50);
		f.getline(src_end,50);
		f.getline(flag_in,500);
		f.getline(flag_out,500);
		f.getline(rax_start,50);
		f.getline(rax_end,50);
		f.getline(rdx_start,50);
		f.getline(rdx_end,50);

		f.close();		
		
		stringstream xtra_regs_start;
		stringstream xtra_regs_end;
		xtra_regs_start << rax_start << "," << rdx_start;
		xtra_regs_end << rax_end << "," << rdx_end;
		
		if (flags==true) {
				iopairs << boost::format(buffer) % (start+i+1) % dst_start % dst_end % src_start % src_end % flag_in % flag_out % xtra_regs_start.str()% xtra_regs_end.str() << std::flush;			
		} else {
				iopairs << boost::format(buffer) % (start+i+1) % dst_start % dst_end % src_start % src_end % "" % "" % xtra_regs_start.str() % xtra_regs_end.str() << std::flush;
		}
			
	}
	template_file.close();
	delete buffer;
	return iopairs.str();

}


std::string get_iopairs_r(int count, int start, int op1, std::string pin_instr, bool flags, bool write_rax)
{
	char *buffer; 
	int i;
	std::streambuf* raw_buffer; 
	ifstream template_file;
	std::stringstream iopairs;
	
	template_file.open("/root/TestLemmas/Templates/Template_IOPair.thy", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int k=raw_buffer->sgetn(buffer, 20000);
	buffer[k]=0;
	
	ifstream f;
		
	for(i=0;i<count;i++)
	{
		char dst_start[50],dst_end[50],src_start[50],src_end[50],flag_in[500],flag_out[500],rax_start[50],rax_end[50];
		
		//get iopair from pintool instrument
		std::stringstream s_tmp;
				s_tmp << "cd && ./runpin.sh " << (start+i) << " " << op1 << " " << op1 << " " <<  pin_instr ;
			int j = std::system(s_tmp.str().c_str());
			j++;
			
		f.open("/root/chum_test.out");
		f.getline(dst_start,50);
		f.getline(dst_end,50);
		f.getline(src_start,50);
		f.getline(src_end,50);
		f.getline(flag_in,500);
		f.getline(flag_out,500);
		f.getline(rax_start,50);
		f.getline(rax_end,50);
		cout << "dst_start=" << dst_start << endl;
		f.close();		
		if (flags==true) {
			if (write_rax) {
				iopairs << boost::format(buffer) % (start+i+1) % dst_start % dst_end % src_start % src_end % flag_in % flag_out % rax_start % rax_end << std::flush;
			} else {
				iopairs << boost::format(buffer) % (start+i+1) % dst_start % dst_end % src_start % src_end % flag_in % flag_out % "" % "" << std::flush;
			}
			
		} else {
			if (write_rax) {
				iopairs << boost::format(buffer) % (start+i+1) % dst_start % dst_end % src_start % src_end % "" % "" % rax_start % rax_end << std::flush;
			} else {
				iopairs << boost::format(buffer) % (start+i+1) % dst_start % dst_end % src_start % src_end % "" % "" % "" % "" << std::flush;
			}
		}
			
	}
	template_file.close();
	delete buffer;
	return iopairs.str();

}

std::string get_iopairs_r_r(int count, int start, int op1, int op2, std::string pin_instr, bool flags, bool write_rax)
{
	char *buffer; 
	int i;
	std::streambuf* raw_buffer; 
	ifstream template_file;
	std::stringstream iopairs;
	
	template_file.open("/root/TestLemmas/Templates/Template_IOPair.thy", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int k=raw_buffer->sgetn(buffer, 20000);
	buffer[k]=0;
	
	ifstream f;
		
	for(i=0;i<count;i++)
	{
		char dst_start[50],dst_end[50],src_start[50],src_end[50],flag_in[500],flag_out[500],rax_start[50],rax_end[50];
		
		//get iopair from pintool instrument
		std::stringstream s_tmp;
				s_tmp << "cd && ./runpin.sh " << (start+i) << " " << op1 << " " << op2 << " " <<  pin_instr ;
			int j = std::system(s_tmp.str().c_str());
			j++;
			
		f.open("/root/chum_test.out");
		f.getline(dst_start,50);
		f.getline(dst_end,50);
		f.getline(src_start,50);
		f.getline(src_end,50);
		f.getline(flag_in,500);
		f.getline(flag_out,500);
		f.getline(rax_start,50);
		f.getline(rax_end,50);
		cout << "dst_start=" << dst_start << endl;
		f.close();		
		if (flags==true) {
			if (write_rax) {
				iopairs << boost::format(buffer) % (start+i+1) % dst_start % dst_end % src_start % src_end % flag_in % flag_out % rax_start % rax_end << std::flush;
			} else {
				iopairs << boost::format(buffer) % (start+i+1) % dst_start % dst_end % src_start % src_end % flag_in % flag_out % "" % "" << std::flush;
			}
			
		} else {
			if (write_rax) {
				iopairs << boost::format(buffer) % (start+i+1) % dst_start % dst_end % src_start % src_end % "" % "" % rax_start % rax_end << std::flush;
			} else {
				iopairs << boost::format(buffer) % (start+i+1) % dst_start % dst_end % src_start % src_end % "" % "" % "" % "" << std::flush;
			}
		}
			
	}
	template_file.close();
	delete buffer;
	return iopairs.str();

}

std::string get_iopairs_r_imm(string instr, Type t1, Type t2, int count, int start, bool flags)
{
	char *buffer; 
	int i,lemma_i;
	std::streambuf* raw_buffer; 
	ifstream template_file;
	std::stringstream iopairs;
	
	template_file.open("/root/TestLemmas/Templates/Template_IOPair.thy", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int k=raw_buffer->sgetn(buffer, 20000);
	buffer[k]=0;
	
	ifstream f;
		
	for(lemma_i=0;lemma_i<count;lemma_i++)
	{
		char dst_start[50],dst_end[50],src_start[50],src_end[50],flag_in[500],flag_out[500],rax_start[50],rax_end[50];
		char *buffer2; 
		unsigned long long imm_register;
		
		//Create and open the Pintool Instrument file for the instruction
		std::stringstream tmp_pintool_filename;
		tmp_pintool_filename << "/root/tmp_Pintool_Instrument_"<< template_prefix_arg.value() <<".s";
		ofstream tmp_pintool_file;		
		tmp_pintool_file.open(tmp_pintool_filename.str());	
		
		//Build  Assembly File
		stringstream s_tmp2;
		string s_op1=getOperands_r_op1(t1);
		string s_imm;
		imm_register=get_testcase_register(start+lemma_i,1);
		s_imm=reg_to_imm(t2,imm_register);
		s_tmp2 << s_op1 << s_imm;
		
		ifstream template_assembly;
		template_assembly.open("/root/TestLemmas/Templates/Template_Assembly_r_imm.s", std::ifstream::binary);
		buffer2 = new char[20000];
		raw_buffer = template_assembly.rdbuf(); 
		i=raw_buffer->sgetn(buffer2, 20000);
		buffer2[i]=0;			
		tmp_pintool_file << boost::format(buffer2) % instr % s_tmp2.str();
		template_assembly.close();
		tmp_pintool_file.close();

		//compile pintool instrument
		std::stringstream s_tmp;
		s_tmp << "cd && gcc /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value() <<".s -o /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value();
		int j = std::system(s_tmp.str().c_str());
		j++;
		
		//get iopair from pintool instrument
		std::stringstream s_tmp3;
				s_tmp3 << "cd && ./runpin.sh " << (start+lemma_i) << " 1 2 /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value() ;
		int j2 = std::system(s_tmp3.str().c_str());
		j2++;
			
		f.open("/root/chum_test.out");
		f.getline(dst_start,50);
		f.getline(dst_end,50);
		f.getline(src_start,50);
		f.getline(src_end,50);
		f.getline(flag_in,500);
		f.getline(flag_out,500);
		f.getline(rax_start,50);
		f.getline(rax_end,50);
		cout << instr << " " << s_tmp2.str() << endl;
		f.close();		
		if (flags==true) {
			iopairs << boost::format(buffer) % (start+lemma_i+1) % dst_start % dst_end % s_imm % s_imm % flag_in % flag_out % "" % "" << std::flush;
		} else {
			iopairs << boost::format(buffer) % (start+lemma_i+1) % dst_start % dst_end % s_imm % s_imm % "" % "" % "" % ""  << std::flush;
		}			
	}
	template_file.close();
	delete buffer;
	return iopairs.str();

}

std::string get_iopairs_r_m(string instr, Type t1, Type t2, int count, int start, bool flags, bool write_rax)
{
	char *buffer; 
	int i,lemma_i;
	std::streambuf* raw_buffer; 
	ifstream template_file;
	std::stringstream iopairs;
	
	template_file.open("/root/TestLemmas/Templates/Template_IOPair.thy", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int k=raw_buffer->sgetn(buffer, 20000);
	buffer[k]=0;
	
	ifstream f;
		
	for(lemma_i=0;lemma_i<count;lemma_i++)
	{
		char dst_start[50],dst_end[50],src_start[50],src_end[50],flag_in[500],flag_out[500],rax_start[50],rax_end[50],rdx_start[50],rdx_end[50],memory_op[50],throwaway[300];
		char *buffer2; 
		unsigned long long m_register; // as the test case is generalized off of a register equivalent and this is the register associated with the test case that needs to end up in memory

		
		//Create and open the Pintool Instrument file for the instruction
		std::stringstream tmp_pintool_filename;
		tmp_pintool_filename << "/root/tmp_r_m_Pintool_Instrument_"<< template_prefix_arg.value() <<".s";
		ofstream tmp_pintool_file;		
		tmp_pintool_file.open(tmp_pintool_filename.str());	
		
		//Build  Assembly File
		stringstream s_tmp2;
		
		string mem_ptr;
		switch (t2) {
			default:
			case Type::M_64:
				mem_ptr = "qword ptr";
				break;
			case Type::M_32:
				mem_ptr = "dword ptr";
				break;
			case Type::M_16:
				mem_ptr = "word ptr";
				break;
			case Type::M_8:
				mem_ptr = "byte ptr";
				break;
		}
		string s_op1=getOperands_r_op1(t1);
		string s_m[8];
		string s_m_end[8];
		m_register=get_testcase_register(start+lemma_i,1);
		reg_to_m(m_register, s_m[7], s_m[6], s_m[5], s_m[4], s_m[3], s_m[2], s_m[1], s_m[0]);
		s_tmp2 << instr << " " << s_op1 << mem_ptr << " ";
		
		ifstream template_assembly;
		template_assembly.open("/root/TestLemmas/Templates/Template_Assembly_r_m.s", std::ifstream::binary);
		buffer2 = new char[20000];
		raw_buffer = template_assembly.rdbuf(); 
		i=raw_buffer->sgetn(buffer2, 20000);
		buffer2[i]=0;			
		tmp_pintool_file << boost::format(buffer2) % 
			s_tmp2.str() % add_hex_prefix(s_m[0]) % add_hex_prefix(s_m[1]) % add_hex_prefix(s_m[2]) % 
			add_hex_prefix(s_m[3]) % add_hex_prefix(s_m[4]) % add_hex_prefix(s_m[5]) % add_hex_prefix(s_m[6]) % 
			add_hex_prefix(s_m[7]);
		template_assembly.close();
		tmp_pintool_file.close();

		//compile pintool instrument
		std::stringstream s_tmp;
		s_tmp << "cd && gcc /root/tmp_r_m_Pintool_Instrument_"<< template_prefix_arg.value() <<".s -o /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value() ;
		int j = std::system(s_tmp.str().c_str());
		j++;
		
		//get iopair from pintool instrument
		std::stringstream s_tmp3;
				s_tmp3 << "cd && ./runpin.sh " << (start+lemma_i) << " 1 2 /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value() ;
		int j2 = std::system(s_tmp3.str().c_str());
		j2++;
			
		f.open("/root/chum_test.out");
		f.getline(dst_start,50);
		f.getline(dst_end,50);
		f.getline(src_start,50);
		f.getline(src_end,50);
		f.getline(flag_in,500);
		f.getline(flag_out,500);
		f.getline(rax_start,50);
		f.getline(rax_end,50);
		f.getline(rdx_start,50);
		f.getline(rdx_end,50);
		f.getline(throwaway,300); //ymm0_start
		f.getline(throwaway,300); //ymm0_end
		f.getline(throwaway,300); //ymm1_start
		f.getline(throwaway,300); //ymm1_end
		f.getline(throwaway,300); //ymm2_start
		f.getline(throwaway,300); //ymm2_end
		f.getline(throwaway,300); //ymm3_start
		f.getline(throwaway,300); //ymm3_end
		f.getline(throwaway,300); //ymm4_start
		f.getline(throwaway,300); //ymm4_end		
		bool mem_used=false;
		f >> mem_used;
		if (mem_used) {
			unsigned long long l;
			f >> hex >> l;
			reg_to_m(l, s_m_end[7], s_m_end[6], s_m_end[5], s_m_end[4], s_m_end[3], 
					s_m_end[2], s_m_end[1], s_m_end[0]);
		} else { 
			for (int count=0;count<8;count++) s_m_end[count]=s_m[count];
		}
		
		stringstream s_tmp4;
		stringstream s_tmp5;
		switch (t2) {
			default:
			case Type::M_64:
				s_tmp4 << "0x" << s_m[0] << s_m[1] << s_m[2] << s_m[3] << s_m[4] << s_m[5] << s_m[6] << s_m[7]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1] << s_m_end[2] << s_m_end[3] << s_m_end[4] << s_m_end[5] << s_m_end[6] << s_m_end[7]; 
				break;
			case Type::M_32:
				s_tmp4 << "0x" << s_m[0] << s_m[1] << s_m[2] << s_m[3]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1] << s_m_end[2] << s_m_end[3]; 
				break;
			case Type::M_16:
				s_tmp4 << "0x" << s_m[0] << s_m[1]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1]; 
				break;
			case Type::M_8:
				s_tmp4 << "0x" << s_m[0]; 
				s_tmp5 << "0x" << s_m_end[0]; 
				break;
		}

		cout << s_tmp2.str() << " [mem=" << s_tmp4.str() <<"->" <<  s_tmp5.str() <<"]" << endl;
		f.close();		
		if (flags==true) {
			if(write_rax) {
				iopairs << boost::format(buffer) % (start+lemma_i+1) % dst_start % dst_end % s_tmp4.str() % s_tmp5.str() % flag_in % flag_out % rax_start % rax_end << std::flush;
			} else {
				iopairs << boost::format(buffer) % (start+lemma_i+1) % dst_start % dst_end % s_tmp4.str() % s_tmp5.str() % flag_in % flag_out % "" % "" << std::flush;
			}
		} else {
			if(write_rax) {
				iopairs << boost::format(buffer) % (start+lemma_i+1) % dst_start % dst_end % s_tmp4.str() % s_tmp5.str() % "" % "" % rax_start % rax_end << std::flush;
			} else {
				iopairs << boost::format(buffer) % (start+lemma_i+1) % dst_start % dst_end % s_tmp4.str() % s_tmp5.str() % "" % "" % "" % "" << std::flush;
			}
		}			
	}
	template_file.close();
	delete buffer;
	return iopairs.str();

}

std::string get_iopairs_m_r(string instr, Type t1, Type t2, int count, int start, bool flags, bool write_rax)
{
	char *buffer; 
	int i,lemma_i;
	std::streambuf* raw_buffer; 
	ifstream template_file;
	std::stringstream iopairs;
	
	template_file.open("/root/TestLemmas/Templates/Template_IOPair.thy", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int k=raw_buffer->sgetn(buffer, 20000);
	buffer[k]=0;
	
	ifstream f;
		
	for(lemma_i=0;lemma_i<count;lemma_i++)
	{
		char dst_start[50],dst_end[50],src_start[50],src_end[50],flag_in[500],flag_out[500],rax_start[50],rax_end[50],rdx_start[50],rdx_end[50],memory_op[50],throwaway[300];
		char *buffer2; 
		unsigned long long m_register; // as the test case is generalized off of a register equivalent and this is the register associated with the test case that needs to end up in memory

		
		//Create and open the Pintool Instrument file for the instruction
		std::stringstream tmp_pintool_filename;
		tmp_pintool_filename << "/root/tmp_m_r_Pintool_Instrument_"<< template_prefix_arg.value() <<".s";
		ofstream tmp_pintool_file;		
		tmp_pintool_file.open(tmp_pintool_filename.str());	
		
		//Build  Assembly File
		m_register=get_testcase_register(start+lemma_i,3); //rbx
		string mem_ptr;
		switch (t1) {
			default:
			case Type::M_64:
				mem_ptr = "qword ptr";
				break;
			case Type::M_32:
				mem_ptr = "dword ptr";
				break;
			case Type::M_16:
				mem_ptr = "word ptr";
				break;
			case Type::M_8:
				mem_ptr = "byte ptr";
				break;
		}
		string s_op2=getOperands_m_r(t2);
		string s_m[8];
		string s_m_end[8];
		reg_to_m(m_register, s_m[7], s_m[6], s_m[5], s_m[4], s_m[3], s_m[2], s_m[1], s_m[0]);
		ifstream template_assembly;
		template_assembly.open("/root/TestLemmas/Templates/Template_Assembly_m_r.s", std::ifstream::binary);
		buffer2 = new char[20000];
		raw_buffer = template_assembly.rdbuf(); 
		i=raw_buffer->sgetn(buffer2, 20000);
		buffer2[i]=0;			
		tmp_pintool_file << boost::format(buffer2) % instr % mem_ptr %
			s_op2 % add_hex_prefix(s_m[0]) % add_hex_prefix(s_m[1]) % add_hex_prefix(s_m[2]) % 
			add_hex_prefix(s_m[3]) % add_hex_prefix(s_m[4]) % add_hex_prefix(s_m[5]) % add_hex_prefix(s_m[6]) % 
			add_hex_prefix(s_m[7]);
		template_assembly.close();
		tmp_pintool_file.close();

		//compile pintool instrument
		std::stringstream s_tmp;
		s_tmp << "cd && gcc /root/tmp_m_r_Pintool_Instrument_"<< template_prefix_arg.value() <<".s -o /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value();
		int j = std::system(s_tmp.str().c_str());
		j++;
		
		//get iopair from pintool instrument
		std::stringstream s_tmp3;
				s_tmp3 << "cd && ./runpin.sh " << (start+lemma_i) << " 1 2 /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value();
		int j2 = std::system(s_tmp3.str().c_str());
		j2++;
			
		f.open("/root/chum_test.out");
		f.getline(dst_start,50);
		f.getline(dst_end,50);
		f.getline(src_start,50);
		f.getline(src_end,50);
		f.getline(flag_in,500);
		f.getline(flag_out,500);
		f.getline(rax_start,50);
		f.getline(rax_end,50);
		f.getline(rdx_start,50);
		f.getline(rdx_end,50);
		f.getline(throwaway,300); //ymm0_start
		f.getline(throwaway,300); //ymm0_end
		f.getline(throwaway,300); //ymm1_start
		f.getline(throwaway,300); //ymm1_end
		f.getline(throwaway,300); //ymm2_start
		f.getline(throwaway,300); //ymm2_end
		f.getline(throwaway,300); //ymm3_start
		f.getline(throwaway,300); //ymm3_end
		f.getline(throwaway,300); //ymm4_start
		f.getline(throwaway,300); //ymm4_end
		bool mem_used=false;
		f >> mem_used;
		
		if (mem_used) {
			unsigned long long l;
			f >> hex >> l;
			reg_to_m(l, s_m_end[7], s_m_end[6], s_m_end[5], s_m_end[4], s_m_end[3], 
					s_m_end[2], s_m_end[1], s_m_end[0]);
		} else { 
			for (int count=0;count<8;count++) s_m_end[count]=s_m[count];
		}
		
		stringstream s_tmp4;
		stringstream s_tmp5;
		switch (t1) {
			default:
			case Type::M_64:
				s_tmp4 << "0x" << s_m[0] << s_m[1] << s_m[2] << s_m[3] << s_m[4] << s_m[5] << s_m[6] << s_m[7]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1] << s_m_end[2] << s_m_end[3] << s_m_end[4] << s_m_end[5] << s_m_end[6] << s_m_end[7]; 
				break;
			case Type::M_32:
				s_tmp4 << "0x" << s_m[0] << s_m[1] << s_m[2] << s_m[3]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1] << s_m_end[2] << s_m_end[3]; 
				break;
			case Type::M_16:
				s_tmp4 << "0x" << s_m[0] << s_m[1]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1]; 
				break;
			case Type::M_8:
				s_tmp4 << "0x" << s_m[0]; 
				s_tmp5 << "0x" << s_m_end[0]; 
				break;
		}


		
		cout << instr << " [mem=" << s_tmp4.str() <<"]" << s_op2 << endl;
		f.close();		
		if (flags==true) {
			if (write_rax) {
				iopairs << boost::format(buffer) % (start+lemma_i+1) % s_tmp4.str() % s_tmp5.str() % src_start % src_end % flag_in % flag_out % rax_start % rax_end << std::flush;
			} else {
				iopairs << boost::format(buffer) % (start+lemma_i+1) % s_tmp4.str() % s_tmp5.str() % src_start % src_end % flag_in % flag_out % "" % "" << std::flush;
			}
		} else {
			if (write_rax) {
				iopairs << boost::format(buffer) % (start+lemma_i+1) % s_tmp4.str() % s_tmp5.str() % src_start % src_end % "" % "" % rax_start % rax_end << std::flush;
			} else {
				iopairs << boost::format(buffer) % (start+lemma_i+1) % s_tmp4.str() % s_tmp5.str() % src_start % src_end % "" % "" % "" % "" << std::flush;
			}
		}			
	}
	template_file.close();
	delete buffer;
	return iopairs.str();

}

std::string get_iopairs_m_imm(string instr, Type t1, Type t2, int count, int start, bool flags)
{
	char *buffer; 
	int i,lemma_i;
	std::streambuf* raw_buffer; 
	ifstream template_file;
	std::stringstream iopairs;
	
	template_file.open("/root/TestLemmas/Templates/Template_IOPair.thy", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int k=raw_buffer->sgetn(buffer, 20000);
	buffer[k]=0;
	
	ifstream f;
		
	for(lemma_i=0;lemma_i<count;lemma_i++)
	{
		char dst_start[50],dst_end[50],src_start[50],src_end[50],flag_in[500],flag_out[500],rax_start[50],rax_end[50],rdx_start[50],rdx_end[50],memory_op[50],throwaway[300];
		char *buffer2; 
		int offset;
		unsigned long long m_register; // as the test case is generalized off of a register equivalent and this is the register associated with the test case that needs to end up in memory
		unsigned long long imm_register; // as the test case is generalized off of a register equivalent and this is the register associated with the test case that needs to end up in memory

		
		//Create and open the Pintool Instrument file for the instruction
		std::stringstream tmp_pintool_filename;
		tmp_pintool_filename << "/root/tmp_m_imm_Pintool_Instrument_"<< template_prefix_arg.value() <<".s";
		ofstream tmp_pintool_file;		
		tmp_pintool_file.open(tmp_pintool_filename.str());	
		
		//Build  Assembly File
		m_register=get_testcase_register(start+lemma_i,3); // rbx is the register
		string s_m[8];
		string s_m_end[8];
		reg_to_m(m_register, s_m[7], s_m[6], s_m[5], s_m[4], s_m[3], s_m[2], s_m[1], s_m[0]);
		string mem_ptr;
		switch (t1) {
			default:
			case Type::M_64:
				mem_ptr = "qword ptr";
				break;
			case Type::M_32:
				mem_ptr = "dword ptr";
				break;
			case Type::M_16:
				mem_ptr = "word ptr";
				break;
			case Type::M_8:
				mem_ptr = "byte ptr";
				break;
		}

		imm_register=get_testcase_register(start+lemma_i,1);
		string s_op2=reg_to_imm(t2, imm_register);
		
		ifstream template_assembly;
		template_assembly.open("/root/TestLemmas/Templates/Template_Assembly_m_imm.s", std::ifstream::binary);
		buffer2 = new char[20000];
		raw_buffer = template_assembly.rdbuf(); 
		i=raw_buffer->sgetn(buffer2, 20000);
		buffer2[i]=0;			
		tmp_pintool_file << boost::format(buffer2) % instr % mem_ptr %
			s_op2 % add_hex_prefix(s_m[0]) % add_hex_prefix(s_m[1]) % add_hex_prefix(s_m[2]) % 
			add_hex_prefix(s_m[3]) % add_hex_prefix(s_m[4]) % add_hex_prefix(s_m[5]) % add_hex_prefix(s_m[6]) % 
			add_hex_prefix(s_m[7]);
		template_assembly.close();
		tmp_pintool_file.close();

		//compile pintool instrument
		std::stringstream s_tmp;
		s_tmp << "cd && gcc /root/tmp_m_imm_Pintool_Instrument_"<< template_prefix_arg.value() <<".s -o /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value();
		int j = std::system(s_tmp.str().c_str());
		j++;
		
		//get iopair from pintool instrument
		std::stringstream s_tmp3;
				s_tmp3 << "cd && ./runpin.sh " << (start+lemma_i) << " 1 2 /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value();
		int j2 = std::system(s_tmp3.str().c_str());
		j2++;
			
		f.open("/root/chum_test.out");
		f.getline(dst_start,50);
		f.getline(dst_end,50);
		f.getline(src_start,50);
		f.getline(src_end,50);
		f.getline(flag_in,500);
		f.getline(flag_out,500);
		f.getline(rax_start,50);
		f.getline(rax_end,50);
		f.getline(rdx_start,50);
		f.getline(rdx_end,50);
		f.getline(throwaway,300); //ymm0_start
		f.getline(throwaway,300); //ymm0_end
		f.getline(throwaway,300); //ymm1_start
		f.getline(throwaway,300); //ymm1_end
		f.getline(throwaway,300); //ymm2_start
		f.getline(throwaway,300); //ymm2_end
		f.getline(throwaway,300); //ymm3_start
		f.getline(throwaway,300); //ymm3_end
		f.getline(throwaway,300); //ymm4_start
		f.getline(throwaway,300); //ymm4_end
		
		bool mem_used=false;
		f >> mem_used;
		
		if (mem_used) {
			unsigned long long l;
			f >> hex >> l;
			reg_to_m(l, s_m_end[7], s_m_end[6], s_m_end[5], s_m_end[4], s_m_end[3], 
					s_m_end[2], s_m_end[1], s_m_end[0]);
		} else { 
			for (int count=0;count<8;count++) s_m_end[count]=s_m[count];
		}
		
		stringstream s_tmp4;
		stringstream s_tmp5;
		switch (t1) {
			default:
			case Type::M_64:
				s_tmp4 << "0x" << s_m[0] << s_m[1] << s_m[2] << s_m[3] << s_m[4] << s_m[5] << s_m[6] << s_m[7]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1] << s_m_end[2] << s_m_end[3] << s_m_end[4] << s_m_end[5] << s_m_end[6] << s_m_end[7]; 
				break;
			case Type::M_32:
				s_tmp4 << "0x" << s_m[0] << s_m[1] << s_m[2] << s_m[3]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1] << s_m_end[2] << s_m_end[3]; 
				break;
			case Type::M_16:
				s_tmp4 << "0x" << s_m[0] << s_m[1]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1]; 
				break;
			case Type::M_8:
				s_tmp4 << "0x" << s_m[0]; 
				s_tmp5 << "0x" << s_m_end[0]; 
				break;
		}


		
		cout << instr << " [mem=" << s_tmp4.str() <<"], " << s_op2 << endl;
		f.close();		
		if (flags==true) {
			iopairs << boost::format(buffer) % (start+lemma_i+1) % s_tmp4.str() % s_tmp5.str() % s_op2 % s_op2 % flag_in % flag_out % "" % ""  << std::flush;
		} else {
			iopairs << boost::format(buffer) % (start+lemma_i+1) % s_tmp4.str() % s_tmp5.str() % s_op2 % s_op2 % "" % "" % "" % ""  << std::flush;
		}			
		
	}
	template_file.close();
	delete buffer;
	return iopairs.str();

}

std::string get_iopairs_m(string instr, Type t1, int count, int start, bool flags)
{
	char *buffer; 
	int i,lemma_i;
	std::streambuf* raw_buffer; 
	ifstream template_file;
	std::stringstream iopairs;
	
	template_file.open("/root/TestLemmas/Templates/Template_IOPair.thy", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int k=raw_buffer->sgetn(buffer, 20000);
	buffer[k]=0;
	
	ifstream f;
		
	for(lemma_i=0;lemma_i<count;lemma_i++)
	{
		char dst_start[50],dst_end[50],src_start[50],src_end[50],flag_in[500],flag_out[500],rax_start[50],rax_end[50],rdx_start[50],rdx_end[50],memory_op[50], throwaway[300];
		char *buffer2; 
		int offset;
		unsigned long long m_register; // as the test case is generalized off of a register equivalent and this is the register associated with the test case that needs to end up in memory

		
		//Create and open the Pintool Instrument file for the instruction
		std::stringstream tmp_pintool_filename;
		tmp_pintool_filename << "/root/tmp_m_Pintool_Instrument_"<< template_prefix_arg.value() <<".s";
		ofstream tmp_pintool_file;		
		tmp_pintool_file.open(tmp_pintool_filename.str());	
		
		//Build  Assembly File
		m_register=get_testcase_register(start+lemma_i,3); // rbx is the register
		string s_m[8];
		string s_m_end[8];
		reg_to_m(m_register, s_m[7], s_m[6], s_m[5], s_m[4], s_m[3], s_m[2], s_m[1], s_m[0]);
		string mem_ptr;
		switch (t1) {
			default:
			case Type::M_64:
				mem_ptr = "qword ptr";
				break;
			case Type::M_32:
				mem_ptr = "dword ptr";
				break;
			case Type::M_16:
				mem_ptr = "word ptr";
				break;
			case Type::M_8:
				mem_ptr = "byte ptr";
				break;
		}
		
		ifstream template_assembly;
		template_assembly.open("/root/TestLemmas/Templates/Template_Assembly_m.s", std::ifstream::binary);
		buffer2 = new char[20000];
		raw_buffer = template_assembly.rdbuf(); 
		i=raw_buffer->sgetn(buffer2, 20000);
		buffer2[i]=0;			
		tmp_pintool_file << boost::format(buffer2) % instr % mem_ptr %
		    add_hex_prefix(s_m[0]) % add_hex_prefix(s_m[1]) % add_hex_prefix(s_m[2]) % 
			add_hex_prefix(s_m[3]) % add_hex_prefix(s_m[4]) % add_hex_prefix(s_m[5]) % add_hex_prefix(s_m[6]) % 
			add_hex_prefix(s_m[7]);
		template_assembly.close();
		tmp_pintool_file.close();

		//compile pintool instrument
		std::stringstream s_tmp;
		s_tmp << "cd && gcc /root/tmp_m_Pintool_Instrument_"<< template_prefix_arg.value() <<".s -o /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value();
		int j = std::system(s_tmp.str().c_str());
		j++;
		
		//get iopair from pintool instrument
		std::stringstream s_tmp3;
				s_tmp3 << "cd && ./runpin.sh " << (start+lemma_i) << " 1 2 /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value();
		int j2 = std::system(s_tmp3.str().c_str());
		j2++;
			
		f.open("/root/chum_test.out");
		f.getline(dst_start,50);
		f.getline(dst_end,50);
		f.getline(src_start,50);
		f.getline(src_end,50);
		f.getline(flag_in,500);
		f.getline(flag_out,500);
		f.getline(rax_start,50);
		f.getline(rax_end,50);
		f.getline(rdx_start,50);
		f.getline(rdx_end,50);
		f.getline(throwaway,300); //ymm0_start
		f.getline(throwaway,300); //ymm0_end
		f.getline(throwaway,300); //ymm1_start
		f.getline(throwaway,300); //ymm1_end
		f.getline(throwaway,300); //ymm2_start
		f.getline(throwaway,300); //ymm2_end
		f.getline(throwaway,300); //ymm3_start
		f.getline(throwaway,300); //ymm3_end
		f.getline(throwaway,300); //ymm4_start
		f.getline(throwaway,300); //ymm4_end
		bool mem_used=false;
		f >> mem_used;
		
		if (mem_used) {
			unsigned long long l;
			f >> hex >> l;
			reg_to_m(l, s_m_end[7], s_m_end[6], s_m_end[5], s_m_end[4], s_m_end[3], 
					s_m_end[2], s_m_end[1], s_m_end[0]);
		} else { 
			for (int count=0;count<8;count++) s_m_end[count]=s_m[count];
		}
		
		stringstream s_tmp4;
		stringstream s_tmp5;
		switch (t1) {
			default:
			case Type::M_64:
				s_tmp4 << "0x" << s_m[0] << s_m[1] << s_m[2] << s_m[3] << s_m[4] << s_m[5] << s_m[6] << s_m[7]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1] << s_m_end[2] << s_m_end[3] << s_m_end[4] << s_m_end[5] << s_m_end[6] << s_m_end[7]; 
				break;
			case Type::M_32:
				s_tmp4 << "0x" << s_m[0] << s_m[1] << s_m[2] << s_m[3]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1] << s_m_end[2] << s_m_end[3]; 
				break;
			case Type::M_16:
				s_tmp4 << "0x" << s_m[0] << s_m[1]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1]; 
				break;
			case Type::M_8:
				s_tmp4 << "0x" << s_m[0]; 
				s_tmp5 << "0x" << s_m_end[0]; 
				break;
		}


		
		cout << instr << " [mem=" << s_tmp4.str() <<"]" << endl;
		f.close();		
		if (flags==true) {
			iopairs << boost::format(buffer) % (start+lemma_i+1) % s_tmp4.str() % s_tmp5.str() % "0x0" % "0x0" % flag_in % flag_out % "" % ""  << std::flush;
		} else {
			iopairs << boost::format(buffer) % (start+lemma_i+1) % s_tmp4.str() % s_tmp5.str() % "0x0" % "0x0" % "" % "" % "" % "" << std::flush;
		}			
		
	}
	template_file.close();
	delete buffer;
	return iopairs.str();

}

std::string get_iopairs_simd_simd(int count, int start, std::string pin_instr, bool flags)
{
	char *buffer; 
	int i;
	std::streambuf* raw_buffer; 
	ifstream template_file;
	std::stringstream iopairs;
	
	template_file.open("/root/TestLemmas/Templates/Template_IOPair.thy", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int k=raw_buffer->sgetn(buffer, 20000);
	buffer[k]=0;
	
	ifstream f;
		
	for(i=0;i<count;i++)
	{
		char throwaway[300];
		char flag_in[500],flag_out[500], ymm1_start[300], ymm1_end[300], ymm2_start[300], ymm2_end[300];
		
		//get iopair from pintool instrument
		std::stringstream s_tmp;
				s_tmp << "cd && ./runpin.sh " << (start+i) << " 1 2 " <<  pin_instr ;
			int j = std::system(s_tmp.str().c_str());
			j++;
			
		f.open("/root/chum_test.out");
		f.getline(throwaway,300); //dst_start
		f.getline(throwaway,300); //dst_end
		f.getline(throwaway,300); //src_start
		f.getline(throwaway,300); //src_end
		f.getline(flag_in,500);
		f.getline(flag_out,500);
		f.getline(throwaway,300); //rax_start
		f.getline(throwaway,300); //rax_end
		f.getline(throwaway,300); //rdx_start
		f.getline(throwaway,300); //rdx_end
		f.getline(throwaway,300); //ymm0_start
		f.getline(throwaway,300); //ymm0_end
		f.getline(ymm1_start,300); 
		f.getline(ymm1_end,300); 
		f.getline(ymm2_start,300); 
		f.getline(ymm2_end,300); 

		cout << "dst_start=" << ymm1_start << endl;
		f.close();		
		if (flags==true) {
			iopairs << boost::format(buffer) % (start+i+1) % ymm1_start % ymm1_end % ymm2_start % ymm2_end % flag_in % flag_out % "" % "" << std::flush;
		} else {
			iopairs << boost::format(buffer) % (start+i+1) % ymm1_start % ymm1_end % ymm2_start % ymm2_end % "" % "" % "" % "" << std::flush;
		}			
	}
	template_file.close();
	delete buffer;
	return iopairs.str();

}

std::string get_iopairs_simd_m(string instr, Type t1, Type t2, int count, int start, bool flags)
{
	char *buffer; 
	int i,lemma_i;
	std::streambuf* raw_buffer; 
	ifstream template_file;
	std::stringstream iopairs;
	
	template_file.open("/root/TestLemmas/Templates/Template_IOPair.thy", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int k=raw_buffer->sgetn(buffer, 20000);
	buffer[k]=0;
	
	ifstream f;
		
	for(lemma_i=0;lemma_i<count;lemma_i++)
	{
		char dst_start[50],dst_end[50],src_start[50],src_end[50],flag_in[500],flag_out[500],rax_start[50],rax_end[50],rdx_start[50],rdx_end[50],memory_op[50],ymm1_start[300],ymm1_end[300],throwaway[300];
		char *buffer2; 
		unsigned long long simd_register[4]; // as the test case is generalized off of a register equivalent and this is the register associated with the test case that needs to end up in memory

		
		//Create and open the Pintool Instrument file for the instruction
		std::stringstream tmp_pintool_filename;
		tmp_pintool_filename << "/root/tmp_simd_m_Pintool_Instrument_"<< template_prefix_arg.value() <<".s";
		ofstream tmp_pintool_file;		
		tmp_pintool_file.open(tmp_pintool_filename.str());	
		
		//Build  Assembly File
		stringstream s_tmp2;
		string mem_ptr;
		switch (t2) {
			case Type::M_64:
				mem_ptr = "qword ptr";
				break;
			case Type::M_32:
				mem_ptr = "dword ptr";
				break;
			case Type::M_16:
				mem_ptr = "word ptr";
				break;
			case Type::M_8:
				mem_ptr = "byte ptr";
				break;
			default:
				mem_ptr="";
				break;
		}
		string s_m[32];
		string s_m_end[32];
		get_testcase_simd_register(start+lemma_i,2, &simd_register[0]);
		simdreg_to_m(&simd_register[0], s_m[31], s_m[30],
							 s_m[29], s_m[28], s_m[27], s_m[26], s_m[25], s_m[24], s_m[23], s_m[22], s_m[21], s_m[20], 
							 s_m[19], s_m[18], s_m[17], s_m[16], s_m[15], s_m[14], s_m[13], s_m[12], s_m[11], s_m[10], 
							 s_m[9], s_m[8], s_m[7], s_m[6], s_m[5], s_m[4], s_m[3], s_m[2], s_m[1], s_m[0]);

		if (t1 == Type::XMM) s_tmp2 << instr << " xmm1, " << mem_ptr << " ";
		else s_tmp2 << instr << " ymm1, " << mem_ptr << " ";
		
		ifstream template_assembly;
		template_assembly.open("/root/TestLemmas/Templates/Template_Assembly_simd_m.s", std::ifstream::binary);
		buffer2 = new char[20000];
		raw_buffer = template_assembly.rdbuf(); 
		i=raw_buffer->sgetn(buffer2, 20000);
		buffer2[i]=0;			
		tmp_pintool_file << boost::format(buffer2) % s_tmp2.str() 
			% add_hex_prefix(s_m[0]) % add_hex_prefix(s_m[1]) % add_hex_prefix(s_m[2]) % add_hex_prefix(s_m[3]) 
			% add_hex_prefix(s_m[4]) % add_hex_prefix(s_m[5]) % add_hex_prefix(s_m[6]) % add_hex_prefix(s_m[7])   
			% add_hex_prefix(s_m[8]) % add_hex_prefix(s_m[9]) % add_hex_prefix(s_m[10]) % add_hex_prefix(s_m[11])   
			% add_hex_prefix(s_m[12]) % add_hex_prefix(s_m[13]) % add_hex_prefix(s_m[14]) % add_hex_prefix(s_m[15])   
			% add_hex_prefix(s_m[16]) % add_hex_prefix(s_m[17]) % add_hex_prefix(s_m[18]) % add_hex_prefix(s_m[19])   
			% add_hex_prefix(s_m[20]) % add_hex_prefix(s_m[21]) % add_hex_prefix(s_m[22]) % add_hex_prefix(s_m[23])   
			% add_hex_prefix(s_m[24]) % add_hex_prefix(s_m[25]) % add_hex_prefix(s_m[26]) % add_hex_prefix(s_m[27])   
			% add_hex_prefix(s_m[28]) % add_hex_prefix(s_m[29]) % add_hex_prefix(s_m[30]) % add_hex_prefix(s_m[31]);
		delete buffer2;
		template_assembly.close();
		tmp_pintool_file.close();

		//compile pintool instrument
		std::stringstream s_tmp;
		s_tmp << "cd && gcc /root/tmp_simd_m_Pintool_Instrument_"<< template_prefix_arg.value() <<".s -o /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value() ;
		int j = std::system(s_tmp.str().c_str());
		j++;
		
		//get iopair from pintool instrument
		std::stringstream s_tmp3;
				s_tmp3 << "cd && ./runpin.sh " << (start+lemma_i) << " 1 2 /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value() ;
		int j2 = std::system(s_tmp3.str().c_str());
		j2++;
			
		f.open("/root/chum_test.out");
		f.getline(dst_start,50);
		f.getline(dst_end,50);
		f.getline(src_start,50);
		f.getline(src_end,50);
		f.getline(flag_in,500);
		f.getline(flag_out,500);
		f.getline(rax_start,50);
		f.getline(rax_end,50);
		f.getline(rdx_start,50);
		f.getline(rdx_end,50);
		f.getline(throwaway,300); //ymm0_start
		f.getline(throwaway,300); //ymm0_end
		f.getline(ymm1_start,300); //ymm1_start
		f.getline(ymm1_end,300); //ymm1_end
		f.getline(throwaway,300); //ymm2_start
		f.getline(throwaway,300); //ymm2_end
		f.getline(throwaway,300); //ymm3_start
		f.getline(throwaway,300); //ymm3_end
		f.getline(throwaway,300); //ymm4_start
		f.getline(throwaway,300); //ymm4_end
		bool mem_used=false;
		f >> mem_used;
		if (mem_used) {
			unsigned long long l[4];
			f >> hex >> l[3] >> l[2] >> l[1] >> l[0];
			simdreg_to_m(&l[0], s_m_end[31], s_m_end[30],
							 s_m_end[29], s_m_end[28], s_m_end[27], s_m_end[26], s_m_end[25], s_m_end[24], s_m_end[23], s_m_end[22], s_m_end[21], s_m_end[20], 
							 s_m_end[19], s_m_end[18], s_m_end[17], s_m_end[16], s_m_end[15], s_m_end[14], s_m_end[13], s_m_end[12], s_m_end[11], s_m_end[10], 
							 s_m_end[9], s_m_end[8], s_m_end[7], s_m_end[6], s_m_end[5], s_m_end[4], s_m_end[3], s_m_end[2], s_m_end[1], s_m_end[0]);
		} else { 
			for (int count=0;count<32;count++) s_m_end[count]=s_m[count];
		}
		
		stringstream s_tmp4;
		stringstream s_tmp5;
		switch (t2) {
			default:
			case Type::M_256:
				s_tmp4 << "0x" 	<< s_m[0]  << s_m[1]  << s_m[2] << s_m[3] << s_m[4] << s_m[5] << s_m[6] << s_m[7] << s_m[8] << s_m[9] 
								<< s_m[10] << s_m[11] << s_m[12] << s_m[13] << s_m[14] << s_m[15] << s_m[16] << s_m[17] << s_m[18] << s_m[19]
								<< s_m[20] << s_m[21] << s_m[22] << s_m[23] << s_m[24] << s_m[25] << s_m[26] << s_m[27] << s_m[28] << s_m[29]
								<< s_m[30] << s_m[31]; 
				s_tmp5 << "0x"  << s_m_end[0]  << s_m_end[1]  << s_m_end[2]  << s_m_end[3]  << s_m_end[4]  << s_m_end[5]  << s_m_end[6] 
								<< s_m_end[7]  << s_m_end[8]  << s_m_end[9]  << s_m_end[10] << s_m_end[11] << s_m_end[12] << s_m_end[13] 
								<< s_m_end[14] << s_m_end[15] << s_m_end[16] << s_m_end[17] << s_m_end[18] << s_m_end[19] << s_m_end[20] 
								<< s_m_end[21] << s_m_end[22] << s_m_end[23] << s_m_end[24] << s_m_end[25] << s_m_end[26] << s_m_end[27] 
								<< s_m_end[28] << s_m_end[29] << s_m_end[30] << s_m_end[31]; 
				break;
			case Type::M_128:
				s_tmp4 << "0x" << s_m[0] << s_m[1] << s_m[2] << s_m[3] << s_m[4] << s_m[5] << s_m[6] << s_m[7] << s_m[8] << s_m[9] 
								<< s_m[10] << s_m[11] << s_m[12] << s_m[13] << s_m[14] << s_m[15]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1] << s_m_end[2] << s_m_end[3] << s_m_end[4] << s_m_end[5] << s_m_end[6] << s_m_end[7] << s_m_end[8] << s_m_end[9]
								<< s_m_end[10] << s_m_end[11] << s_m_end[12] << s_m_end[13] << s_m_end[14] << s_m_end[15]; 
				break;
			case Type::M_64:
				s_tmp4 << "0x" << s_m[0] << s_m[1] << s_m[2] << s_m[3] << s_m[4] << s_m[5] << s_m[6] << s_m[7]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1] << s_m_end[2] << s_m_end[3] << s_m_end[4] << s_m_end[5] << s_m_end[6] << s_m_end[7]; 
				break;
			case Type::M_32:
				s_tmp4 << "0x" << s_m[0] << s_m[1] << s_m[2] << s_m[3]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1] << s_m_end[2] << s_m_end[3]; 
				break;
			case Type::M_16:
				s_tmp4 << "0x" << s_m[0] << s_m[1]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1]; 
				break;
			case Type::M_8:
				s_tmp4 << "0x" << s_m[0]; 
				s_tmp5 << "0x" << s_m_end[0]; 
				break;
		}

		cout << s_tmp2.str() << " [mem=" << s_tmp4.str() <<"->" <<  s_tmp5.str() <<"]" << endl;
		f.close();		
		if (flags==true) {
			iopairs << boost::format(buffer) % (start+lemma_i+1) % ymm1_start % ymm1_end % s_tmp4.str() % s_tmp5.str() % flag_in % flag_out % "" % "" << std::flush;
		} else {
			iopairs << boost::format(buffer) % (start+lemma_i+1) % ymm1_start % ymm1_end % s_tmp4.str() % s_tmp5.str() % "" % "" % "" % "" << std::flush;
			
		}			
	}
	template_file.close();
	delete buffer;
	return iopairs.str();
}

std::string get_iopairs_m_simd(string instr, Type t1, Type t2, int count, int start, bool flags)
{
	char *buffer; 
	int i,lemma_i;
	std::streambuf* raw_buffer; 
	ifstream template_file;
	std::stringstream iopairs;
	
	template_file.open("/root/TestLemmas/Templates/Template_IOPair.thy", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int k=raw_buffer->sgetn(buffer, 20000);
	buffer[k]=0;
	
	ifstream f;
		
	for(lemma_i=0;lemma_i<count;lemma_i++)
	{
		char dst_start[50],dst_end[50],src_start[50],src_end[50],flag_in[500],flag_out[500],rax_start[50],rax_end[50],rdx_start[50],rdx_end[50],memory_op[50],throwaway[300], ymm2_start[300], ymm2_end[300];
		char *buffer2; 
		unsigned long long simd_register[4]; // as the test case is generalized off of a register equivalent and this is the register associated with the test case that needs to end up in memory

		
		//Create and open the Pintool Instrument file for the instruction
		std::stringstream tmp_pintool_filename;
		tmp_pintool_filename << "/root/tmp_m_simd_Pintool_Instrument_"<< template_prefix_arg.value() <<".s";
		ofstream tmp_pintool_file;		
		tmp_pintool_file.open(tmp_pintool_filename.str());	
		
		//Build  Assembly File
		stringstream s_tmp2;
		string mem_ptr;
		switch (t1) {
			case Type::M_64:
				mem_ptr = "qword ptr";
				break;
			case Type::M_32:
				mem_ptr = "dword ptr";
				break;
			case Type::M_16:
				mem_ptr = "word ptr";
				break;
			case Type::M_8:
				mem_ptr = "byte ptr";
				break;
			default:
				mem_ptr="";
				break;
		}
		string s_m[32];
		string s_m_end[32];
		get_testcase_simd_register(start+lemma_i,1, &simd_register[0]);
		simdreg_to_m(&simd_register[0], s_m[31], s_m[30],
							 s_m[29], s_m[28], s_m[27], s_m[26], s_m[25], s_m[24], s_m[23], s_m[22], s_m[21], s_m[20], 
							 s_m[19], s_m[18], s_m[17], s_m[16], s_m[15], s_m[14], s_m[13], s_m[12], s_m[11], s_m[10], 
							 s_m[9], s_m[8], s_m[7], s_m[6], s_m[5], s_m[4], s_m[3], s_m[2], s_m[1], s_m[0]);		
		string s_op2;
		if (t2 == Type::XMM) s_op2 = " xmm2"; 
		else s_op2 = " ymm2";

		ifstream template_assembly;
		template_assembly.open("/root/TestLemmas/Templates/Template_Assembly_m_simd.s", std::ifstream::binary);
		buffer2 = new char[20000];
		raw_buffer = template_assembly.rdbuf(); 
		i=raw_buffer->sgetn(buffer2, 20000);
		buffer2[i]=0;			
		tmp_pintool_file << boost::format(buffer2) % instr % mem_ptr % s_op2 
			% add_hex_prefix(s_m[0]) % add_hex_prefix(s_m[1]) % add_hex_prefix(s_m[2]) % add_hex_prefix(s_m[3]) 
			% add_hex_prefix(s_m[4]) % add_hex_prefix(s_m[5]) % add_hex_prefix(s_m[6]) % add_hex_prefix(s_m[7])   
			% add_hex_prefix(s_m[8]) % add_hex_prefix(s_m[9]) % add_hex_prefix(s_m[10]) % add_hex_prefix(s_m[11])   
			% add_hex_prefix(s_m[12]) % add_hex_prefix(s_m[13]) % add_hex_prefix(s_m[14]) % add_hex_prefix(s_m[15])   
			% add_hex_prefix(s_m[16]) % add_hex_prefix(s_m[17]) % add_hex_prefix(s_m[18]) % add_hex_prefix(s_m[19])   
			% add_hex_prefix(s_m[20]) % add_hex_prefix(s_m[21]) % add_hex_prefix(s_m[22]) % add_hex_prefix(s_m[23])   
			% add_hex_prefix(s_m[24]) % add_hex_prefix(s_m[25]) % add_hex_prefix(s_m[26]) % add_hex_prefix(s_m[27])   
			% add_hex_prefix(s_m[28]) % add_hex_prefix(s_m[29]) % add_hex_prefix(s_m[30]) % add_hex_prefix(s_m[31]);
		delete buffer2;
		template_assembly.close();
		tmp_pintool_file.close();
	
		//compile pintool instrument
		std::stringstream s_tmp;
		s_tmp << "cd && gcc /root/tmp_m_simd_Pintool_Instrument_"<< template_prefix_arg.value() <<".s -o /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value();
		int j = std::system(s_tmp.str().c_str());
		j++;
		
		//get iopair from pintool instrument
		std::stringstream s_tmp3;
				s_tmp3 << "cd && ./runpin.sh " << (start+lemma_i) << " 1 2 /root/tmp_Pintool_Instrument_"<< template_prefix_arg.value();
		int j2 = std::system(s_tmp3.str().c_str());
		j2++;
			
		f.open("/root/chum_test.out");
		f.getline(dst_start,50);
		f.getline(dst_end,50);
		f.getline(src_start,50);
		f.getline(src_end,50);
		f.getline(flag_in,500);
		f.getline(flag_out,500);
		f.getline(rax_start,50);
		f.getline(rax_end,50);
		f.getline(rdx_start,50);
		f.getline(rdx_end,50);
		f.getline(throwaway,300); //ymm0_start
		f.getline(throwaway,300); //ymm0_end
		f.getline(throwaway,300); //ymm1_start
		f.getline(throwaway,300); //ymm1_end
		f.getline(ymm2_start,300); //ymm2_start
		f.getline(ymm2_end,300); //ymm2_end
		f.getline(throwaway,300); //ymm3_start
		f.getline(throwaway,300); //ymm3_end
		f.getline(throwaway,300); //ymm4_start
		f.getline(throwaway,300); //ymm4_end
		bool mem_used=false;
		f >> mem_used;
		if (mem_used) {
			unsigned long long l[4];
			f >> hex >> l[3] >> l[2] >> l[1] >> l[0];
			simdreg_to_m(&l[0], s_m_end[31], s_m_end[30],
							 s_m_end[29], s_m_end[28], s_m_end[27], s_m_end[26], s_m_end[25], s_m_end[24], s_m_end[23], s_m_end[22], s_m_end[21], s_m_end[20], 
							 s_m_end[19], s_m_end[18], s_m_end[17], s_m_end[16], s_m_end[15], s_m_end[14], s_m_end[13], s_m_end[12], s_m_end[11], s_m_end[10], 
							 s_m_end[9], s_m_end[8], s_m_end[7], s_m_end[6], s_m_end[5], s_m_end[4], s_m_end[3], s_m_end[2], s_m_end[1], s_m_end[0]);
		} else { 
			for (int count=0;count<32;count++) s_m_end[count]=s_m[count];
		}
		stringstream s_tmp4;
		stringstream s_tmp5;
		switch (t1) {
			default:
			case Type::M_256:
				s_tmp4 << "0x" 	<< s_m[0]  << s_m[1]  << s_m[2] << s_m[3] << s_m[4] << s_m[5] << s_m[6] << s_m[7] << s_m[8] << s_m[9] 
								<< s_m[10] << s_m[11] << s_m[12] << s_m[13] << s_m[14] << s_m[15] << s_m[16] << s_m[17] << s_m[18] << s_m[19]
								<< s_m[20] << s_m[21] << s_m[22] << s_m[23] << s_m[24] << s_m[25] << s_m[26] << s_m[27] << s_m[28] << s_m[29]
								<< s_m[30] << s_m[31]; 
				s_tmp5 << "0x"  << s_m_end[0]  << s_m_end[1]  << s_m_end[2]  << s_m_end[3]  << s_m_end[4]  << s_m_end[5]  << s_m_end[6] 
								<< s_m_end[7]  << s_m_end[8]  << s_m_end[9]  << s_m_end[10] << s_m_end[11] << s_m_end[12] << s_m_end[13] 
								<< s_m_end[14] << s_m_end[15] << s_m_end[16] << s_m_end[17] << s_m_end[18] << s_m_end[19] << s_m_end[20] 
								<< s_m_end[21] << s_m_end[22] << s_m_end[23] << s_m_end[24] << s_m_end[25] << s_m_end[26] << s_m_end[27] 
								<< s_m_end[28] << s_m_end[29] << s_m_end[30] << s_m_end[31]; 
				break;
			case Type::M_128:
				s_tmp4 << "0x" << s_m[0] << s_m[1] << s_m[2] << s_m[3] << s_m[4] << s_m[5] << s_m[6] << s_m[7] << s_m[8] << s_m[9] 
								<< s_m[10] << s_m[11] << s_m[12] << s_m[13] << s_m[14] << s_m[15]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1] << s_m_end[2] << s_m_end[3] << s_m_end[4] << s_m_end[5] << s_m_end[6] << s_m_end[7] << s_m_end[8] << s_m_end[9]
								<< s_m_end[10] << s_m_end[11] << s_m_end[12] << s_m_end[13] << s_m_end[14] << s_m_end[15]; 
				break;
			case Type::M_64:
				s_tmp4 << "0x" << s_m[0] << s_m[1] << s_m[2] << s_m[3] << s_m[4] << s_m[5] << s_m[6] << s_m[7]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1] << s_m_end[2] << s_m_end[3] << s_m_end[4] << s_m_end[5] << s_m_end[6] << s_m_end[7]; 
				break;
			case Type::M_32:
				s_tmp4 << "0x" << s_m[0] << s_m[1] << s_m[2] << s_m[3]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1] << s_m_end[2] << s_m_end[3]; 
				break;
			case Type::M_16:
				s_tmp4 << "0x" << s_m[0] << s_m[1]; 
				s_tmp5 << "0x" << s_m_end[0] << s_m_end[1]; 
				break;
			case Type::M_8:
				s_tmp4 << "0x" << s_m[0]; 
				s_tmp5 << "0x" << s_m_end[0]; 
				break;
		}
		
		cout << instr << " [mem=" << s_tmp4.str() <<"]," << s_op2 << endl;
		f.close();		
		if (flags==true) {
			iopairs << boost::format(buffer) % (start+lemma_i+1) % s_tmp4.str() % s_tmp5.str() % ymm2_start % ymm2_end % flag_in % flag_out % "" % "" << std::flush;
		} else {
			iopairs << boost::format(buffer) % (start+lemma_i+1) % s_tmp4.str() % s_tmp5.str() % ymm2_start % ymm2_end % "" % "" % "" % "" << std::flush;
		}			
	}
	template_file.close();
	delete buffer;
	return iopairs.str();

}

std::string get_iopairs_simd_r(int count, int start, std::string pin_instr, bool flags)
{
	char *buffer; 
	int i;
	std::streambuf* raw_buffer; 
	ifstream template_file;
	std::stringstream iopairs;
	
	template_file.open("/root/TestLemmas/Templates/Template_IOPair.thy", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int k=raw_buffer->sgetn(buffer, 20000);
	buffer[k]=0;
	
	ifstream f;
		
	for(i=0;i<count;i++)
	{
		char throwaway[300];
		char flag_in[500],flag_out[500], ymm1_start[300], ymm1_end[300], src_start[300], src_end[300];
		
		//get iopair from pintool instrument
		std::stringstream s_tmp;
				s_tmp << "cd && ./runpin.sh " << (start+i) << " 1 2 " <<  pin_instr ;
			int j = std::system(s_tmp.str().c_str());
			j++;
			
		f.open("/root/chum_test.out");
		f.getline(throwaway,300); //dst_start
		f.getline(throwaway,300); //dst_end
		f.getline(src_start,300); //src_start
		f.getline(src_end,300); //src_end
		f.getline(flag_in,500);
		f.getline(flag_out,500);
		f.getline(throwaway,300); //rax_start
		f.getline(throwaway,300); //rax_end
		f.getline(throwaway,300); //rdx_start
		f.getline(throwaway,300); //rdx_end
		f.getline(throwaway,300); //ymm0_start
		f.getline(throwaway,300); //ymm0_end
		f.getline(ymm1_start,300); 
		f.getline(ymm1_end,300); 
		f.getline(throwaway,300); 
		f.getline(throwaway,300); 

		cout << "dst_start=" << ymm1_start << endl;
		f.close();		
		if (flags==true) {
			iopairs << boost::format(buffer) % (start+i+1) % ymm1_start % ymm1_end % src_start % src_end % flag_in % flag_out % "" % "" << std::flush;
		} else {
			iopairs << boost::format(buffer) % (start+i+1) % ymm1_start % ymm1_end % src_start % src_end % "" % "" % "" % "" << std::flush;
		}			
	}
	template_file.close();
	delete buffer;
	return iopairs.str();

}

std::string get_iopairs_r_simd(int count, int start, std::string pin_instr, bool flags)
{
	char *buffer; 
	int i;
	std::streambuf* raw_buffer; 
	ifstream template_file;
	std::stringstream iopairs;
	
	template_file.open("/root/TestLemmas/Templates/Template_IOPair.thy", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int k=raw_buffer->sgetn(buffer, 20000);
	buffer[k]=0;
	
	ifstream f;
		
	for(i=0;i<count;i++)
	{
		char throwaway[300];
		char flag_in[500],flag_out[500], dst_start[300], dst_end[300], ymm2_start[300], ymm2_end[300];
		
		//get iopair from pintool instrument
		std::stringstream s_tmp;
				s_tmp << "cd && ./runpin.sh " << (start+i) << " 1 2 " <<  pin_instr ;
			int j = std::system(s_tmp.str().c_str());
			j++;
			
		f.open("/root/chum_test.out");
		f.getline(dst_start,300); //dst_start
		f.getline(dst_end,300); //dst_end
		f.getline(throwaway,300); //src_start
		f.getline(throwaway,300); //src_end
		f.getline(flag_in,500);
		f.getline(flag_out,500);
		f.getline(throwaway,300); //rax_start
		f.getline(throwaway,300); //rax_end
		f.getline(throwaway,300); //rdx_start
		f.getline(throwaway,300); //rdx_end
		f.getline(throwaway,300); //ymm0_start
		f.getline(throwaway,300); //ymm0_end
		f.getline(throwaway,300); 
		f.getline(throwaway,300); 
		f.getline(ymm2_start,300); 
		f.getline(ymm2_end,300); 

		cout << "dst_start=" << dst_start << endl;
		f.close();		
		if (flags==true) {
			iopairs << boost::format(buffer) % (start+i+1) % dst_start % dst_end % ymm2_start % ymm2_end % flag_in % flag_out % "" % "" << std::flush;
		} else {
			iopairs << boost::format(buffer) % (start+i+1) % dst_start % dst_end % ymm2_start % ymm2_end % "" % "" % "" % "" << std::flush;
		}			
	}
	template_file.close();
	delete buffer;
	return iopairs.str();

}

bool contains_unterpreted_funcs(string s)
{
	if (s.compare("addpd") == 0) return true; //uninterpreted functions
	if (s.compare("addps") == 0) return true; //uninterpreted functions
	if (s.compare("addsd") == 0) return true; //uninterpreted functions
	if (s.compare("addss") == 0) return true; //uninterpreted functions
	if (s.compare("addsubpd") == 0) return true; //uninterpreted functions
	if (s.compare("addsubps") == 0) return true; //uninterpreted functions
	if (s.compare("cvtdq2pd") == 0) return true; //uninterpreted functions
	if (s.compare("cvtdq2ps") == 0) return true; //uninterpreted functions
	if (s.compare("cvtpd2dq") == 0) return true; //uninterpreted functions
	if (s.compare("cvtpd2ps") == 0) return true; //uninterpreted functions
	if (s.compare("cvtps2dq") == 0) return true; //uninterpreted functions
	if (s.compare("cvtps2pd") == 0) return true; //uninterpreted functions
	if (s.compare("cvtsd2si") == 0) return true; //uninterpreted functions
	if (s.compare("cvtsd2ss") == 0) return true; //uninterpreted functions
	if (s.compare("cvtsi2sd") == 0) return true; //uninterpreted functions
	if (s.compare("cvtsi2ss") == 0) return true; //uninterpreted functions
	if (s.compare("cvtss2sd") == 0) return true; //uninterpreted functions
	if (s.compare("cvtss2si") == 0) return true; //uninterpreted functions
	if (s.compare("cvttpd2dq") == 0) return true; //uninterpreted functions
	if (s.compare("cvttps2dq") == 0) return true; //uninterpreted functions
	if (s.compare("cvttsd2si") == 0) return true; //uninterpreted functions
	if (s.compare("cvttss2si") == 0) return true; //uninterpreted functions
	if (s.compare("divpd") == 0) return true; //uninterpreted functions
	if (s.compare("divps") == 0) return true; //uninterpreted functions
	if (s.compare("divsd") == 0) return true; //uninterpreted functions
	if (s.compare("divss") == 0) return true; //uninterpreted functions
	if (s.compare("haddpd") == 0) return true; //uninterpreted functions
	if (s.compare("haddps") == 0) return true; //uninterpreted functions
	if (s.compare("hsubpd") == 0) return true; //uninterpreted functions
	if (s.compare("hsubps") == 0) return true; //uninterpreted functions
	if (s.compare("maxpd") == 0) return true; //uninterpreted functions
	if (s.compare("maxps") == 0) return true; //uninterpreted functions
	if (s.compare("maxsd") == 0) return true; //uninterpreted functions
	if (s.compare("maxss") == 0) return true; //uninterpreted functions
	if (s.compare("minpd") == 0) return true; //uninterpreted functions
	if (s.compare("minps") == 0) return true; //uninterpreted functions
	if (s.compare("minsd") == 0) return true; //uninterpreted functions
	if (s.compare("minss") == 0) return true; //uninterpreted functions
	if (s.compare("mulpd") == 0) return true; //uninterpreted functions
	if (s.compare("mulps") == 0) return true; //uninterpreted functions
	if (s.compare("mulsd") == 0) return true; //uninterpreted functions
	if (s.compare("mulss") == 0) return true; //uninterpreted functions
	if (s.compare("rcpps") == 0) return true; //uninterpreted functions
	if (s.compare("rcpss") == 0) return true; //uninterpreted functions
	if (s.compare("rsqrtps") == 0) return true; //uninterpreted functions
	if (s.compare("rsqrtss") == 0) return true; //uninterpreted functions
	if (s.compare("sqrtpd") == 0) return true; //uninterpreted functions
	if (s.compare("sqrtps") == 0) return true; //uninterpreted functions
	if (s.compare("sqrtsd") == 0) return true; //uninterpreted functions
	if (s.compare("sqrtss") == 0) return true; //uninterpreted functions
	if (s.compare("subpd") == 0) return true; //uninterpreted functions
	if (s.compare("subps") == 0) return true; //uninterpreted functions
	if (s.compare("subsd") == 0) return true; //uninterpreted functions
	if (s.compare("subss") == 0) return true; //uninterpreted functions
	if (s.compare("vaddpd") == 0) return true; //uninterpreted functions
	if (s.compare("vaddps") == 0) return true; //uninterpreted functions
	if (s.compare("vaddsd") == 0) return true; //uninterpreted functions
	if (s.compare("vaddss") == 0) return true; //uninterpreted functions
	if (s.compare("vaddsubpd") == 0) return true; //uninterpreted functions
	if (s.compare("vaddsubps") == 0) return true; //uninterpreted functions
	if (s.compare("vcvtdq2pd") == 0) return true; //uninterpreted functions
	if (s.compare("vcvtdq2ps") == 0) return true; //uninterpreted functions
	if (s.compare("vcvtpd2dq") == 0) return true; //uninterpreted functions
	if (s.compare("vcvtpd2ps") == 0) return true; //uninterpreted functions
	if (s.compare("vcvtps2dq") == 0) return true; //uninterpreted functions
	if (s.compare("vcvtps2pd") == 0) return true; //uninterpreted functions
	if (s.compare("vcvtsd2si") == 0) return true; //uninterpreted functions
	if (s.compare("vcvtsd2ss") == 0) return true; //uninterpreted functions
	if (s.compare("vcvtsi2sd") == 0) return true; //uninterpreted functions
	if (s.compare("vcvtsi2ss") == 0) return true; //uninterpreted functions
	if (s.compare("vcvtss2sd") == 0) return true; //uninterpreted functions
	if (s.compare("vcvtss2si") == 0) return true; //uninterpreted functions
	if (s.compare("vcvttpd2dq") == 0) return true; //uninterpreted functions
	if (s.compare("vcvttps2dq") == 0) return true; //uninterpreted functions
	if (s.compare("vcvttsd2si") == 0) return true; //uninterpreted functions
	if (s.compare("vcvttss2si") == 0) return true; //uninterpreted functions
	if (s.compare("vdivpd") == 0) return true; //uninterpreted functions
	if (s.compare("vdivps") == 0) return true; //uninterpreted functions
	if (s.compare("vdivsd") == 0) return true; //uninterpreted functions
	if (s.compare("vdivss") == 0) return true; //uninterpreted functions
	if (s.compare("vfmadd132pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmadd132ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfmadd132sd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmadd132ss") == 0) return true; //uninterpreted functions
	if (s.compare("vfmadd213pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmadd213ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfmadd213sd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmadd213ss") == 0) return true; //uninterpreted functions
	if (s.compare("vfmadd231pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmadd231ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfmadd231sd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmadd231ss") == 0) return true; //uninterpreted functions
	if (s.compare("vfmaddsub132pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmaddsub132ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfmaddsub213pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmaddsub213ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfmaddsub231pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmaddsub231ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsub132pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsub132ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsub132sd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsub132ss") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsub213pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsub213ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsub213sd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsub213ss") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsub231pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsub231ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsub231sd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsub231ss") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsubadd132pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsubadd132ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsubadd213pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsubadd213ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsubadd231pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfmsubadd231ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmadd132pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmadd132ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmadd132sd") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmadd132ss") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmadd213pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmadd213ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmadd213sd") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmadd213ss") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmadd231pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmadd231ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmadd231sd") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmadd231ss") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmsub132pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmsub132ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmsub132sd") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmsub132ss") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmsub213pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmsub213ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmsub213sd") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmsub213ss") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmsub231pd") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmsub231ps") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmsub231sd") == 0) return true; //uninterpreted functions
	if (s.compare("vfnmsub231ss") == 0) return true; //uninterpreted functions
	if (s.compare("vhaddpd") == 0) return true; //uninterpreted functions
	if (s.compare("vhaddps") == 0) return true; //uninterpreted functions
	if (s.compare("vhsubpd") == 0) return true; //uninterpreted functions
	if (s.compare("vhsubps") == 0) return true; //uninterpreted functions
	if (s.compare("vmaxpd") == 0) return true; //uninterpreted functions
	if (s.compare("vmaxps") == 0) return true; //uninterpreted functions
	if (s.compare("vmaxsd") == 0) return true; //uninterpreted functions
	if (s.compare("vmaxss") == 0) return true; //uninterpreted functions
	if (s.compare("vminpd") == 0) return true; //uninterpreted functions
	if (s.compare("vminps") == 0) return true; //uninterpreted functions
	if (s.compare("vminsd") == 0) return true; //uninterpreted functions
	if (s.compare("vminss") == 0) return true; //uninterpreted functions
	if (s.compare("vmulpd") == 0) return true; //uninterpreted functions
	if (s.compare("vmulps") == 0) return true; //uninterpreted functions
	if (s.compare("vmulsd") == 0) return true; //uninterpreted functions
	if (s.compare("vmulss") == 0) return true; //uninterpreted functions
	if (s.compare("vrcpps") == 0) return true; //uninterpreted functions
	if (s.compare("vrcpss") == 0) return true; //uninterpreted functions
	if (s.compare("vrsqrtps") == 0) return true; //uninterpreted functions
	if (s.compare("vrsqrtss") == 0) return true; //uninterpreted functions
	if (s.compare("vsqrtpd") == 0) return true; //uninterpreted functions
	if (s.compare("vsqrtps") == 0) return true; //uninterpreted functions
	if (s.compare("vsqrtsd") == 0) return true; //uninterpreted functions
	if (s.compare("vsqrtss") == 0) return true; //uninterpreted functions
	if (s.compare("vsubpd") == 0) return true; //uninterpreted functions
	if (s.compare("vsubps") == 0) return true; //uninterpreted functions
	if (s.compare("vsubsd") == 0) return true; //uninterpreted functions
	if (s.compare("vsubss") == 0) return true; //uninterpreted functions
	if (s.compare("sar") == 0) return true; //MP_BOOL
	if (s.compare("shr") == 0) return true;//MP_BOOL
	if (s.compare("shl") == 0) return true;//MP_BOOL
	if (s.compare("sal") == 0) return true;//MP_BOOL		  
return false;
}
void add_batch(stringstream& s, string instr, int variant_count)
{
	stringstream delay;
		delay << "";

		s  	<< "echo \""
				<< " isabelle build -j13 -v -b -d \\\"/root/reassembly_verification/isabelle\\\" -o threads=13 reassembly_"
					<< instr <<  template_prefix_arg.value() 
				<< " 2>&1 > " 
					<< "~/logs/" << instr <<  template_prefix_arg.value() << ".log" 
		<< "\" | batch " << delay.str() << endl;

}



void create_instruction_dir(string dirname)
{
	string dir_path = "/root/TestLemmas/Output/" + dirname;

	boost::filesystem::path dir(dir_path);
	boost::filesystem::create_directory(dir);
}
int main(int argc, char** argv) {
  char *buffer; 
  string fam; // family
  string s; //instruction
  string instr_upper; //instruction capitalized
  StrataHandler sh(strata_path_arg.value());
  ComboHandler oh(strata_path_arg.value());
  target_arg.required(false);  
  CommandLineConfig::strict_with_convenience(argc,argv);
  int famcount=0;
int vcount=0; //used to add waits into server script
	
  std::istringstream ( lemma_count_arg.value() ) >> lemma_count;
  std::istringstream ( lemma_start_arg.value() ) >> lemma_start;
  set_filename << "TestLemmas" << template_prefix_arg.value();		  
  inFile.open("chum_test.in2"); //test case data from strata
	
  create_instruction_dir(set_filename.str());
		
  std::stringstream list_of_instr_fams;  
  std::stringstream list_of_instr_fams_makefile;  
  std::stringstream instruction_variant_sessions;
  std::stringstream instruction_variant_build_heap;
  
  
  for (auto ifam=leviathan_x86_family_table.begin(); ifam!=leviathan_x86_family_table.end();++ifam) { //for each instruction mnemonic
	int instrcount=0;
	fam = ifam-> first;
	bool fam_used=false;
    std::stringstream list_of_instrs;	
	std::stringstream makefile_instr_lines;		

	for(std::vector<int>::size_type i_nem = 0; i_nem != ifam->second.size(); i_nem++) {
	  int variantcount=0;
	  bool instr_used=false;
	  s = ifam->second[i_nem];
	  std::stringstream list_of_variants;		
	  std::stringstream makefile_variant_lines;		
	  instr_upper = s;
	  instr_upper[0] = toupper(instr_upper[0]);

	  
	  if (contains_unterpreted_funcs(s)) continue; //uninterpreted functions
	  if (s.compare("blsi") == 0) continue;//slow
	  if (s.compare("tzcnt") == 0) continue;//slow
	  if (s.compare("bt") == 0) continue; //slow
	  

	  
      for (Entry e : leviathan_table[s]) {  //For each Instruction Variant of a given nmenonic
		int ge=0;int gs=0;
		Opcode o = e.second.first;
		if(e.second.first==VZEROALL) continue;   	
		if(e.second.first==MOVSD_XMM_M64) continue;  	// fails generalization argument
		if(e.second.first==MOVSD_M64_XMM) continue;  	// fails generalization argument
		if(e.second.first==MOVSS_XMM_M32) continue;  	// fails generalization argument
		if(e.second.first==MOVSS_M32_XMM) continue; 	// fails generalization argument
		if(e.second.second.size()>1) if(e.second.second[1] == Type::IMM_32) continue; // gcc compilataion issue, possibly gcc bug
		if(e.second.second.size()>1) if(e.second.second[1] == Type::IMM_64) continue;//  gcc compilataion issue, possibly gcc bug

		//unsupported by Strata 
		if (sh.support_reason(e.second.first) == SupportReason::NONE && !specgen_is_base(e.second.first)) {
			continue;
		}
		
		//temp
		
		
		//support nullary, unary, and binary
		//if (e.second.second.size()!=0 && e.second.second.size()!=1 &&  e.second.second.size()!=2 ) continue; 	
		
		//End temp
		
		
		if(e.second.second.size()!=2 && e.second.second.size()!=1) continue; 	
		if(get_template(e) !=  TestTemplate::tt_r_r && get_template(e) !=  TestTemplate::tt_r) continue;
		
		instr_used=true;fam_used=true;
		
		//create dirs
		std::stringstream fam_filename;
		std::stringstream instr_filename;
		fam_filename << set_filename.str() << "/" << fam;
		instr_filename << fam_filename.str() << "/" << instr_upper;
		create_instruction_dir(fam_filename.str());
		create_instruction_dir(instr_filename.str());
	
		//Create and open the theory file for the instruction variant
		std::stringstream instruction_variant_theory_filename;
		if(e.second.second.size()==0) instruction_variant_theory_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_nullary" << template_prefix_arg.value() << ".thy";
		if(e.second.second.size()==1) instruction_variant_theory_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << template_prefix_arg.value() << ".thy";
		if(e.second.second.size()==2) instruction_variant_theory_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_" << e.first[1] << template_prefix_arg.value() << ".thy";
		ofstream instruction_variant_theory_file;		
		instruction_variant_theory_file.open(instruction_variant_theory_filename.str());

		//Create and open the IOPairs file for the instruction variant
		std::stringstream instruction_variant_iopairs_filename;		
		if(e.second.second.size()==0) instruction_variant_iopairs_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_nullary" << "_IOPairs" << template_prefix_arg.value() << ".thy";
		if(e.second.second.size()==1) instruction_variant_iopairs_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_IOPairs" << template_prefix_arg.value() << ".thy";
		if(e.second.second.size()==2) instruction_variant_iopairs_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_IOPairs" << template_prefix_arg.value() << ".thy";
		ofstream instruction_variant_iopairs_file;		
		instruction_variant_iopairs_file.open(instruction_variant_iopairs_filename.str());
		
		//find the appropriate template and build it up
		switch( get_template(e))
		{
			case TestTemplate::tt_nullary:
				{
				std::streambuf* raw_buffer; 
				ifstream template_file;
				ifstream template_assembly;
				ifstream template_iopairsfile;
				int i;
//				
				//Build  Assembly File
				//Create and open the Pintool Instrument file for the instruction variant
				std::stringstream instruction_variant_pintool_filename;
				instruction_variant_pintool_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_Pintool_Instrument" << ".s";
				ofstream instruction_variant_pintool_file;		
				instruction_variant_pintool_file.open(instruction_variant_pintool_filename.str());
				template_assembly.open("/root/TestLemmas/Templates/Template_Assembly_nullary.s", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_assembly.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_pintool_file << boost::format(buffer) % s ;
				template_assembly.close();
				instruction_variant_pintool_file.close();
				
				//Build Theory
				template_file.open("/root/TestLemmas/Templates/Template_nullary.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_theory_file << boost::format(buffer) % instr_upper % s  
					% get_lemmas(((s.compare("nop") == 0)? "/root/TestLemmas/Templates/Template_nullary_Lemma_Nop.thy":"/root/TestLemmas/Templates/Template_nullary_Lemma.thy"), lemma_count, lemma_start) 
					% template_prefix_arg.value();
					
				delete buffer;				
				template_file.close();
				
				//add to list of variants for this mnemonic
				list_of_variants << instr_upper << "_nullary" <<  template_prefix_arg.value()
							     << " ";
				add_batch(instruction_variant_build_heap, s, vcount++);				 

				instruction_variant_sessions 
<< "session \"reassembly_" 
<< s <<  template_prefix_arg.value()
<< "\" = \"reassembly_test_setup\" + theories \"../InstructionSemantics/TestLemmas/" 
<< set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_nullary" << template_prefix_arg.value() 
<< "\"" << endl;
				
				//add to gcc makefile for this mnemonic
//				 makefile_variant_lines << "\tgcc " << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument" << ".s -o " << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument" << endl;

				//compile pintool instrument
				std::stringstream s_tmp;
				s_tmp << "cd /root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper << "&& gcc " << instr_upper  << "_Pintool_Instrument" << ".s -o " << instr_upper  << "_Pintool_Instrument";
				int j = std::system(s_tmp.str().c_str());
				j++;
				
				//Build the IO Pairs.
				std::stringstream s_pininstr;
				s_pininstr << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper << "/" << instr_upper << "_Pintool_Instrument";
				template_iopairsfile.open("/root/TestLemmas/Templates/Template_nullary_IOPairs.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_iopairsfile.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_iopairs_file << boost::format(buffer) % instr_upper % 	
					get_iopairs_nullary(lemma_count, lemma_start, s_pininstr.str(),flag_table[s]) 
					% template_prefix_arg.value();
				delete buffer;				
				template_iopairsfile.close();				
			}
				
				break;
			case TestTemplate::tt_r:
				{
				std::streambuf* raw_buffer; 
				ifstream template_file;
				ifstream template_assembly;
				ifstream template_iopairsfile;
				int i;
//				
				//Build  Assembly File
				//Create and open the Pintool Instrument file for the instruction variant
				std::stringstream instruction_variant_pintool_filename;
				instruction_variant_pintool_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" 
					<< fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_Pintool_Instrument" << ".s";
				ofstream instruction_variant_pintool_file;		
				instruction_variant_pintool_file.open(instruction_variant_pintool_filename.str());
				template_assembly.open("/root/TestLemmas/Templates/Template_Assembly_r.s", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_assembly.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_pintool_file << boost::format(buffer) % s % getOperands_r(e.second.second[0]);
				template_assembly.close();
				instruction_variant_pintool_file.close();
				
				//Build Theory
				template_file.open("/root/TestLemmas/Templates/Template_r.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;						
				instruction_variant_theory_file << boost::format(buffer) % instr_upper % s 
					% sizeof_Type_bits(e.second.second[0]) % getRegType(e.second.second[0])  
//					% get_lemmas(((s.compare("nop") == 0)? "/root/TestLemmas/Templates/Template_r_Lemma_Nop.thy":"/root/TestLemmas/Templates/Template_r_Lemma.thy"), lemma_count, lemma_start) 
					% get_lemmas("/root/TestLemmas/Templates/Template_r_Lemma.thy", lemma_count, lemma_start) 
					% template_prefix_arg.value() % fam;
					
				delete buffer;				
				template_file.close();
				
				//add to list of variants for this mnemonic
				list_of_variants << instr_upper << "_r" << sizeof_Type_bits(e.second.second[0]) <<  template_prefix_arg.value()
							     << " ";
				stringstream iv;
				iv << s << "_r" << sizeof_Type_bits(e.second.second[0]);				
				add_batch(instruction_variant_build_heap, iv.str(), vcount++);				 

				instruction_variant_sessions 
<< "session \"reassembly_" 
<< s << "_r" << sizeof_Type_bits(e.second.second[0]) <<  template_prefix_arg.value()
<< "\" = \"reassembly_test_setup\" + theories \"../InstructionSemantics/TestLemmas/" 
<< set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << template_prefix_arg.value() 
<< "\"" << endl;
				
				//add to gcc makefile for this mnemonic
//				 makefile_variant_lines << "\tgcc " << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument" << ".s -o " << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument" << endl;

				//compile pintool instrument
				std::stringstream s_tmp;
				s_tmp << "cd /root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper << "&& gcc " << instr_upper << "_" << e.first[0] << "_Pintool_Instrument" << ".s -o " << instr_upper << "_" << e.first[0] << "_Pintool_Instrument";
				int j = std::system(s_tmp.str().c_str());
				j++;
				
				
				//Build the IO Pairs.
				int p= getOperands_r_type(e.second.second[0]);
				std::stringstream s_pininstr;
				s_pininstr << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper << "/" << instr_upper << "_" << e.first[0] << "_Pintool_Instrument";
				template_iopairsfile.open("/root/TestLemmas/Templates/Template_r_IOPairs.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_iopairsfile.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_iopairs_file << boost::format(buffer) % instr_upper % 	
					sizeof_Type_bits(e.second.second[0]) % 
					get_iopairs_r(lemma_count, lemma_start, p,s_pininstr.str(),flag_table[s],
					false) % template_prefix_arg.value();
				delete buffer;				
				template_iopairsfile.close();				
			}
				
				break;
			case TestTemplate::tt_m:
			{
				std::streambuf* raw_buffer; 
				ifstream template_file;

				template_file.open("/root/TestLemmas/Templates/Template_m.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				int i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				instruction_variant_theory_file << boost::format(buffer) % instr_upper % s % sizeof_Type_bits(e.second.second[0]) % getMemSize(e.second.second[0]) 
							
							% get_lemmas("/root/TestLemmas/Templates/Template_m_Lemma.thy", lemma_count, lemma_start)  % template_prefix_arg.value();
				template_file.close();
				delete buffer;
			
				list_of_variants << instr_upper << "_m" << sizeof_Type_bits(e.second.second[0]) <<  template_prefix_arg.value()
							     << " ";

				stringstream iv;
				iv << s << "_m" << sizeof_Type_bits(e.second.second[0]);				
				add_batch(instruction_variant_build_heap, iv.str(), vcount++);				 
 				
				 instruction_variant_sessions 
						<< "session \"reassembly_" 
						<< s << "_m" << sizeof_Type_bits(e.second.second[0]) <<  template_prefix_arg.value()
						<< "\" = \"reassembly_test_setup\" + theories \"../InstructionSemantics/TestLemmas/" 
						<< set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << template_prefix_arg.value() 
						<< "\"" << endl;
				
				//Build the IO Pairs.
				ifstream template_iopairsfile;
				template_iopairsfile.open("/root/TestLemmas/Templates/Template_m_IOPairs.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_iopairsfile.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_iopairs_file << boost::format(buffer) % instr_upper % 	
					sizeof_Type_bits(e.second.second[0]) %		
					get_iopairs_m(s, e.second.second[0], lemma_count, lemma_start, flag_table[s]) % template_prefix_arg.value();
												
				delete buffer;				
				template_iopairsfile.close();
			}
				break;
				
			case TestTemplate::tt_m_r:				
			{
				std::streambuf* raw_buffer; 
				ifstream template_file;

				template_file.open("/root/TestLemmas/Templates/Template_m_r.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				int i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				instruction_variant_theory_file << boost::format(buffer) % instr_upper % s % sizeof_Type_bits(e.second.second[0]) % getMemSize(e.second.second[0]) 
												% sizeof_Type_bits(e.second.second[1]) % getRegType(e.second.second[1])
												% get_lemmas(((s.compare("cmpxchg") == 0)? "/root/TestLemmas/Templates/Template_m_r_no_rax_Lemma.thy":"/root/TestLemmas/Templates/Template_m_r_Lemma.thy"), lemma_count, lemma_start) 
												% template_prefix_arg.value();
												
				list_of_variants << instr_upper << "_m" << sizeof_Type_bits(e.second.second[0]) << "_r" << sizeof_Type_bits(e.second.second[1]) <<  template_prefix_arg.value()
							     << " ";

				stringstream iv;
				iv << s << "_m" << sizeof_Type_bits(e.second.second[0]) << "_r" << sizeof_Type_bits(e.second.second[1]);				
				add_batch(instruction_variant_build_heap, iv.str(), vcount++);				 
								  				
				instruction_variant_sessions 
<< "session \"reassembly_" 
<< s << "_m" << sizeof_Type_bits(e.second.second[0]) << "_r" << sizeof_Type_bits(e.second.second[1]) <<  template_prefix_arg.value() 
<< "\" = \"reassembly_test_setup\" + theories \"../InstructionSemantics/TestLemmas/" 
<< set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_" << e.first[1] << template_prefix_arg.value() 
<< "\"" << endl;
				template_file.close();
				delete buffer;

				//Build the IO Pairs.
				ifstream template_iopairsfile;
				template_iopairsfile.open("/root/TestLemmas/Templates/Template_m_r_IOPairs.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_iopairsfile.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_iopairs_file << boost::format(buffer) % instr_upper % 	
					sizeof_Type_bits(e.second.second[0]) % sizeof_Type_bits(e.second.second[1]) % 
					get_iopairs_m_r(s, e.second.second[0], e.second.second[1], lemma_count, lemma_start, flag_table[s],
					((s.compare("cmpxchg") == 0)? true:false)) % template_prefix_arg.value();
			
				delete buffer;				
				template_iopairsfile.close();

				
			}
				break;
			case TestTemplate::tt_m_imm:
			{
				std::streambuf* raw_buffer; 
				ifstream template_file;

				template_file.open("/root/TestLemmas/Templates/Template_m_imm.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				int i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				instruction_variant_theory_file << boost::format(buffer) % instr_upper % s % sizeof_Type_bits(e.second.second[0]) % getMemSize(e.second.second[0]) 
							% sizeof_Type_bits(e.second.second[1])
							% get_lemmas("/root/TestLemmas/Templates/Template_m_imm_Lemma.thy", lemma_count, lemma_start)  % template_prefix_arg.value();
				template_file.close();
				delete buffer;
			
				list_of_variants << instr_upper << "_m" << sizeof_Type_bits(e.second.second[0]) << "_imm" << sizeof_Type_bits(e.second.second[1]) <<  template_prefix_arg.value()
							     << " ";
				stringstream iv;
				iv << s << "_m" << sizeof_Type_bits(e.second.second[0]) << "_imm" << sizeof_Type_bits(e.second.second[1]);				
				add_batch(instruction_variant_build_heap, iv.str(), vcount++);				 

				 instruction_variant_sessions 
						<< "session \"reassembly_" 
						<< s << "_m" << sizeof_Type_bits(e.second.second[0]) << "_imm" << sizeof_Type_bits(e.second.second[1]) <<  template_prefix_arg.value()
						<< "\" = \"reassembly_test_setup\" + theories \"../InstructionSemantics/TestLemmas/" 
						<< set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_" << e.first[1] << template_prefix_arg.value() 
						<< "\"" << endl;
				
				//Build the IO Pairs.
				ifstream template_iopairsfile;
				template_iopairsfile.open("/root/TestLemmas/Templates/Template_m_imm_IOPairs.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_iopairsfile.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_iopairs_file << boost::format(buffer) % instr_upper % 	
					sizeof_Type_bits(e.second.second[0]) % sizeof_Type_bits(e.second.second[1]) % 
					
					get_iopairs_m_imm(s, e.second.second[0], e.second.second[1], lemma_count, lemma_start, flag_table[s]) % template_prefix_arg.value();
												
				delete buffer;				
				template_iopairsfile.close();

				
			}
				break;
			case TestTemplate::tt_r_imm:
			{
				std::streambuf* raw_buffer; 
				ifstream template_file;
				
				//Build Theory
				template_file.open("/root/TestLemmas/Templates/Template_r_imm.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				int i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				instruction_variant_theory_file << boost::format(buffer) % instr_upper % s % sizeof_Type_bits(e.second.second[0]) % getRegType(e.second.second[0]) 
							% sizeof_Type_bits(e.second.second[1])
							% get_lemmas("/root/TestLemmas/Templates/Template_r_imm_Lemma.thy", lemma_count, lemma_start) % template_prefix_arg.value();

				list_of_variants << instr_upper << "_r" << sizeof_Type_bits(e.second.second[0]) << "_imm" << sizeof_Type_bits(e.second.second[1]) <<  template_prefix_arg.value()
							     << " ";

				stringstream iv;
				iv << s << "_r" << sizeof_Type_bits(e.second.second[0]) << "_imm" << sizeof_Type_bits(e.second.second[1]);				
				add_batch(instruction_variant_build_heap, iv.str(), vcount++);				 

				instruction_variant_sessions 
<< "session \"reassembly_" 
<< s << "_r" << sizeof_Type_bits(e.second.second[0]) << "_imm" << sizeof_Type_bits(e.second.second[1]) <<  template_prefix_arg.value()
<< "\" = \"reassembly_test_setup\" + theories \"../InstructionSemantics/TestLemmas/" 
<< set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_" << e.first[1] << template_prefix_arg.value() 
<< "\"" << endl;
				template_file.close();
				delete buffer;
				
				//Build the IO Pairs.
				ifstream template_iopairsfile;
				template_iopairsfile.open("/root/TestLemmas/Templates/Template_r_imm_IOPairs.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_iopairsfile.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_iopairs_file << boost::format(buffer) % instr_upper % 	
					sizeof_Type_bits(e.second.second[0]) % sizeof_Type_bits(e.second.second[1]) % 
					get_iopairs_r_imm(s, e.second.second[0], e.second.second[1], lemma_count, lemma_start, flag_table[s]) % template_prefix_arg.value();
				delete buffer;				
				template_iopairsfile.close();
		
				
			}
				break;
			case TestTemplate::tt_r_m:
			{
				std::streambuf* raw_buffer; 
				ifstream template_file;

				template_file.open("/root/TestLemmas/Templates/Template_r_m.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				int i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				instruction_variant_theory_file << boost::format(buffer) % instr_upper % s % sizeof_Type_bits(e.second.second[0]) % getRegType(e.second.second[0])
												% sizeof_Type_bits(e.second.second[1]) % getMemSize(e.second.second[1])
												% get_lemmas(((s.compare("cmpxchg") == 0)? "/root/TestLemmas/Templates/Template_r_m_no_rax_Lemma.thy":"/root/TestLemmas/Templates/Template_r_m_Lemma.thy"), lemma_count, lemma_start) 												
												% template_prefix_arg.value();
										
				list_of_variants << instr_upper << "_r" << sizeof_Type_bits(e.second.second[0]) << "_m" << sizeof_Type_bits(e.second.second[1]) <<  template_prefix_arg.value()
							     << " ";

				stringstream iv;
				iv << s << "_r" << sizeof_Type_bits(e.second.second[0]) << "_m" << sizeof_Type_bits(e.second.second[1]);				
				add_batch(instruction_variant_build_heap, iv.str(), vcount++);				 

				instruction_variant_sessions 
<< "session \"reassembly_" 
<< s << "_r" << sizeof_Type_bits(e.second.second[0]) << "_m" << sizeof_Type_bits(e.second.second[1]) <<  template_prefix_arg.value()
<< "\" = \"reassembly_test_setup\" + theories \"../InstructionSemantics/TestLemmas/" 
<< set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_" << e.first[1] << template_prefix_arg.value() 
<< "\"" << endl;
				template_file.close();
				delete buffer;
								
				//Build the IO Pairs.
				ifstream template_iopairsfile;
				template_iopairsfile.open("/root/TestLemmas/Templates/Template_r_m_IOPairs.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_iopairsfile.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_iopairs_file << boost::format(buffer) % instr_upper % 	
					sizeof_Type_bits(e.second.second[0]) % sizeof_Type_bits(e.second.second[1]) % 
					get_iopairs_r_m(s, e.second.second[0], e.second.second[1], lemma_count, lemma_start, flag_table[s],
					((s.compare("cmpxchg") == 0)? true:false)) % template_prefix_arg.value();
												
				delete buffer;				
				template_iopairsfile.close();
				
			}
				break;				
			case TestTemplate::tt_r_r:
			{
				std::streambuf* raw_buffer; 

				ifstream template_assembly;
				int i;
				//Build  Assembly File
				//Create and open the Pintool Instrument file for the instruction variant
				std::stringstream instruction_variant_pintool_filename;
				instruction_variant_pintool_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument" << ".s";
				ofstream instruction_variant_pintool_file;		
				instruction_variant_pintool_file.open(instruction_variant_pintool_filename.str());
				template_assembly.open("/root/TestLemmas/Templates/Template_Assembly_r_r.s", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_assembly.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_pintool_file << boost::format(buffer) % s % getOperands_r_r(e.second.second[0], e.second.second[1]);
				template_assembly.close();
				instruction_variant_pintool_file.close();
				
				//Build Theory
				ifstream template_file;
				template_file.open("/root/TestLemmas/Templates/Template_r_r.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_theory_file << boost::format(buffer) % instr_upper % s 
					% sizeof_Type_bits(e.second.second[0]) % getRegType(e.second.second[0]) 
					% sizeof_Type_bits(e.second.second[1]) % getRegType(e.second.second[1]) 
					% get_lemmas(((s.compare("cmpxchg") == 0)? "/root/TestLemmas/Templates/Template_r_r_no_rax_Lemma.thy":"/root/TestLemmas/Templates/Template_r_r_Lemma.thy"), lemma_count, lemma_start) 
					% fam
					% template_prefix_arg.value();
					
				delete buffer;				
				template_file.close();
				
				//add to list of variants for this mnemonic
				list_of_variants << instr_upper << "_r" << sizeof_Type_bits(e.second.second[0]) << "_r" << sizeof_Type_bits(e.second.second[1]) <<  template_prefix_arg.value()
							     << " ";

				stringstream iv;
				iv << s << "_r" << sizeof_Type_bits(e.second.second[0]) << "_r" << sizeof_Type_bits(e.second.second[1]);				
				add_batch(instruction_variant_build_heap, iv.str(), vcount++);				 

				instruction_variant_sessions 
<< "session \"reassembly_" 
<< s << "_r" << sizeof_Type_bits(e.second.second[0]) << "_r" << sizeof_Type_bits(e.second.second[1]) <<  template_prefix_arg.value()
<< "\" = \"reassembly_test_setup\" + theories \"../InstructionSemantics/TestLemmas/" 
<< set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_" << e.first[1] << template_prefix_arg.value() 
<< "\"" << endl;
	
				//compile pintool instrument
				std::stringstream s_tmp;
				s_tmp << "cd /root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper << "&& gcc " << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument" << ".s -o " << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument";
				int j = std::system(s_tmp.str().c_str());
				j++;
				
				//Build the IO Pairs.
				ifstream template_iopairsfile;
				int p= getOperands_r_r_type(e.second.second[0], e.second.second[1]);
				std::stringstream s_pininstr;
				s_pininstr << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper << "/" << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument";
				template_iopairsfile.open("/root/TestLemmas/Templates/Template_r_r_IOPairs.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_iopairsfile.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_iopairs_file << boost::format(buffer) % instr_upper % 	
					sizeof_Type_bits(e.second.second[0]) % sizeof_Type_bits(e.second.second[1]) % 
					get_iopairs_r_r(lemma_count, lemma_start, p/10,p%10,s_pininstr.str(),flag_table[s],
					((s.compare("cmpxchg") == 0)? true:false)) % template_prefix_arg.value();
				template_iopairsfile.close();				
				delete buffer;				
				//End IO Piars
				
			}
				break;
			case TestTemplate::tt_simd_simd:
			{
				std::streambuf* raw_buffer; 
				int i;

				
				//Build  Assembly File
				//Create and open the Pintool Instrument file for the instruction variant
				ifstream template_assembly;
				std::stringstream instruction_variant_pintool_filename;
				instruction_variant_pintool_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument" << ".s";
				ofstream instruction_variant_pintool_file;		
				instruction_variant_pintool_file.open(instruction_variant_pintool_filename.str());
				template_assembly.open("/root/TestLemmas/Templates/Template_Assembly_simd_simd.s", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_assembly.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				std::stringstream simd_operands;
				simd_operands << e.first[0] << "1, " << e.first[1] << "2";
				instruction_variant_pintool_file << boost::format(buffer) % s % simd_operands.str();
				instruction_variant_pintool_file.close();
				delete buffer;
				template_assembly.close();
				
				//Build Theory				
				ifstream template_file;
				template_file.open("/root/TestLemmas/Templates/Template_simd_simd.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				instruction_variant_theory_file << boost::format(buffer) % instr_upper % s 
					% get_lemmas("/root/TestLemmas/Templates/Template_simd_simd_Lemma.thy", lemma_count, lemma_start) 
					% e.first[0] % e.first[1] % template_prefix_arg.value();
				delete buffer;
				template_file.close();

				//compile pintool instrument
				std::stringstream s_tmp;
				s_tmp << "cd /root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper << "&& gcc " 
					  << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument" << ".s -o " << instr_upper 
					  << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument";
				int j = std::system(s_tmp.str().c_str());
				j++;
				
				//Build the IO Pairs.
				ifstream template_iopairsfile;
				std::stringstream s_pininstr;
				s_pininstr << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper << "/" 
							<< instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument";
				template_iopairsfile.open("/root/TestLemmas/Templates/Template_simd_simd_IOPairs.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_iopairsfile.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_iopairs_file << boost::format(buffer) % instr_upper % 	
					get_iopairs_simd_simd(lemma_count, lemma_start,s_pininstr.str(),flag_table[s]) 
					% e.first[0] % e.first[1] % template_prefix_arg.value();
				template_iopairsfile.close();				
				delete buffer;				
				//End IO Piars
				
				//Lists
				list_of_variants << instr_upper << "_" << e.first[0] << "_" << e.first[1] <<  template_prefix_arg.value() << " ";
				stringstream iv;
				iv << s << "_" << e.first[0] << "_" << e.first[1];			
				add_batch(instruction_variant_build_heap, iv.str(), vcount++);				 

				instruction_variant_sessions << "session \"reassembly_" << s << "_" << e.first[0] << "_" << e.first[1] <<  template_prefix_arg.value()
					<< "\" = \"reassembly_test_setup\" + theories \"../InstructionSemantics/TestLemmas/" 
					<< set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" 
					<< e.first[0] << "_" << e.first[1] << template_prefix_arg.value() << "\"" << endl;
			}
				break;
			case TestTemplate::tt_simd_m:
			{
				std::streambuf* raw_buffer; 
				ifstream template_file;

				template_file.open("/root/TestLemmas/Templates/Template_simd_m.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				int i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				instruction_variant_theory_file << boost::format(buffer) % instr_upper % s 
												% sizeof_Type_bits(e.second.second[1]) % getMemSize(e.second.second[1])
												% get_lemmas("/root/TestLemmas/Templates/Template_simd_m_Lemma.thy", lemma_count, lemma_start) 
												% e.first[0] % template_prefix_arg.value();
										
				list_of_variants << instr_upper << "_"<< e.first[0] <<"_m" << sizeof_Type_bits(e.second.second[1]) <<  template_prefix_arg.value() << " ";

				stringstream iv;
				iv << s << "_"<< e.first[0] <<"_m" << sizeof_Type_bits(e.second.second[1]);				
				add_batch(instruction_variant_build_heap, iv.str(), vcount++);				 

				instruction_variant_sessions 
<< "session \"reassembly_" 
<< s << "_"<< e.first[0] <<"_m" << sizeof_Type_bits(e.second.second[1]) <<  template_prefix_arg.value() 
<< "\" = \"reassembly_test_setup\" + theories \"../InstructionSemantics/TestLemmas/" 
<< set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_" << e.first[1] << template_prefix_arg.value() 
<< "\"" << endl;
				template_file.close();
				delete buffer;

				//Build the IO Pairs.
				ifstream template_iopairsfile;
				template_iopairsfile.open("/root/TestLemmas/Templates/Template_simd_m_IOPairs.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_iopairsfile.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_iopairs_file << boost::format(buffer) % instr_upper % 	
					sizeof_Type_bits(e.second.second[1]) % 
					get_iopairs_simd_m(s, e.second.second[0], e.second.second[1], lemma_count, lemma_start, flag_table[s]) % e.first[0] % template_prefix_arg.value();
												
				delete buffer;				
				template_iopairsfile.close();
				
				
				
			}
				break;				
			case TestTemplate::tt_m_simd:				
			{
				std::streambuf* raw_buffer; 
				ifstream template_file;

				//Theory Template
				template_file.open("/root/TestLemmas/Templates/Template_m_simd.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				int i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				instruction_variant_theory_file << boost::format(buffer) % instr_upper % s % sizeof_Type_bits(e.second.second[0]) % getMemSize(e.second.second[0]) 
												% get_lemmas("/root/TestLemmas/Templates/Template_m_simd_Lemma.thy", lemma_count, lemma_start) 
												%e.first[1] % template_prefix_arg.value();
				delete buffer;

												
				//Lists								
				list_of_variants << instr_upper << "_m" << sizeof_Type_bits(e.second.second[0]) << "_" << e.first[1] <<  template_prefix_arg.value() <<" ";

				stringstream iv;				
				iv << s << "_m" << sizeof_Type_bits(e.second.second[0]) << "_" << e.first[1] ;				
				add_batch(instruction_variant_build_heap, iv.str(), vcount++);				 
				instruction_variant_sessions 
					<< "session \"reassembly_" << s << "_m" << sizeof_Type_bits(e.second.second[0]) << "_" << e.first[1] <<  template_prefix_arg.value()
					<< "\" = \"reassembly_test_setup\" + theories \"../InstructionSemantics/TestLemmas/" 
					<< set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_" << e.first[1] 
					<< template_prefix_arg.value() << "\"" << endl;
				template_file.close();
				
				
				//Build the IO Pairs.
				ifstream template_iopairsfile;
				template_iopairsfile.open("/root/TestLemmas/Templates/Template_m_simd_IOPairs.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_iopairsfile.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_iopairs_file << boost::format(buffer) % instr_upper % 	
					sizeof_Type_bits(e.second.second[0]) %
					get_iopairs_m_simd(s, e.second.second[0], e.second.second[1], lemma_count, lemma_start, flag_table[s]) 
					% e.first[1] % template_prefix_arg.value();
				delete buffer;				
				template_iopairsfile.close();
				
			}
				break;
			case TestTemplate::tt_simd_r:
			{
				std::streambuf* raw_buffer; 
				int i;

				
				//Build  Assembly File
				//Create and open the Pintool Instrument file for the instruction variant
				ifstream template_assembly;
				std::stringstream instruction_variant_pintool_filename;
				instruction_variant_pintool_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument" << ".s";
				ofstream instruction_variant_pintool_file;		
				instruction_variant_pintool_file.open(instruction_variant_pintool_filename.str());
				template_assembly.open("/root/TestLemmas/Templates/Template_Assembly_simd_r.s", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_assembly.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				string s_op1 = e.first[0] +"1";
				string s_op2; 
				switch (e.second.second[1]){
					case Type::R_32:
						s_op2 = "ecx";
						break;
					default:
					case Type::R_64:
						s_op2 = "rcx";
						break;
				}
				instruction_variant_pintool_file << boost::format(buffer) % s % s_op1 % s_op2;
				instruction_variant_pintool_file.close();
				delete buffer;
				template_assembly.close();
				
				//Build Theory				
				ifstream template_file;
				template_file.open("/root/TestLemmas/Templates/Template_simd_r.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				instruction_variant_theory_file << boost::format(buffer) % instr_upper % s 
					% get_lemmas("/root/TestLemmas/Templates/Template_simd_r_Lemma.thy", lemma_count, lemma_start) 
					% e.first[0] 
					% sizeof_Type_bits(e.second.second[1]) % getRegType(e.second.second[1]) 
					% template_prefix_arg.value();
				delete buffer;
				template_file.close();

				//compile pintool instrument
				std::stringstream s_tmp;
				s_tmp << "cd /root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper << "&& gcc " 
					  << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument" << ".s -o " << instr_upper 
					  << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument";
				int j = std::system(s_tmp.str().c_str());
				j++;
				
				//Build the IO Pairs.
				ifstream template_iopairsfile;
				std::stringstream s_pininstr;
				s_pininstr << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper << "/" 
							<< instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument";
				template_iopairsfile.open("/root/TestLemmas/Templates/Template_simd_r_IOPairs.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_iopairsfile.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_iopairs_file << boost::format(buffer) % instr_upper % 	
					get_iopairs_simd_r(lemma_count, lemma_start,s_pininstr.str(),flag_table[s]) 
					% e.first[0] 
					% sizeof_Type_bits(e.second.second[1])
					% template_prefix_arg.value();
				template_iopairsfile.close();				
				delete buffer;				
				//End IO Piars
				
				//Lists
				list_of_variants << instr_upper << "_" << e.first[0] << "_" << e.first[1] <<  template_prefix_arg.value() << " ";
				stringstream iv;
				iv << s << "_" << e.first[0] << "_" << e.first[1];			
				add_batch(instruction_variant_build_heap, iv.str(), vcount++);				 

				instruction_variant_sessions << "session \"reassembly_" << s << "_" << e.first[0] << "_" << e.first[1] <<  template_prefix_arg.value()
					<< "\" = \"reassembly_test_setup\" + theories \"../InstructionSemantics/TestLemmas/" 
					<< set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" 
					<< e.first[0] << "_" << e.first[1] << template_prefix_arg.value() << "\"" << endl;
			}
				break;
			case TestTemplate::tt_r_simd:
			{
				std::streambuf* raw_buffer; 
				int i;

				//Build  Assembly File
				//Create and open the Pintool Instrument file for the instruction variant
				ifstream template_assembly;
				std::stringstream instruction_variant_pintool_filename;
				instruction_variant_pintool_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument" << ".s";
				ofstream instruction_variant_pintool_file;		
				instruction_variant_pintool_file.open(instruction_variant_pintool_filename.str());
				template_assembly.open("/root/TestLemmas/Templates/Template_Assembly_r_simd.s", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_assembly.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				string s_op1; 
				switch (e.second.second[0]){
					case Type::R_32:
						s_op1 = "ebx";
						break;
					default:
					case Type::R_64:
						s_op1 = "rbx";
						break;
				}
				string s_op2 = e.first[1] +"2";
				instruction_variant_pintool_file << boost::format(buffer) % s % s_op1 % s_op2;
				instruction_variant_pintool_file.close();
				delete buffer;
				template_assembly.close();
				
				//Build Theory				
				ifstream template_file;
				template_file.open("/root/TestLemmas/Templates/Template_r_simd.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				instruction_variant_theory_file << boost::format(buffer) % instr_upper % s 
					% get_lemmas("/root/TestLemmas/Templates/Template_r_simd_Lemma.thy", lemma_count, lemma_start) 
					% sizeof_Type_bits(e.second.second[0]) % getRegType(e.second.second[0]) 
					% e.first[1] 
					% template_prefix_arg.value();
				delete buffer;
				template_file.close();

				//compile pintool instrument
				std::stringstream s_tmp;
				s_tmp << "cd /root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper << "&& gcc " 
					  << instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument" << ".s -o " << instr_upper 
					  << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument";
				int j = std::system(s_tmp.str().c_str());
				j++;
				
				//Build the IO Pairs.
				ifstream template_iopairsfile;
				std::stringstream s_pininstr;
				s_pininstr << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper << "/" 
							<< instr_upper << "_" << e.first[0] << "_" << e.first[1] << "_Pintool_Instrument";
				template_iopairsfile.open("/root/TestLemmas/Templates/Template_r_simd_IOPairs.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_iopairsfile.rdbuf(); 
				i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;								
				instruction_variant_iopairs_file << boost::format(buffer) % instr_upper 
					% get_iopairs_r_simd(lemma_count, lemma_start,s_pininstr.str(),flag_table[s]) 
					% sizeof_Type_bits(e.second.second[0])
					% e.first[1] 
					% template_prefix_arg.value();
				template_iopairsfile.close();				
				delete buffer;				
				//End IO Piars
				
				//Lists
				list_of_variants << instr_upper << "_" << e.first[0] << "_" << e.first[1] <<  template_prefix_arg.value() << " ";
				stringstream iv;
				iv << s << "_" << e.first[0] << "_" << e.first[1];			
				add_batch(instruction_variant_build_heap, iv.str(), vcount++);				 

				instruction_variant_sessions << "session \"reassembly_" << s << "_" << e.first[0] << "_" << e.first[1] <<  template_prefix_arg.value()
					<< "\" = \"reassembly_test_setup\" + theories \"../InstructionSemantics/TestLemmas/" 
					<< set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_" 
					<< e.first[0] << "_" << e.first[1] << template_prefix_arg.value() << "\"" << endl;
			}
				break;
				
				
				
			default:				
				if(e.second.second.size()==1) 
				{
					instruction_variant_theory_file << "theory " << instr_upper << "_" << e.first[0]  <<  template_prefix_arg.value() << " imports Main begin end";
					list_of_variants << "(* " << instr_upper << "_" << e.first[0] << " *)";				
				} else if(e.second.second.size()==2) 
				{
					instruction_variant_theory_file << "theory " << instr_upper << "_" << e.first[0] << "_" << e.first[1] <<  template_prefix_arg.value() << " imports Main begin end";
					list_of_variants << "(* " << instr_upper << "_" << e.first[0] << "_" << e.first[1] << " *)";								
				}				
			break;
		}
		if (variantcount % 5 == 4) list_of_variants << endl;		
		instruction_variant_theory_file.close();
		instruction_variant_iopairs_file.close();
		variantcount++;		

	  }
		if(instr_used == true){	
			list_of_instrs << " \"" << instr_upper << "/" << instr_upper <<  template_prefix_arg.value() << "\" ";
			makefile_instr_lines << "\tmake -C " << instr_upper << "/" << endl;
			
			if (instrcount % 5 == 4) list_of_instrs << endl;		
			instrcount++;	
				  //Create and open the theory file for the instruction variant Setup Theory
			  std::stringstream instruction_setup_filename;
			  instruction_setup_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper << "_Setup" << template_prefix_arg.value() <<".thy";
			  ofstream instr_setup_file;		
			  instr_setup_file.open(instruction_setup_filename.str());

			  {
				std::streambuf* raw_buffer; 
				ifstream template_file;
				template_file.open("/root/TestLemmas/Templates/Template_Setup.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				int i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				instr_setup_file << boost::format(buffer) % instr_upper % s % fam % template_prefix_arg.value();
				template_file.close();
				delete buffer;
			  }		
  			  instr_setup_file.close();
			
				//Create and open the theory file for the Instruction Theory
				std::stringstream instruction_filename;
				instruction_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << instr_upper  << "/" << instr_upper <<  template_prefix_arg.value() << ".thy";
				ofstream instr_file;		
				instr_file.open(instruction_filename.str());

			  {
				std::streambuf* raw_buffer; 
				ifstream template_file;
				template_file.open("/root/TestLemmas/Templates/Template.thy", std::ifstream::binary);
				buffer = new char[20000];
				raw_buffer = template_file.rdbuf(); 
				int i=raw_buffer->sgetn(buffer, 20000);
				buffer[i]=0;
				instr_file << boost::format(buffer) % instr_upper % list_of_variants.str() % template_prefix_arg.value();
				template_file.close();
				delete buffer;
			  }		
				instr_file.close();
				
		}
	}
		if(fam_used == true){	
			list_of_instr_fams << " \"" << fam << "/" << fam <<  template_prefix_arg.value() << "\" " ;
			list_of_instr_fams_makefile << "\tmake -C " << fam << "/" << endl;

			if (famcount % 3 == 2) list_of_instr_fams << endl;		
			famcount++;	

			//Create and open the theory file for the Instruction Theory
			std::stringstream instrfam_filename;
			instrfam_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << fam << "/" << fam <<  template_prefix_arg.value() << ".thy";
			ofstream instrfam_file;		
			instrfam_file.open(instrfam_filename.str());

		  {
			std::streambuf* raw_buffer; 
			ifstream template_file;
			template_file.open("/root/TestLemmas/Templates/Template.thy", std::ifstream::binary);
			buffer = new char[20000];
			raw_buffer = template_file.rdbuf(); 
			int i=raw_buffer->sgetn(buffer, 20000);
			buffer[i]=0;
			instrfam_file << boost::format(buffer) % fam % list_of_instrs.str() % template_prefix_arg.value();
			template_file.close();
			delete buffer;
		  }		
			instrfam_file.close();
			
		}
	
  }

	//Create and open the theory file for the Instruction Theory
	std::stringstream tl_filename;
	tl_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << "TestLemmas" <<  template_prefix_arg.value() <<".thy";
	ofstream tl_file;		
	tl_file.open(tl_filename.str());

  {
	std::streambuf* raw_buffer; 
	ifstream template_file;
	template_file.open("/root/TestLemmas/Templates/Template.thy", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int i=raw_buffer->sgetn(buffer, 20000);
	buffer[i]=0;
	tl_file << boost::format(buffer) % "TestLemmas" % list_of_instr_fams.str() % template_prefix_arg.value();
	template_file.close();
	delete buffer;
  }		
	tl_file.close();


	
	std::stringstream root_filename;
	root_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << "ROOT";
	ofstream root_file;		
	root_file.open(root_filename.str());	
  {
	std::streambuf* raw_buffer; 
	ifstream template_file;
	template_file.open("/root/TestLemmas/Templates/Template_Isabelle_ROOT", std::ifstream::binary);
	buffer = new char[20000];
	raw_buffer = template_file.rdbuf(); 
	int i=raw_buffer->sgetn(buffer, 20000);
	buffer[i]=0;
	root_file << boost::format(buffer) % instruction_variant_sessions.str();
	template_file.close();
	delete buffer;
  }		
	root_file.close();	
	

	std::stringstream build_heaps_filename;
	build_heaps_filename << "/root/TestLemmas/Output/" << set_filename.str() << "/" << "build_heaps.sh";
	ofstream build_heaps_file;		
	build_heaps_file.open(build_heaps_filename.str());	
	build_heaps_file << "#!/bin/sh" << endl;
	build_heaps_file << instruction_variant_build_heap.str();
	build_heaps_file.close();	

  inFile.close();
  return 0;
}
