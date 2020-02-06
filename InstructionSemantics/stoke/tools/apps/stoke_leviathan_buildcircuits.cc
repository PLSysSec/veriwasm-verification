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
#include "src/validator/handlers/combo_handler.h"
#include "src/validator/handlers/strata_handler.h"
#include "src/specgen/specgen.h"
#include "src/specgen/support.h"

#include "src/leviathan/leviathan_table.h"
#include "src/symstate/leviathan_visitor.h"

#include "tools/gadgets/functions.h"
#include "tools/gadgets/solver.h"
#include "tools/gadgets/target.h"
#include "tools/gadgets/validator.h"

using namespace cpputil;
using namespace std;
using namespace stoke;
using namespace x64asm; 

typedef std::pair<x64asm::Opcode, std::vector<x64asm::Type>> EntryExternal;
typedef std::pair<vector<std::string>, EntryExternal> Entry;

typedef std::vector<Entry> Row;
typedef std::vector<std::string> IntelNmenonics;
typedef std::map<std::string, Row> Table;

extern Table leviathan_table;

cpputil::ValueArg<std::string>& strata_path_arg =
  cpputil::ValueArg<std::string>::create("strata_path")
  .usage("<path/to/dir>")
  .description("The path to the directory with the strata circuits (a collection of .s files)")
  .default_val("");

auto& support_only_arg = FlagArg::create("support_only").description("Only Show Supported / Unsupported");
auto& skip_empties_arg = FlagArg::create("skip_empties").description("Skip unsupported Ops");
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

int sizeof_Type(Type t)
{
	switch (t)
	{
		case Type::IMM_8:
		case Type::R_8:
		case Type::M_8:
			return 8;
			break;
		case Type::IMM_16:
		case Type::R_16:
		case Type::M_16:
			return 16;
		  break;
		case Type::IMM_32:
		case Type::R_32:
		case Type::M_32:
			return 32;
		  break;
		case Type::IMM_64:
		case Type::R_64:
		case Type::M_64:
			return 64;
		  break;
		case Type::XMM:
		case Type::M_128:
			return 128;
			break;
		case Type::YMM:
		case Type::M_256:
			return 256;
			break;
		default:
			return 0;
			break;
	}
	return 0;
}

enum OperandType { r, imm, m, ymm, xmm};
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
			return OperandType::xmm;
		case Type::YMM:
			return OperandType::ymm;
			
		default:
			break;
	}
	return OperandType::imm;
}

//Only for binary instructions acting on second operand
int generalize_extend( Type end,Type start)
{
	int e = 0;
	
	e = sizeof_Type(end);
	return e;
}
	
int main(int argc, char** argv) {
  target_arg.required(false);
  ofstream ruleset;		
  ofstream support;		
  ofstream instr_ruleset;		
  
  CommandLineConfig::strict_with_convenience(argc,argv);
  StrataHandler sh(strata_path_arg.value());
  ComboHandler oh(strata_path_arg.value());
  DebugHandler::install_sigsegv();
  DebugHandler::install_sigill();

  std::stringstream ruleset_filename;
  ruleset_filename << "/root/Rules/strata_rules";
  ruleset.open(ruleset_filename.str());

  std::stringstream support_filename;
  support_filename << "/root/Rules/strata_rules_support";
  support.open(support_filename.str());
	
  for (auto it=leviathan_table.begin(); it!=leviathan_table.end();++it) { //for each instrucftion nemonic
	string s = it->first;
	
	std::stringstream instr_ruleset_filename;
	instr_ruleset_filename << "/root/Rules/strata_rules_" << s;
	instr_ruleset.open(instr_ruleset_filename.str());
	
	
    for (Entry e : it->second) {  //For each Instruction Variant of a given nmenonic
		int ge=0; //generalization to immediates (this will hold how big to sign-extend)
		int gs=0; //genrealization to memory (
		int vz=0; //don't symbolize operands for vzeroall as it directly writes to a bunch
		int oo=0; //symbolize non-standard registers when dealing with instructions that are optimied for specific registers, IE: eax
		
		Opcode o = e.second.first;
		Instruction it_old(NOP);
		Instruction it(NOP);
		it_old.set_opcode(o);
		it.set_opcode(o);
		
		if(e.second.first==VZEROALL) vz=1; //Symbolization is slightly different as it directly write to all xmms	
		if(e.second.first==MOVSD_XMM_M64) continue; //Skip this for now. Generalization argument doesn't hold 	
		if(e.second.first==MOVSS_XMM_M32) continue; //Skip this for now. Generalization argument doesn't hold 	

		switch (sh.support_reason(e.second.first)){
		case SupportReason::GENERALIZE_SAME:
			o = sh.support_opcode(e.second.first);
			it.set_opcode(o);
			if(get_operandtype(e.second.second[0])==m) gs=1; //as part of generalization condition from M to R or XMM case chop off extra bits. 
			break;
		case SupportReason::GENERALIZE_EXTEND:
			o = sh.support_opcode(e.second.first);
			it.set_opcode(o);
			ge=generalize_extend(it.type(1),it_old.type(1));
			break;
		case SupportReason::GENERALIZE_SHRINK:
			if(get_operandtype(e.second.second[0])==m) gs=1; //as part of generalization condition from M to R or XMM case chop off extra bits. 
			o = sh.support_opcode(e.second.first);
			it.set_opcode(o);
			break;
		default:
				if(e.second.first==MOV_R64_IMM64) {
							it.set_opcode(MOV_R64_R64);
				} //do generalization by hand. strata says support but doesn't generalize to support case as it's in base set 	

			break;
		} 

		SymState state("",true);
		bool abort = false;
		for (size_t i = 0, ie = it.arity(); i < ie; ++i) {
			switch (it.type(i)) {		
				case Type::ZERO:
				  it.set_operand(i, zero);
				  break;
				case Type::ONE:
				  it.set_operand(i, one);
				  break;
				case Type::THREE:
				  it.set_operand(i, three);
				  break;
				case Type::RH:
					if ( i==0) it.set_operand(i, rhs[3]); // BH
					else it.set_operand(i, rhs[1]); //CH
				  break;
				case Type::R_8:
				  it.set_operand(i, r8s[i+8]);
				  break;
				case Type::R_16:
				  it.set_operand(i, r16s[i+8]);
				  break;
				case Type::R_32:
				  it.set_operand(i, r32s[i+8]);
				  break;
				case Type::R_64:
				  it.set_operand(i, r64s[i+8]);
				  break;
				case Type::RAX:
				  it.set_operand(i, rax);
				  oo=i+1;
				  break;
				case Type::EAX:
				  it.set_operand(i, eax);
				  oo=i+1;
				  break;
				case Type::AX:
				  it.set_operand(i, ax);
				  oo=i+1;
				  break;
				case Type::XMM:
				  it.set_operand(i, xmms[i+8]);
				  break;
				case Type::YMM:
				  it.set_operand(i, ymms[i+8]);
				  break;
				case Type::XMM_0:
				  it.set_operand(i, xmm0);
				  break;
				case Type::CL:
				  it.set_operand(i, cl);
				  break;
//				case Type::M_8:
//				case Type::M_16:
//				  it.set_operand(i, m);
//				  break;
				  
				default:
				  abort=true;
				  break;
			}
		}
		
		
		//unsupported by Strata and not in base set
		if (sh.support_reason(e.second.first) == SupportReason::NONE)
		{
			if (!specgen_is_base(e.second.first)) {
				continue;
			}
			else
			{
/*				ruleset << "(" << s; 
				for (size_t i = 0, ie = it.arity(); i < ie; ++i) {
					if ( i > 0) ruleset << ",";
					ruleset << " ";
					ruleset << e.first[i];
				}
				ruleset << ") -> (Is in base so we are keeping it)" << endl;
*/			}
			
		}

		//Unsupported by handler.. Should be nothing unless strata is taken out of combo handler.
		Handler::SupportLevel hsl;
		Handler* hh = NULL;
		hh=oh.get_handler(it,hsl);
		if (hh==NULL) abort=true;
		
		if (abort==true) {
			cout << "HERE!!!  ";
			ruleset << "(" << s; 
			for (size_t i = 0, ie = it.arity(); i < ie; ++i) {
				if ( i > 0) ruleset << ",";
				ruleset << " ";
				ruleset << e.first[i];
			}
			ruleset << ") -> Aborted by lack of param gen or handler." << endl;
			continue; //Abort if we don't handle that type  of operand
		}
					
			std::pair<std::string, Entry> sp = find_entry_by_opcode(o);
			support << "(" << s; 
			for (size_t i = 0, ie = it.arity(); i < ie; ++i) {
				if ( i > 0) support << ",";
				support << " ";
				support << e.first[i];
			}
			support << ") -> ";

			switch (sh.support_reason(e.second.first))
			{
				case SupportReason::LEARNED:
					support << "(Supported::LEARNED) by way of <- [";
					break;

				case SupportReason::GENERALIZE_SAME:
					support << "(Supported::GENERALIZE_SAME) by way of <- [";
					break;
				case SupportReason::GENERALIZE_SHRINK:
					support << "(Supported::GENERALIZE_SHRINK) by way of <- [";
					break;
				case SupportReason::GENERALIZE_EXTEND:
					support << "(Supported::GENERALIZE_EXTEND) by way of <- [";
					break;
				default:
					support << "(Supported::DEFAULT) by way of <- [";
					break;
			} 
			support  << sp.first ;
			for (size_t i = 0, ie = it.arity(); i < ie; ++i) {
				if ( i > 0) support << ",";
				support << " ";
				support << sp.second.first[i];
			}
			support << "]" ;
			support << " <- Using Handler: [";
			support << hh->handler_name() << "] "; 

			support << " Write/Read Set: [";
			support << it.maybe_write_set() << "], [" << it.maybe_read_set() << "]" << endl; 
						
		
		//build formula for instruction using strata handler
		state.set_lineno(0);
		oh.build_circuit(it, state);
		
		//Sets up the Leviathan formula symbolic serialization 
		SymLeviathanVisitor pretty(instr_ruleset,ge);
		SymLeviathanVisitor pretty2(ruleset,ge);
		SymPrintVisitor smtlib(instr_ruleset);
		auto print = [&smtlib, &pretty, &pretty2](const auto c) {  
				SymSimplify s;
				pretty(s.simplify(c));
				pretty2(s.simplify(c));
		};
		
		// print symbolic state
		instr_ruleset << "(" << s; 
		ruleset << "(" << s; 
		for (size_t i = 0, ie = it.arity(); i < ie; ++i) {
			if ( i > 0) { instr_ruleset << ","; ruleset << ","; }
			instr_ruleset << " ";
			instr_ruleset << e.first[i];
			ruleset << " ";
			ruleset << e.first[i];
		}
		instr_ruleset << ") -> (";
		ruleset << ") -> (";

		
		bool printed = false;
		RegSet rs = (RegSet::all_gps() | RegSet::all_ymms()) 
				+
				  Constants::eflags_sf() +
				  Constants::eflags_zf() +
				  Constants::eflags_of() + 
				  Constants::eflags_cf() +
				  Constants::eflags_pf();
	  
		for (auto gp_it = rs.gp_begin(); gp_it != rs.gp_end(); ++gp_it) { //For each general purpose register
			auto val = state.lookup(*gp_it);
			stringstream ss;
			ss << (*gp_it);
			string string_reg= ss.str();

			
			if (!has_changed(gp_it, val)) continue;
				if (printed) { ruleset << " ; "; instr_ruleset << " ; "; printed=false;}

			//This is either a parameter or a hard specified register (IE: MUL sometimes directly modified AX and DX)
			if (string_reg.compare("%r8") == 0 || 
				string_reg.compare("%rbx") == 0 ||
				(string_reg.compare("%rax") == 0 && oo==1))
				{
					instr_ruleset << "OP1" << " = ";
					ruleset << "OP1" << " = ";
				}
			else if (string_reg.compare("%r9") == 0 || 
				string_reg.compare("%rcx") == 0 ||
				(string_reg.compare("%rax") == 0 && oo==2))
				{
					instr_ruleset << "OP2" << " = ";
					ruleset << "OP2" << " = ";
				}
			else if (string_reg.compare("%r10") == 0)
				{
					instr_ruleset << "OP3" << " = ";
					ruleset << "OP3" << " = ";
				}
			else { 
				auto sreg = string_reg.substr(1);
				std::for_each(sreg.begin() , sreg.end(), [](char & c) { c = ::toupper(c);});
				instr_ruleset << sreg << " = ";
				ruleset << sreg << " = ";
			}
			if( gs==1)
			{	
				instr_ruleset << "("; 
				ruleset << "("; 
				print(val); 
				instr_ruleset << ")[" << std::to_string(sizeof_Type(e.second.second[0])-1) << ":0]";  
				ruleset << ")[" << std::to_string(sizeof_Type(e.second.second[0])-1) << ":0]"; 
			} else  {
				print(val);
			}
			printed = true;
		}
		for (auto sse_it = rs.sse_begin(); sse_it != rs.sse_end(); ++sse_it) {
			auto val = state.lookup(*sse_it);
			stringstream ss;
			ss << (*sse_it);
			string string_reg= ss.str();
			string operand_prefix = "";

			if (!has_changed(sse_it, val)) continue;
				if (printed) { ruleset << " ; "; instr_ruleset << " ; "; printed=false;}

			if (string_reg.compare("%ymm8") == 0 && vz==0)
				operand_prefix = "OP1";		
			else if (string_reg.compare("%ymm9") == 0 && vz==0)
				operand_prefix = "OP2"; 			
			else if (string_reg.compare("%ymm10") == 0&& vz==0)
				operand_prefix = "OP3"; 
			else { 
				auto sreg = string_reg.substr(1);
				std::for_each(sreg.begin() , sreg.end(), [](char & c) { c = ::toupper(c);});
				operand_prefix = sreg ;
			}
			
			if( gs==1)
			{	
				instr_ruleset 	<< operand_prefix << " = ("; 
				ruleset 	<< operand_prefix << " = ("; 
				print(val); 
				instr_ruleset << ")[" << (sizeof_Type(e.second.second[0])-1) << ":0]"; 
				ruleset << ")[" << (sizeof_Type(e.second.second[0])-1) << ":0]"; 
			} else {
				instr_ruleset 	<< operand_prefix << " = ";   
				ruleset 	    << operand_prefix << " = "; 
				print(val);  
			
			}
			
			printed = true;
		}
//		if ( enable_flags_arg) {
			for (auto flag_it = rs.flags_begin(); flag_it != rs.flags_end(); ++flag_it) {

				SymBool val = state[*flag_it];

				stringstream ss;
				ss << (*flag_it);
				string string_flag= ss.str();

				if (!has_changed(flag_it, val)) continue;
				if (val.type()==SymBool::Type::VAR) { continue;} // If a flag comes back as a variable it means undefined behavior. In our case that means we are just not going to modify it.
				
				if (printed) { ruleset << " ; "; instr_ruleset << " ; "; printed=false;}
				
				auto sflag = string_flag.substr(1);
				std::for_each(sflag.begin() , sflag.end(), [](char & c) { c = ::toupper(c);});
				ruleset << sflag << " := ";
				instr_ruleset << sflag << " := ";
				print(val);
				printed = true;
			}
//		}
		if(s.compare("blsr")==0 || s.compare("blsmsk")==0) 
		{
			if (printed) { ruleset << " ; "; instr_ruleset << " ; "; printed=false;}
				ruleset << "PF := undefined";
				instr_ruleset << "PF := undefined";
			printed=true;	
		}
		if (printed==false) instr_ruleset << "None" ;
		ruleset << ")" << endl; instr_ruleset << ")" << endl;
	}
	
	instr_ruleset.close();	
  } 
  ruleset.close();
  support.close();

  return 0;
}
