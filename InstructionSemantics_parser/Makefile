NAME := InstructionSemantics

all:
	rm -f $(NAME).grm.sig
	rm -f $(NAME).grm.sml
	rm -f $(NAME).lex.sml
	rm -f $(NAME).grm.desc
	mlyacc $(NAME).grm
	mllex $(NAME).lex
	sed -i.bak 's/^structure YYPosInt : INTEGER = Int/structure YYPosInt = Int/g' $(NAME).lex.sml
	sed -i.bak 's/let val yytext=yymktext()/let val yytext=yymktext() val yyleng=(i-i0-2)/g' $(NAME).lex.sml

