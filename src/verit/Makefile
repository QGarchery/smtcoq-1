
all :
	ocamllex veritLexer.mll       
	menhir --explain veritParser.mly 
	ocamlc -c veritParser.mli
	ocamlc -c veritLexer.ml

.PHONY: all
