all: mlton

mlton: util.sml ast.sml parse.sml tchck.sml top.sml wrap.sml repl.mlb
	mlton -output repl -link-opt -lreadline repl.mlb $(SMACKAGE)/lib/readline/v1/sml-readline.c

