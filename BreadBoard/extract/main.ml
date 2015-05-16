open Test;;
open Coq_c8051;;
let a = Coq_c8051.computeit (Big.zero);;

  print_string "hello";;

  let fn () =
	match a with
	| Some i -> print_int (Big.to_int i);
	|None -> print_string "nada\n";;
									 fn ();;

	
