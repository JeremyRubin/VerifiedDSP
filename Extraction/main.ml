open Extracted;;
open Coq_i8051_Component;;
open Core.Std;;
let r file = In_channel.read_all file;;

  
let explode s =
  let rec exp i l =
	if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

let program = explode (r Sys.argv.(1));;
let rec print_char_list p =
  match p with
  | x :: r ->
	 print_char x;
	 print_char_list r;
  | [] -> print_char '\n';;
let rec print_load_list p =
  match p with
  | (x,y) :: r ->
	 print_string "(";
	 print_int (Big.to_int x);
	 print_string ",";
	 print_int (Big.to_int y);
	 print_string ")\n";
	 print_load_list r;
  | [] -> print_char '\n';;

let load_inst = ihx_to_byte_assoc_line (asciis program) None (Some []);;

print_string "Loading Program:\n";;
print_char_list program;;
match load_inst with
| Some insts -> print_load_list insts;
| None -> ();;


  let main () =
	let v = (computeitString (Big.succ (Big.succ (Big.zero))) program) in
	print_string "done\n";
	match v with
	| Some i ->
	   print_string "Got: ";
	   print_int  (Big.to_int i);
	   print_string "\n";
	   ()
	| None ->
	   print_string"No Result\n";
	   ();;
main ();;
