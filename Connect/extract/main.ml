open Test;;
open Coq_c8051;;
  
let explode s =
  let rec exp i l =
	if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;
let program =
  explode (
":03000000020006F5
:03005F0002000399
:0300030002006296
:07006200C300D3020062227B
:06003500E478FFF6D8FD9F
:200013007900E94400601B7A0090006D780075A000E493F2A308B8000205A0D9F4DAF27527
:02003300A0FF2C
:20003B007800E84400600A790075A000E4F309D8FC7800E84400600C7900900000E4F0A3C5
:04005B00D8FCD9FAFA
:0D000600758107120069E5826003020003A6
:04006900758200227A
:00000001FF" );;
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
	let v = (Coq_c8051.computeitString (Big.succ (Big.succ (Big.zero))) program) in
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
