open Extracted;;
open Coq_i8051_Component;;
open Core.Std;;
open List;;
let r file = In_channel.input_all file;;


let read filename = In_channel.with_file filename ~f:r;;

  
let explode s =
  let rec exp i l =
	if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

(* let program = *)
(*   let l = (read Sys.argv.(1) ) in *)
(*   let p = List.map l  explode in *)
(*   p;; *)

(* let rec print_char_list p = *)
(*   match p with *)
(*   | x :: r -> *)
(* 	 print_char x; *)
(* 	 print_char_list r; *)
(*   | [] -> print_char '\n';; *)
(* let rec print_load_list p = *)
(*   match p with *)
(*   | (x,y) :: r -> *)
(* 	 print_string "("; *)
(* 	 print_int (Big.to_int x); *)
(* 	 print_string ","; *)
(* 	 print_int (Big.to_int y); *)
(* 	 print_string ")\n"; *)
(* 	 print_load_list r; *)
(*   | [] -> print_char '\n';; *)

(* let load_inst = List.map program (fun x -> ihx_to_byte_assoc_line x None (Some []));; *)


(* List.iter program  print_char_list ;; *)

(* List.map load_inst (fun f -> match f with *)
(* | Some insts -> print_load_list insts; *)
(* | None -> ()) ;; *)

let to_Big x =
  let rec f a b =
  match a with
  | 0 -> b
  | a' -> f (a-1) (Big.succ b) in
  f x Big.zero;;
			

  let () =
	let program =  List.map (explode (read Sys.argv.(1) )) conv_char in
	match hd program with
	| Some i ->
	   print_int (int_of_string Sys.argv.(2));
	   print_string "\nGot a program!\n";
	   print_int (Big.to_int i);
	   print_string " <- Byte from program\n";
	   let v = (computeitBinString (to_Big (int_of_string Sys.argv.(2))) program) in
	   print_string "done\n";
	   match v with
	   | Some i ->
		  print_string "Got: ";
		  print_int  (Big.to_int i);
		  print_string "\n";
		  ()
	   | None ->
		  print_string"No Result\n";
		  ()
  | None -> print_string "No Program?\n";;
