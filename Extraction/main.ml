
(**
    VerifiedDSP
    Copyright (C) {2015}  {Jeremy L Rubin}

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License along
    with this program; if not, write to the Free Software Foundation, Inc.,
    51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.

**)
open Extracted;;
open Printf;;
open Coq_i8051_Component;;
open Core.Std;;
open List;;
let r file = In_channel.input_all file;;


let read filename = In_channel.with_file filename ~f:r;;

  
let explode s =
  let rec exp i l =
	if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;


let to_Big x =
  let rec f a b =
  match a with
  | 0 -> b
  | a' -> f (a-1) (Big.succ b) in
  f x Big.zero;;
		
let  pl (x : (int8 * int8 list) list) =
  print_string "[";
  let rec outer = function
	| (a, b)::x' ->
	   Printf.printf "(%i,[" (Big.to_int a);
	   let rec inner = function
		 | n::n' ->
			Printf.printf "%i," (Big.to_int n);
			inner n'
		 | [] -> print_string "]),\n"
	   in
	   inner b;
	   outer x'
	| [] -> print_string "]\n" in
  outer x
  
  let () =
	let program =  List.map (explode (read Sys.argv.(1) )) conv_char in
	match hd program with
	| Some i ->
	   let fuel = (int_of_string Sys.argv.(2)) in
	   print_string "\nGot a program!\n";
	   print_int (Big.to_int i);
	   print_string " <- Byte from program\n";
	   let d = BB.demo3  program (to_Big 6) in
	   pl (IORUN.run d (to_Big fuel))
  | None -> print_string "No Program?\n";;
