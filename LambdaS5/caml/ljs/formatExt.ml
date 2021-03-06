open Batteries
open Format

type printer = formatter -> unit
 
let nest (p : printer) (fmt : formatter) : unit =
  pp_open_vbox fmt 2;
  p fmt;
  pp_close_box fmt ()

let text s fmt = pp_print_string fmt s
 
let rec inter (sep : printer) (lst : printer list) (fmt : formatter) : unit = match lst with
    x1 :: x2 :: xs' ->
      pp_open_box fmt 2;
      x1 fmt; 
      pp_close_box fmt ();
      sep fmt;
      inter sep (x2 :: xs') fmt
  | [x] -> 
      pp_open_box fmt 2;
      x fmt;
      pp_close_box fmt ()
  | [] -> ()

let sep (lst : printer list) (fmt : formatter) : unit = inter (fun fmt -> pp_print_space fmt ()) lst fmt

let rec squish (lst : printer list) (fmt : formatter) : unit = match lst with
  | x :: xs -> x fmt; squish xs fmt
  | [] -> ()
 
 
let vert (p : printer list) (fmt : formatter) : unit = 
  pp_open_vbox fmt 0;
  sep p fmt;
  pp_close_box fmt ()
 
let horz (p : printer list) (fmt : formatter) : unit = 
  pp_open_hbox fmt ();
  sep p fmt;
  pp_close_box fmt ()
  
let horzOrVert (p : printer list) (fmt : formatter) : unit =
  pp_open_hvbox fmt 0;
  sep p fmt;
  pp_close_box fmt ()

let wrapBox (p : printer list) (fmt : formatter) : unit =
  pp_open_hovbox fmt 0;
  sep p fmt;
  pp_close_box fmt ()

let int n fmt = pp_print_int fmt n
 
let float f fmt = pp_print_float fmt f

let bool f fmt = pp_print_bool fmt f
 
let enclose l r (inner : printer) (fmt : formatter) = 
  pp_open_box fmt 2;
  pp_print_string fmt l;
  inner fmt;
  pp_print_string fmt r;
  pp_close_box fmt ()
 
let parens = enclose "(" ")"
 
let braces = enclose "{" "}"
 
let brackets = enclose "[" "]"

let angles = enclose "<" ">"

let rec intersperse el list =
  match list with
  | [] | [ _ ]   -> list
  | x :: y :: tl -> x :: el :: intersperse el (y::tl)

let rec vert_intersperse a lst = match lst with
  | [] -> []
  | [x] -> [x]
  | x :: xs -> squish [x; a] :: (vert_intersperse a xs)

let to_string (f : 'a -> printer) (x : 'a) : string  =
  f x str_formatter;
  flush_str_formatter ()

let to_output o f x =
  f x (formatter_of_output o)

